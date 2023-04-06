use std::{
    iter::repeat,
    io::{Read, Write, BufReader, BufWriter, BufRead, Seek},
    fs::{File, metadata},
    path::Path,
    time::Instant,
    env,
};

use std::{
    cell::RefCell,
    rc::Rc,
};
    

const MEM: usize = 1 << 23;

// Indicates an empty or non-empty buffer. 
#[derive(PartialEq, Eq)]
pub enum BufferState {
    NotEmpty,
    Empty,
}

/// A trait for handling buffered reading.
pub trait BufferedRead {
    fn read_byte(&mut self) -> u8;
    fn read_u64(&mut self) -> u64;
    fn fill_buffer(&mut self) -> BufferState;
}
impl BufferedRead for BufReader<File> {
    /// Read one byte from an input file.
    fn read_byte(&mut self) -> u8 {
        let mut byte = [0u8; 1];

        if self.read(&mut byte).is_ok() {
            if self.buffer().is_empty() {
                self.consume(self.capacity());

                if let Err(e) = self.fill_buf() {
                    println!("Function read_byte failed.");
                    println!("Error: {}", e);
                }
            }
        }
        else {
            println!("Function read_byte failed.");
        }
        u8::from_le_bytes(byte)
    }
    /// Read 8 bytes from an input file, taking care 
    /// to handle reading across buffer boundaries.
    fn read_u64(&mut self) -> u64 {
        let mut bytes = [0u8; 8];

        if let Ok(len) = self.read(&mut bytes) {
            if self.buffer().is_empty() {
                self.consume(self.capacity());
                
                if let Err(e) = self.fill_buf() {
                    println!("Function read_u64 failed.");
                    println!("Error: {}", e);
                }
                if len < 8 {
                    self.read_exact(&mut bytes[len..]).unwrap();
                }
            }
        }
        else {
            println!("Function read_u64 failed.");
        }
        u64::from_le_bytes(bytes)
    }

    /// Fills the input buffer, returning the buffer's state.
    fn fill_buffer(&mut self) -> BufferState {
        self.consume(self.capacity());
        if let Err(e) = self.fill_buf() {
            println!("Function fill_buffer failed.");
            println!("Error: {}", e);
        }
        if self.buffer().is_empty() {
            return BufferState::Empty;
        }
        BufferState::NotEmpty
    }
}

/// A trait for handling buffered writing.
pub trait BufferedWrite {
    fn write_byte(&mut self, output: u8);
    fn write_u64(&mut self, output: u64);
    fn flush_buffer(&mut self);
}
impl BufferedWrite for BufWriter<File> {
    /// Write one byte to an output file.
    fn write_byte(&mut self, output: u8) {
        if let Err(e) = self.write(&[output]) {
            println!("Function write_byte failed.");
            println!("Error: {}", e);
        }
        
        if self.buffer().len() >= self.capacity() {
            if let Err(e) = self.flush() {
                println!("Function write_byte failed.");
                println!("Error: {}", e);
            }
        }
    }
    /// Write 8 bytes to an output file.
    fn write_u64(&mut self, output: u64) {
        if let Err(e) = self.write(&output.to_le_bytes()[..]) {
            println!("Function write_u64 failed.");
            println!("Error: {}", e);
        }
        
        if self.buffer().len() >= self.capacity() {
            if let Err(e) = self.flush() {
                println!("Function write_u64 failed.");
                println!("Error: {}", e);
            }
        }
    }

    /// Flush buffer to file.
    fn flush_buffer(&mut self) {
        if let Err(e) = self.flush() {
            println!("Function flush_buffer failed.");
            println!("Error: {}", e);
        }    
    }
}
fn new_input_file(file_name: &str) -> BufReader<File> {
    BufReader::with_capacity(
        1 << 20, File::open(file_name).unwrap()
    )
}
fn new_output_file(file_name: &str) -> BufWriter<File> {
    BufWriter::with_capacity(
        1 << 20, File::create(file_name).unwrap()
    )
}


// Logistic Functions

/// Returns p = 1/(1 + exp(-d)) (Inverse of stretch)
/// d = (-2047..2047), p = (0..4095)
pub fn squash(d: i32) -> i32 {
    const SQ_T: [i32; 33] = [
    1,2,3,6,10,16,27,45,73,120,194,310,488,747,1101,
    1546,2047,2549,2994,3348,3607,3785,3901,3975,4022,
    4050,4068,4079,4085,4089,4092,4093,4094];
    if d > 2047  { return 4095; }
    if d < -2047 { return 0;    }
    let i_w = d & 127;
    let d = ((d >> 7) + 16) as usize;
    (SQ_T[d] * (128 - i_w) + SQ_T[d+1] * i_w + 64) >> 7
}

/// Returns p = ln(d/(1-d)) (Inverse of squash)
/// d = (0..4095), p = (-2047..2047)
pub fn stretch(d: i32) -> i32 {
    assert!(d < 4096);
    STRETCH_TABLE[d as usize] as i32
}


/// An APM takes an existing prediction and a context, and interpolates a 
/// new, refined prediction. Also known as Secondary Symbol Estimation (SSE).
pub struct Apm {
    bin:       usize,    // A value used for interpolating a new prediction
    num_cxts:  usize,    // Number of possible contexts i.e 256 for order-0
    bin_map:   Vec<u16>, // Table mapping values 0..=32 to squashed 16 bit values
}
impl Apm {
    /// Create a new Apm.
    pub fn new(n: usize) -> Apm {
        Apm {
            bin:       0,
            num_cxts:  n,
            bin_map:   repeat( // Map 0..33 to values in closure, create n copies
                       (0..33).map(|i| (squash((i - 16) * 128) * 16) as u16)
                       .collect::<Vec<u16>>().into_iter() )
                       .take(n)
                       .flatten()
                       .collect::<Vec<u16>>(),
        }
    }

    /// Interpolate a new prediction.
    pub fn p(&mut self, bit: i32, rate: i32, mut pr: i32, cxt: u32) -> i32 {
        assert!(bit == 0 || bit == 1 && pr >= 0 && pr < 4096);
        assert!(cxt < self.num_cxts as u32);
        self.update(bit, rate);
        
        pr = stretch(pr);   // -2047 to 2047
        let i_w = pr & 127; // Interpolation weight (33 points)
        
        // Compute set of bins from context, and singular bin from prediction
        self.bin = (((pr + 2048) >> 7) + ((cxt as i32) * 33)) as usize;

        let l = self.bin_map[self.bin] as i32;   // Lower bin
        let u = self.bin_map[self.bin+1] as i32; // Upper bin
        ((l * (128 - i_w)) + (u * i_w)) >> 11 // Interpolate pr from bin and bin+1
    }

    /// Update the two bins last used for interpolation.
    pub fn update(&mut self, bit: i32, rate: i32) {
        assert!(bit == 0 || bit == 1 && rate > 0 && rate < 32);
        
        // Controls direction of update (bit = 1: increase, bit = 0: decrease)
        let g: i32 = (bit << 16) + (bit << rate) - bit - bit;

        // Bins used for interpolating previous prediction
        let l = self.bin_map[self.bin] as i32;   // Lower
        let u = self.bin_map[self.bin+1] as i32; // Upper
        self.bin_map[self.bin]   = (l + ((g - l) >> rate)) as u16;
        self.bin_map[self.bin+1] = (u + ((g - u) >> rate)) as u16;
    }
}


/// A bit history (state) is mapped to a probability using an adaptive table
/// (StateMap). Each table entry has a 22-bit probability (initially p = 0.5) 
/// and 10-bit count (initially n = 0) packed into 32 bits.  After bit y is 
/// predicted, n is incremented up to the limit (1023) and the probability is 
/// adjusted by p := p + (y - p)/(n + 0.5).  This model is stationary: 
/// p = (n1 + 0.5)/(n + 1), where n1 is the number of times y = 1 out of n.

#[allow(overflowing_literals)]
const PR_MSK: i32 = 0xFFFFFC00; // High 22 bit mask
const LIMIT: usize = 127; // Controls rate of adaptation (higher = slower) (0..1024)

/// A Statemap is used in an indirect context model to map a context to a 
/// state (a 1 byte representation of previously encountered bits), which 
/// is then mapped to a prediction. 
#[derive(Clone)]
pub struct StateMap {
    cxt:      usize,    // Context of last prediction
    cxt_map:  Vec<u32>, // Maps a context to a prediction and a count
    rec_t:    Vec<u16>, // Reciprocal table: controls adjustment to cxt_map
}
impl StateMap {
    /// Create a new StateMap.
    pub fn new(n: usize) -> StateMap {
        StateMap {
            cxt:      0,
            cxt_map:  vec![1 << 31; n],
            rec_t:    (0..1024).map(|i| 16_384/(i+i+3)).collect(),
        }
    }

    /// Maps a context, usually a state, to a prediction.
    pub fn p(&mut self, bit: i32, cxt: i32) -> i32 {
        assert!(bit == 0 || bit == 1);
        self.update(bit);
        self.cxt = cxt as usize;
        (self.cxt_map[self.cxt] >> 20) as i32
    }

    /// Update mapping based on prediction error.
    pub fn update(&mut self, bit: i32) {
        let count = (self.cxt_map[self.cxt] & 1023) as usize; // Low 10 bits
        let pr    = (self.cxt_map[self.cxt] >> 10 ) as i32;   // High 22 bits

        if count < LIMIT { self.cxt_map[self.cxt] += 1; }

        // Update cxt_map based on prediction error
        let pr_err = ((bit << 22) - pr) >> 3; // Prediction error
        let rec_v = self.rec_t[count] as i32; // Reciprocal value
        self.cxt_map[self.cxt] = 
        self.cxt_map[self.cxt].wrapping_add(((pr_err * rec_v) & PR_MSK) as u32);
    }
}


/// Predictions are combined using a neural network (Mixer). The inputs p_i, 
/// i=0..6 are first stretched: t_i = log(p_i/(1 - p_i)), then the output is 
/// computed: p = squash(SUM_i t_i * w_i), where squash(x) = 1/(1 + exp(-x)) 
/// is the inverse of stretch().  The weights are adjusted to reduce the 
/// error: w_i := w_i + L * t_i * (y - p) where (y - p) is the prediction 
/// error and L ~ 0.002 is the learning rate. This is a standard single layer 
/// backpropagation network modified to minimize coding cost rather than RMS 
/// prediction error (thus dropping the factors p * (1 - p) from learning).
pub struct Mixer {
    max_in:   usize,    // Maximum number of inputs
    inputs:   Vec<i32>, // Current inputs
    weights:  Vec<i32>, // Weights used for weighted averaging
    wht_set:  usize,    // Single set of weights chosen by a context
    pr:       i32,      // Current prediction
}
impl Mixer {
    /// Create a new Mixer with m sets of n weights.
    pub fn new(n: usize, m: usize) -> Mixer {
        Mixer {
            max_in:   n,                     
            inputs:   Vec::with_capacity(n), 
            weights:  vec![0; n * m],        
            wht_set:  0,                     
            pr:       2048,                  
        }
    }

    /// Add an input prediction to the Mixer.
    pub fn add(&mut self, pr: i32) {
        assert!(self.inputs.len() < self.inputs.capacity());
        self.inputs.push(pr);
    }

    /// Choose the set of weights to be used for averaging.
    pub fn set(&mut self, cxt: u32) {
        self.wht_set = (cxt as usize) * self.max_in; 
    }

    /// Compute weighted average of input predictions.
    pub fn p(&mut self) -> i32 {
        let d = dot_product(&self.inputs[..], &self.weights[self.wht_set..]);
        self.pr = squash(d);
        self.pr
    }

    /// Update weights based on prediction error.
    pub fn update(&mut self, bit: i32) {
        let error: i32 = ((bit << 12) - self.pr) * 7;
        assert!(error >= -32768 && error < 32768);
        train(&self.inputs[..], &mut self.weights[self.wht_set..], error);
        self.inputs.clear();
    }
}

/// Update weights based on prediction error.
fn train(inputs: &[i32], weights: &mut [i32], error: i32) {
    for (input, weight) in inputs.iter().zip(weights.iter_mut()) {
        *weight += ((*input * error) + 0x8000) >> 16;
    }
}

/// Compute dot product.
fn dot_product(inputs: &[i32], weights: &[i32]) -> i32 {
    (inputs.iter().zip(weights.iter())
    .map(|(i, w)| i * w).sum::<i32>()) >> 16
}


/// A match model finds the last occurrence of a high order context and predicts 
/// which symbol came next. The accuracy of the prediction depends on the length 
/// of the context match. The prediction for a match of L bytes (or 8L bits) is 
/// that the next bit will be the same with probability 1 - 1/8L. Typically a 
/// match model of order 6-8 is mixed with lower order context models. A match 
/// model is faster and uses less memory than a corresponding context model but 
/// does not model well for low orders.
///
/// The model looks up the current context in a hash table, first using a longer 
/// context, then a shorter one. If a match is found, then the following bits are 
/// predicted until there is a misprediction. The prediction is computed by mapping 
/// the predicted bit, the match length (1..15 or quantized by 4 in 16..62, max 62),
/// and the last whole byte as context into a StateMap. If no match is found, then 
/// the order 0 context (last 0..7 bits of the current byte) is used as context to 
/// the StateMap.
/// 
/// One third of memory is used by MatchModel, divided equally between a rotating 
/// input buffer of 2^(N+19) bytes and an index (hash table) with 2^(N+17) entries. 
/// Two context hashes are maintained, a long one, h1, of length ceil((N+17)/3) 
/// bytes and a shorter one, h2, of length ceil((N+17)/5) bytes, where ceil() is 
/// the ceiling function. The index does not use collision detection. At each byte 
/// boundary, if there is not currently a match, then the bytes before the current 
/// byte are compared with the location indexed by h1. If less than 2 bytes match, 
/// then h2 is tried. If a match of length >1 is found, the match is maintained 
/// until the next bit mismatches the predicted bit. The table is updated at h1 
/// and h2 after every byte.
const MAX_LEN: usize = 62;

pub struct MatchModel {
    mch_ptr:  usize,    // Pointer to current byte in matched context in buf
    mch_len:  usize,    // Length of match
    cxt:      usize,    // Order-0 context (last 0..7 bits)
    bits:     usize,    // Number of bits in cxt
    hash_s:   usize,    // Short context hash
    hash_l:   usize,    // Long context hash
    buf_pos:  usize,    // Number of bytes in buf
    sm:       StateMap, // Len, bit, last byte -> prediction
    buf:      Vec<u8>,  // Rotating input buffer
    ht:       Vec<u32>, // Context hash -> next byte in buf
    buf_end:  usize,    // Last index of buf (for rotating buffer)
    ht_end:   usize,    // Last index of ht  (for hashing)
}
impl MatchModel {
    /// Create a new MatchModel.
    pub fn new(n: usize) -> MatchModel {
        MatchModel {
            mch_ptr:  0,    hash_s:   0,
            mch_len:  0,    hash_l:   0,
            cxt:      1,    buf_pos:  0,
            bits:     0,    
            sm:       StateMap::new(56 << 8),
            buf:      vec![0; n / 2],
            ht:       vec![0; n / 8],
            buf_end:  (n / 2) - 1,
            ht_end:   (n / 8) - 1,
        }
    }

    /// Generate a prediction and add it to a Mixer.
    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);

        let mut cxt = self.cxt;

        // Get n bits of byte at buf[mch_ptr], where n is number of bits in cxt
        // i.e. cxt currently has 3 bits, so get 3 bits of buf[mch_ptr]
        let pr_cxt = ((self.buf[self.mch_ptr] as usize) + 256) >> (8 - self.bits);

        // If the new value of pr_cxt (containing the next "predicted" bit) doesn't
        // match the new value of cxt (containing the next actual bit), reset the match.
        if self.mch_len > 0 && pr_cxt == cxt {
            let pr_bit = (self.buf[self.mch_ptr] >> (7 - self.bits) & 1) as usize;

            // Create new context consisting of the match length, 
            // the next predicted bit, and the previous byte.
            if self.mch_len < 16 { cxt = self.mch_len * 2 + pr_bit; }
            else { cxt = (self.mch_len >> 2) * 2 + pr_bit + 24; }
            
            let prev_byte = self.buf[(self.buf_pos - 1) & self.buf_end];
            cxt = cxt * 256 + prev_byte as usize;
        } 
        else {
            self.mch_len = 0;
        }
        self.sm.p(bit, cxt as i32)
    }

    /// Update context, rotating buffer, and check for matches.
    pub fn update(&mut self, bit: i32) {
        // Update order-0 context
        self.cxt = (self.cxt << 1) + bit as usize;
        self.bits += 1;                      

        if self.bits == 8 { // Byte boundary
            self.update_long_hash(); 
            self.update_short_hash(); 

            // Add byte to buffer
            self.buf[self.buf_pos] = self.cxt as u8; 
            self.buf_pos += 1;            
            self.buf_pos &= self.buf_end; 

            self.bits = 0; 
            self.cxt = 1;

            if self.mch_len > 0 { 
                self.mch_ptr += 1;
                self.mch_ptr &= self.buf_end;
                if self.mch_len < MAX_LEN { self.mch_len += 1; }
            }
            else { // No current match, try long hash
                self.check_prev_bytes(self.hash_l);
            }

            if self.mch_len < 2 { // Less than 2 bytes match, try short hash
                self.mch_len = 0;
                self.check_prev_bytes(self.hash_s);
            }

            self.ht[self.hash_s] = self.buf_pos as u32;
            self.ht[self.hash_l] = self.buf_pos as u32;
        }
    }

    /// Check bytes preceding current buffer position and bytes preceding 
    /// buffer position indexed by context hash for matches.
    pub fn check_prev_bytes(&mut self, hash: usize) {
        // Map context hash to index in buffer
        self.mch_ptr = self.ht[hash] as usize; 

        if self.mch_ptr != self.buf_pos {
            // Byte before location indexed by hash (mch_ptr) - match length (mch_len)
            // i.e. if mch_ptr is 50 and mch_len is 3, prev_byte_h is 46 
            let mut prev_byte_h = (self.mch_ptr - self.mch_len - 1) & self.buf_end;
            // Byte before current byte - match length
            let mut prev_byte   = (self.buf_pos - self.mch_len - 1) & self.buf_end;

            // Check subsequent previous bytes, stopping at a mismatch
            while self.mch_len < MAX_LEN   
            && prev_byte_h != self.buf_pos 
            && self.buf[prev_byte] == self.buf[prev_byte_h] {
                self.mch_len += 1;
                prev_byte_h = (prev_byte_h - 1) & self.buf_end; 
                prev_byte   = (prev_byte   - 1) & self.buf_end;  
            }
        }
    }
    
    /// Update short hash of length ceil((N+17)/5) bytes.
    fn update_short_hash(&mut self) {
        self.hash_s = (self.hash_s * (5 << 5) + self.cxt) & self.ht_end;
    }

    /// Update long hash of length ceil((N+17)/3) bytes.
    fn update_long_hash(&mut self) {
        self.hash_l = (self.hash_l * (3 << 3) + self.cxt) & self.ht_end;
    }

    /// Return length of match.
    pub fn len(&self) -> usize {
        self.mch_len
    }
}


/// State array length.
const B: usize = 16;

#[repr(align(64))]
#[derive(Debug)]
pub struct HashTable {
    t:     Vec<u8>, // Hash table mapping index to state array
    size:  usize,   // Size of hash table in bytes
}
impl HashTable {
    /// Create a new HashTable.
    pub fn new(n: usize) -> HashTable {
        assert!(B.is_power_of_two());
        assert!(n.is_power_of_two());
        assert!(n >= (B * 4)); 
        HashTable {
            t:     vec![0; n + B * 4 + 64],
            size:  n,
        }
    }

    /// Map context i to element 0 of state array. A state array is a set 
    /// of states corresponding to possible future contexts.
    pub fn hash(&mut self, mut i: u32) -> *mut u8 {
        i = i.wrapping_mul(123456791).rotate_right(16).wrapping_mul(234567891);
        let chksum = (i >> 24) as u8;
        let mut i = i as usize; // Convert to usize for indexing
        i = (i * B) & (self.size - B);

        if self.t[i]       == chksum { return &mut self.t[i];       }
        if self.t[i^B]     == chksum { return &mut self.t[i^B];     }
        if self.t[i^(B*2)] == chksum { return &mut self.t[i^(B*2)]; }

        if self.t[i+1] > self.t[(i+1)^B]
        || self.t[i+1] > self.t[(i+1)^(B*2)] { i ^= B; }

        if self.t[i+1] > self.t[(i+1)^B^(B*2)] { i ^= B ^ (B * 2); }

        for x in self.t[i..i+B].iter_mut() {
            *x = 0;
        }

        self.t[i] = chksum;
        &mut self.t[i]
    }
}

fn next_state(state: u8, bit: i32) -> u8 {
    STATE_TABLE[state as usize][bit as usize]
}

type SharedHashTable = Rc<RefCell<HashTable>>;

pub struct ContextModelO1 {
    bits:       usize,
    pub cxt:    u32,
    pub o1cxt:  u32,
    pub state:  *mut u8,
    pub t0:     [u8; 65_536],
    sm:         StateMap,
}
impl ContextModelO1 {
    pub fn new() -> ContextModelO1 {
        ContextModelO1 {
            bits:   0,
            cxt:    1,
            o1cxt:  0,
            state:  &mut 0,
            t0:     [0; 65_536], 
            sm:     StateMap::new(256),
        }
    }
    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);
        unsafe { 
            self.sm.p(bit, *self.state as i32) 
        }
    }
    pub fn update(&mut self, bit: i32) {
        unsafe { 
            *self.state = next_state(*self.state, bit); 
        }

        self.cxt = (self.cxt << 1) + bit as u32;
        self.bits += 1;

        if self.cxt >= 256 {
            self.cxt -= 256;
            self.o1cxt = self.cxt << 8;
            self.cxt = 1;
            self.bits = 0;
        }

        unsafe { 
            self.state = 
                ((&mut self.t0[0] as *mut u8)
                .add(self.o1cxt as usize))
                .add(self.cxt as usize);
        }
    }
}


pub struct ContextModelO2 {
    bits:       usize,
    cxt:        u32,
    cxt4:       u32,
    pub o2cxt:  u32,
    pub state:  *mut u8,
    sm:         StateMap,
    ht:         SharedHashTable,
}
impl ContextModelO2 {
    pub fn new(ht: SharedHashTable) -> ContextModelO2 {
        ContextModelO2 {
            bits:   0,
            cxt:    1,
            cxt4:   0,
            o2cxt:  0,
            state:  &mut 0,
            sm:     StateMap::new(256),
            ht,
        }
    }
    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);
        unsafe { 
            self.sm.p(bit, *self.state as i32) 
        }
    }
    pub fn update(&mut self, bit: i32) {
        unsafe { 
            *self.state = next_state(*self.state, bit); 
        }

        self.cxt = (self.cxt << 1) + bit as u32;
        self.bits += 1;

        if self.cxt >= 256 {
            self.cxt -= 256;
            self.cxt4 = (self.cxt4 << 8) | self.cxt;
            self.o2cxt = (self.cxt4 & 0xFFFF) << 5 | 0x57000000;
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o2cxt).add(1); 
            }
            self.cxt = 1;
            self.bits = 0;
        }
        if self.bits == 4 {
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o2cxt + self.cxt).add(1); 
            }
        }
        else if self.bits > 0 {
            let j = ((bit as usize) + 1) << ((self.bits & 3) - 1);
            unsafe { 
                self.state = self.state.add(j); 
            }
        }
    }
}

pub struct ContextModelO3 {
    bits:       usize,
    cxt:        u32,
    cxt4:       u32,
    pub o3cxt:  u32,
    pub state:  *mut u8,
    sm:         StateMap,
    ht:         SharedHashTable,
}
impl ContextModelO3 {
    pub fn new(ht: SharedHashTable) -> ContextModelO3 {
        ContextModelO3 {
            bits:   0,
            cxt:    1,
            cxt4:   0,
            o3cxt:  0,
            state:  &mut 0,
            sm:     StateMap::new(256),
            ht,
        }
    }
    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);
        unsafe { 
            self.sm.p(bit, *self.state as i32) 
        }
    }
    pub fn update(&mut self, bit: i32) {
        unsafe { 
            *self.state = next_state(*self.state, bit); 
        }

        self.cxt = (self.cxt << 1) + bit as u32;
        self.bits += 1;

        if self.cxt >= 256 {
            self.cxt -= 256;
            self.cxt4 = (self.cxt4 << 8) | self.cxt;
            self.o3cxt = (self.cxt4 << 8).wrapping_mul(3);
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o3cxt).add(1); 
            }
            self.cxt = 1;
            self.bits = 0;
        }
        if self.bits == 4 {
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o3cxt + self.cxt).add(1); 
            }
        }
        else if self.bits > 0 {
            let j = ((bit as usize) + 1) << ((self.bits & 3) - 1);
            unsafe { 
                self.state = self.state.add(j); 
            }
        }
    }
}

pub struct ContextModelO4 {
    bits:       usize,
    cxt:        u32,
    cxt4:       u32,
    pub o4cxt:  u32,
    pub state:  *mut u8,
    sm:         StateMap,
    ht:         SharedHashTable,
}
impl ContextModelO4 {
    pub fn new(ht: SharedHashTable) -> ContextModelO4 {
        ContextModelO4 {
            bits:   0,
            cxt:    1,
            cxt4:   0,
            o4cxt:  0,
            state:  &mut 0,
            sm:     StateMap::new(256),
            ht,
        }
    }
    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);
        unsafe { 
            self.sm.p(bit, *self.state as i32) 
        }
    }
    pub fn update(&mut self, bit: i32) {
        unsafe { 
            *self.state = next_state(*self.state, bit); 
        }

        self.cxt = (self.cxt << 1) + bit as u32;
        self.bits += 1;

        if self.cxt >= 256 {
            self.cxt -= 256;
            self.cxt4 = (self.cxt4 << 8) | self.cxt;
            self.o4cxt = self.cxt4.wrapping_mul(5); 
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o4cxt).add(1); 
            }
            self.cxt = 1;
            self.bits = 0;
        }
        if self.bits == 4 {
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o4cxt + self.cxt).add(1); 
            }
        }
        else if self.bits > 0 {
            let j = ((bit as usize) + 1) << ((self.bits & 3) - 1);
            unsafe { 
                self.state = self.state.add(j); 
            }
        }
    }
}

pub struct ContextModelO6 {
    bits:       usize,
    cxt:        u32,
    cxt4:       u32,
    pub o6cxt:  u32,
    pub state:  *mut u8,
    sm:         StateMap,
    ht:         SharedHashTable,
}
impl ContextModelO6 {
    pub fn new(ht: SharedHashTable) -> ContextModelO6 {
        ContextModelO6 {
            bits:   0,
            cxt:    1,
            cxt4:   0,
            o6cxt:  0,
            state:  &mut 0,
            sm:     StateMap::new(256),
            ht,
        }
    }
    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);
        unsafe { 
            self.sm.p(bit, *self.state as i32) 
        }
    }
    pub fn update(&mut self, bit: i32) {
        unsafe { 
            *self.state = next_state(*self.state, bit); 
        }

        self.cxt = (self.cxt << 1) + bit as u32;
        self.bits += 1;

        if self.cxt >= 256 {
            self.cxt -= 256;
            self.cxt4 = (self.cxt4 << 8) | self.cxt;
            self.o6cxt = (self.o6cxt.wrapping_mul(11 << 5) + self.cxt * 13) & 0x3FFFFFFF;
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o6cxt).add(1); 
            }
            self.cxt = 1;
            self.bits = 0;
        }
        if self.bits == 4 {
            unsafe { 
                self.state = self.ht.borrow_mut().hash(self.o6cxt + self.cxt).add(1); 
            }
        }
        else if self.bits > 0 {
            let j = ((bit as usize) + 1) << ((self.bits & 3) - 1);
            unsafe { 
                self.state = self.state.add(j); 
            }
        }
    }
}

pub struct WordModel {
    cxt:           u32,
    bits:          usize,
    pub word_cxt:  u32,
    pub state:     *mut u8,
    sm:            StateMap,
    ht:            Rc<RefCell<HashTable>>,
}
impl WordModel {
    pub fn new(ht: Rc<RefCell<HashTable>>) -> WordModel {
        WordModel {
            cxt:       1,
            bits:      0,
            word_cxt:  0,
            state:     &mut 0,
            sm:        StateMap::new(256),
            ht,
        }
    }

    pub fn p(&mut self, bit: i32) -> i32 {
        self.update(bit);
        unsafe { self.sm.p(bit, *self.state as i32) }
    }

    pub fn update(&mut self, bit: i32) {
        unsafe { *self.state = next_state(*self.state, bit); }

        self.cxt = (self.cxt << 1) + bit as u32;
        self.bits += 1;

        if self.cxt >= 256 {
            self.cxt -= 256;
            self.word_cxt = match self.cxt {
                65..=90 => {
                    self.cxt += 32; // Fold to lowercase
                    (self.word_cxt + self.cxt).wrapping_mul(7 << 3)
                },
                97..=122 => {
                    (self.word_cxt + self.cxt).wrapping_mul(7 << 3)
                },
                _ => 0,
            };
            unsafe { self.state = self.ht.borrow_mut().hash(self.word_cxt).add(1); }
            self.cxt = 1;
            self.bits = 0;
        }
        if self.bits == 4 {
            unsafe { self.state = self.ht.borrow_mut().hash(self.word_cxt + self.cxt).add(1); }
        }
        else if self.bits > 0 {
            let j = ((bit as usize) + 1) << ((self.bits & 3) - 1);
            unsafe { self.state = self.state.add(j); }
        }
    }
}


/// lpaq1 by Matt Mahoney <http://mattmahoney.net/dc/#lpaq>. 
/// lpaq1's model combines 7 contexts: orders 1, 2, 3, 4, 6, a lowercase 
/// unigram word context (for ASCII text), and a "match" order, which 
/// predicts the next bit in the last matching context. The independent 
/// bit predictions of the 7 models are combined using one of 80 neural 
/// networks (selected by a small context), then adjusted using 2 SSE 
/// stages (order 0 and 1) and arithmetic coded.
/// 
/// Prediction is bitwise. This means that an order-n context consists of 
/// the last n whole bytes plus any of the 0 to 7 previously coded bits of 
/// the current byte starting with the most significant bit. The unigram 
/// word context consists of a hash of the last (at most) 11 consecutive 
/// letters (A-Z, a-z) folded to lower case. The context does not include 
/// any nonalphabetic characters nor any characters preceding the last 
/// nonalphabetic character.
/// 
/// The first 6 contexts (orders 1..4, 6, word) are used to index a hash 
/// table to look up a bit-history represented by an 8-bit state. A state 
/// can either represent all histories up to 4 bits long, or a pair of 0,1 
/// counts plus a flag to indicate the most recent bit. The counts are 
/// bounded by (41,0), (40,1), (12,2), (5,3), (4,4) and likewise for 1,0. 
/// If a count is exceeded, the opposite count is reduced to approximately 
/// preserve the count ratio. The last bit flag is present only for states 
/// whose total count is less than 16. There are 253 possible states.
///
/// The 7 predictions are combined using a neural network (Mixer). The
/// inputs p_i, i=0..6 are first stretched: t_i = log(p_i/(1 - p_i)), 
/// then the output is computed: p = squash(SUM_i t_i * w_i), where
/// squash(x) = 1/(1 + exp(-x)) is the inverse of stretch(). The weights
/// are adjusted to reduce the error: w_i := w_i + L * t_i * (y - p) where
/// (y - p) is the prediction error and L ~ 0.002 is the learning rate.
/// This is a standard single layer backpropagation network modified to
/// minimize coding cost rather than RMS prediction error (thus dropping
/// the factors p * (1 - p) from learning).
/// 
/// One of 80 neural networks are selected by a context that depends on
/// the 3 high order bits of the last whole byte plus the context order
/// (quantized to 0, 1, 2, 3, 4, 6, 8, 12, 16, 32). The order is
/// determined by the number of nonzero bit histories and the length of
/// the match from MatchModel.
/// 
/// The Mixer output is adjusted by 2 SSE stages (called APM for adaptive
/// probability map). An APM is a StateMap that accepts both a discrte
/// context and an input probability, pr. pr is stetched and quantized
/// to 24 levels. The output is interpolated between the 2 nearest table 
/// entries, and then only the nearest entry is updated. The entries are 
/// initialized to p = pr and n = 6 (to slow down initial adaptation)
/// with a limit n <= 255. The two stages use a discrete order 0 context 
/// (last 0..7 bits) and a hashed order-1 context (14 bits). Each output 
/// is averaged with its input weighted by 1/4.
/// 
/// The output is arithmetic coded. The code for a string s with probability
/// p(s) is a number between Q and Q+p(x) where Q is the total probability of 
/// all strings lexicographically preceding s. The number is coded as a big-
/// -endian base-256 fraction.
pub struct Predictor {
    pr:    i32,            // Prediction
    wm:    WordModel,      // Lowercase unigram word model
    mm:    MatchModel,     // Match model
    cm1:   ContextModelO1, // Order 1 context model
    cm2:   ContextModelO2, // Order 2 context model 
    cm3:   ContextModelO3, // Order 3 context model
    cm4:   ContextModelO4, // Order 4 context model
    cm6:   ContextModelO6, // Order 6 context model
    mxr:   Mixer,          // For weighted averaging of independent predictions
    apm1:  Apm,            // Adaptive Probability Map for refining Mixer output
    apm2:  Apm,            //
}
impl Predictor {
    /// Create a new Predictor.
    pub fn new() -> Predictor {
        // Hash table for mapping context hashes to state arrays.
        // Shared between models.
        let ht = Rc::new(RefCell::new(HashTable::new(MEM*2)));

        let mut p = Predictor {           
            pr:    2048,         
            cm1:   ContextModelO1::new(),
            cm2:   ContextModelO2::new(Rc::clone(&ht)),
            cm3:   ContextModelO3::new(Rc::clone(&ht)),
            cm4:   ContextModelO4::new(Rc::clone(&ht)),
            cm6:   ContextModelO6::new(Rc::clone(&ht)),
            wm:    WordModel::new(Rc::clone(&ht)),
            mm:    MatchModel::new(MEM),
            mxr:   Mixer::new(7, 80),
            apm1:  Apm::new(256),
            apm2:  Apm::new(16384),
        };
        
        p.wm.state  = &mut p.cm1.t0[0];
        p.cm1.state = &mut p.cm1.t0[0];
        p.cm2.state = &mut p.cm1.t0[0];
        p.cm3.state = &mut p.cm1.t0[0];
        p.cm4.state = &mut p.cm1.t0[0];
        p.cm6.state = &mut p.cm1.t0[0];
        p
    }

    /// Return current prediction.
    pub fn p(&mut self) -> i32 {
        assert!(self.pr >= 0 && self.pr < 4096);
        self.pr
    }

    /// Update contexts and states, map states to predictions, and mix
    /// predictions in Mixer.
    pub fn update(&mut self, bit: i32) {
        assert!(bit == 0 || bit == 1);
        
        self.mxr.update(bit);
        
        // Add independent predictions to mixer
        self.mxr.add(stretch(self.mm.p(bit)));
        self.mxr.add(stretch(self.wm.p(bit)));
        self.mxr.add(stretch(self.cm1.p(bit)));
        self.mxr.add(stretch(self.cm2.p(bit)));
        self.mxr.add(stretch(self.cm3.p(bit)));
        self.mxr.add(stretch(self.cm4.p(bit)));
        self.mxr.add(stretch(self.cm6.p(bit)));
        
        // Set weights to be used during mixing
        let order = self.order(self.mm.len());
        self.mxr.set(order + 10 * (self.cm1.o1cxt >> 13));

        // Mix
        self.pr = self.mxr.p();

        // 2 SSE stages
        self.pr = (self.pr + 3 * self.apm1.p(bit, 7, self.pr, self.cm1.cxt)) >> 2;
        self.pr = (self.pr + 3 * self.apm2.p(bit, 7, self.pr, self.cm1.cxt ^ self.cm1.o1cxt >> 2)) >> 2;
    }

    /// Determine order from match model length or number
    /// of non-zero bit histories.
    fn order(&mut self, len: usize) -> u32 {
        let mut order: u32 = 0;

        // If len is 0, order is determined from 
        // number of non-zero bit histories
        if len == 0 {
            unsafe {
                if *self.cm2.state != 0 { order += 1; }
                if *self.cm3.state != 0 { order += 1; }
                if *self.cm4.state != 0 { order += 1; }
                if *self.cm6.state != 0 { order += 1; }
            }
        }
        else {
            order = 5 +
            if len >= 8  { 1 } else { 0 } +
            if len >= 12 { 1 } else { 0 } +
            if len >= 16 { 1 } else { 0 } +
            if len >= 32 { 1 } else { 0 };
        }
        order
    }
}


// Encoder
struct Encoder {
    high:       u32,
    low:        u32,
    predictor:  Predictor,
    archive:    BufWriter<File>,
}
impl Encoder {
    fn new(archive: BufWriter<File>) -> Encoder {
        let mut enc = Encoder {
            high: 0xFFFFFFFF, 
            low: 0, 
            predictor: Predictor::new(), 
            archive
        };   
        enc.archive.write_u64(0);
        enc.archive.write_u64(0);
        enc.archive.write_u64(0);
        enc
    }
    fn compress_bit(&mut self, bit: i32) {
        let mut p = self.predictor.p() as u32;
        if p < 2048 { p += 1; }

        let range = self.high - self.low;
        let mid: u32 = self.low + (range >> 12) * p
                       + ((range & 0x0FFF) * p >> 12);
                       
        if bit == 1 {
            self.high = mid;
        } 
        else {
            self.low = mid + 1;
        }
        self.predictor.update(bit);
        
        while ( (self.high ^ self.low) & 0xFF000000) == 0 {
            self.archive.write_byte((self.high >> 24) as u8);
            self.high = (self.high << 8) + 255;
            self.low <<= 8;  
        }
    }
    fn flush(&mut self) {
        while ( (self.high ^ self.low) & 0xFF000000) == 0 {
            self.archive.write_byte((self.high >> 24) as u8);
            self.high = (self.high << 8) + 255;
            self.low <<= 8; 
        }
        self.archive.write_byte((self.high >> 24) as u8);
        self.archive.flush_buffer();
    }

    fn compress_block(&mut self, block: &[u8]) {
        for byte in block.iter() {
            for i in (0..=7).rev() {
                self.compress_bit(((*byte >> i) & 1) as i32);
            }   
        }
    }
    // Write 24 byte block data header
    fn write_block_data(&mut self, final_block_size: usize, block_size: usize, num_blocks: usize) {
        self.archive.get_ref().rewind().unwrap();
        self.archive.write_u64(final_block_size as u64);
        self.archive.write_u64(block_size as u64);
        self.archive.write_u64(num_blocks as u64);    
    }
}


struct Decoder {
    high:       u32,
    low:        u32,
    predictor:  Predictor,
    archive:    BufReader<File>,
    x:          u32, 
}
impl Decoder {
    fn new(archive: BufReader<File>) -> Decoder {
        Decoder {
            high: 0xFFFFFFFF, 
            low: 0, 
            x: 0, 
            predictor: Predictor::new(), 
            archive,
        }
    }
    fn decompress_bit(&mut self) -> i32 {
        let mut p = self.predictor.p() as u32;
        if p < 2048 { p += 1; }

        let range = self.high - self.low;
        let mid: u32 = self.low + (range >> 12) * p
                       + ((range & 0x0FFF) * p >> 12);

        let mut bit: i32 = 0;
        if self.x <= mid {
            bit = 1;
            self.high = mid;
        } 
        else {
            self.low = mid + 1;
        }
        self.predictor.update(bit);
        
        while ( (self.high ^ self.low) & 0xFF000000) == 0 {
            self.high = (self.high << 8) + 255;
            self.low <<= 8; 
            self.x = (self.x << 8) + self.archive.read_byte() as u32; 
        }
        bit
    }
    fn decompress_block(&mut self, block_size: usize) -> Vec<u8> {
        let mut block: Vec<u8> = Vec::with_capacity(block_size); 
        while block.len() < block.capacity() {
            let mut byte: i32 = 1;
            while byte < 256 {
                byte += byte + self.decompress_bit();
            }
            byte -= 256;
            block.push(byte as u8); 
        }
        block
    }
    // Read 24 byte block data header
    fn read_block_data(&mut self) -> (usize, usize, usize) {
        (
        self.archive.read_u64() as usize, 
        self.archive.read_u64() as usize,
        self.archive.read_u64() as usize
        ) 
    }
    fn init_x(&mut self) {
        for _ in 0..4 {
            self.x = (self.x << 8) + self.archive.read_byte() as u32;
        }
    }
}


fn main() {
    let start_time = Instant::now();
    let args: Vec<String> = env::args().skip(1).collect();

    let mut file_in  = new_input_file(&args[1]);
    let mut file_out = new_output_file(&args[2]);

    match (&args[0]).as_str() {
        "c" => {  
            let mut final_block_size = 0;
            let mut num_blocks = 0;

            let mut enc = Encoder::new(file_out);

            // Compress ---------------------------------------------------
            loop {
                if file_in.fill_buffer() == BufferState::Empty { break; }
                final_block_size = file_in.buffer().len();
                enc.compress_block(&file_in.buffer());
                num_blocks += 1;
            } 
            // ------------------------------------------------------------
            enc.flush();
            enc.write_block_data(final_block_size, file_in.capacity(), num_blocks);
            println!("Finished Compressing.");
        }
        "d" => {
            let mut dec = Decoder::new(file_in);

            let (final_block_size, block_size, num_blocks) = dec.read_block_data();

            // Call after reading header
            dec.init_x();

            // Decompress -------------------------------------------------
            for _ in 0..(num_blocks - 1) {
                let block = dec.decompress_block(block_size);
                for byte in block.iter() {
                    file_out.write_byte(*byte);
                }
            }
            let block = dec.decompress_block(final_block_size);
            for byte in block.iter() {
                file_out.write_byte(*byte);
            }
            // ------------------------------------------------------------
            file_out.flush_buffer();
            println!("Finished Decompressing.");  
        }
        _ => { 
            println!("To Compress: c input output");
            println!("To Decompress: d input output");
        }
    }
    let file_in_size  = metadata(Path::new(&args[1])).unwrap().len();
    let file_out_size = metadata(Path::new(&args[2])).unwrap().len();   
    println!("{} bytes -> {} bytes in {:.2?}", 
    file_in_size, file_out_size, start_time.elapsed());  
}


const STATE_TABLE: [[u8; 2]; 256] = [
[  1,  2],[  3,  5],[  4,  6],[  7, 10],[  8, 12],[  9, 13],[ 11, 14], // 0
[ 15, 19],[ 16, 23],[ 17, 24],[ 18, 25],[ 20, 27],[ 21, 28],[ 22, 29], // 7
[ 26, 30],[ 31, 33],[ 32, 35],[ 32, 35],[ 32, 35],[ 32, 35],[ 34, 37], // 14
[ 34, 37],[ 34, 37],[ 34, 37],[ 34, 37],[ 34, 37],[ 36, 39],[ 36, 39], // 21
[ 36, 39],[ 36, 39],[ 38, 40],[ 41, 43],[ 42, 45],[ 42, 45],[ 44, 47], // 28
[ 44, 47],[ 46, 49],[ 46, 49],[ 48, 51],[ 48, 51],[ 50, 52],[ 53, 43], // 35
[ 54, 57],[ 54, 57],[ 56, 59],[ 56, 59],[ 58, 61],[ 58, 61],[ 60, 63], // 42
[ 60, 63],[ 62, 65],[ 62, 65],[ 50, 66],[ 67, 55],[ 68, 57],[ 68, 57], // 49
[ 70, 73],[ 70, 73],[ 72, 75],[ 72, 75],[ 74, 77],[ 74, 77],[ 76, 79], // 56
[ 76, 79],[ 62, 81],[ 62, 81],[ 64, 82],[ 83, 69],[ 84, 71],[ 84, 71], // 63
[ 86, 73],[ 86, 73],[ 44, 59],[ 44, 59],[ 58, 61],[ 58, 61],[ 60, 49], // 70
[ 60, 49],[ 76, 89],[ 76, 89],[ 78, 91],[ 78, 91],[ 80, 92],[ 93, 69], // 77
[ 94, 87],[ 94, 87],[ 96, 45],[ 96, 45],[ 48, 99],[ 48, 99],[ 88,101], // 84
[ 88,101],[ 80,102],[103, 69],[104, 87],[104, 87],[106, 57],[106, 57], // 91
[ 62,109],[ 62,109],[ 88,111],[ 88,111],[ 80,112],[113, 85],[114, 87], // 98
[114, 87],[116, 57],[116, 57],[ 62,119],[ 62,119],[ 88,121],[ 88,121], // 105
[ 90,122],[123, 85],[124, 97],[124, 97],[126, 57],[126, 57],[ 62,129], // 112
[ 62,129],[ 98,131],[ 98,131],[ 90,132],[133, 85],[134, 97],[134, 97], // 119
[136, 57],[136, 57],[ 62,139],[ 62,139],[ 98,141],[ 98,141],[ 90,142], // 126
[143, 95],[144, 97],[144, 97],[ 68, 57],[ 68, 57],[ 62, 81],[ 62, 81], // 133
[ 98,147],[ 98,147],[100,148],[149, 95],[150,107],[150,107],[108,151], // 140
[108,151],[100,152],[153, 95],[154,107],[108,155],[100,156],[157, 95], // 147
[158,107],[108,159],[100,160],[161,105],[162,107],[108,163],[110,164], // 154
[165,105],[166,117],[118,167],[110,168],[169,105],[170,117],[118,171], // 161
[110,172],[173,105],[174,117],[118,175],[110,176],[177,105],[178,117], // 168
[118,179],[110,180],[181,115],[182,117],[118,183],[120,184],[185,115], // 175
[186,127],[128,187],[120,188],[189,115],[190,127],[128,191],[120,192], // 182
[193,115],[194,127],[128,195],[120,196],[197,115],[198,127],[128,199], // 189
[120,200],[201,115],[202,127],[128,203],[120,204],[205,115],[206,127], // 196
[128,207],[120,208],[209,125],[210,127],[128,211],[130,212],[213,125], // 203
[214,137],[138,215],[130,216],[217,125],[218,137],[138,219],[130,220], // 210
[221,125],[222,137],[138,223],[130,224],[225,125],[226,137],[138,227], // 217
[130,228],[229,125],[230,137],[138,231],[130,232],[233,125],[234,137], // 224
[138,235],[130,236],[237,125],[238,137],[138,239],[130,240],[241,125], // 231
[242,137],[138,243],[130,244],[245,135],[246,137],[138,247],[140,248], // 238
[249,135],[250, 69],[ 80,251],[140,252],[249,135],[250, 69],[ 80,251], // 245
[140,252],[  0,  0],[  0,  0],[  0,  0]];  // 252


pub const STRETCH_TABLE: [i16; 4096] = [
-2047, -2047, -1984, -1856, -1770, -1728, -1685, -1648, -1616, -1584, -1552, -1525, -1504,
-1482, -1461, -1440, -1418, -1402, -1390, -1378, -1367, -1355, -1344, -1332, -1320,
-1309, -1297, -1285, -1276, -1269, -1262, -1255, -1248, -1240, -1233, -1226, -1219,
-1212, -1205, -1198, -1191, -1184, -1176, -1169, -1162, -1155, -1149, -1145, -1140,
-1136, -1131, -1126, -1122, -1117, -1113, -1108, -1104, -1099, -1094, -1090, -1085,
-1081, -1076, -1072, -1067, -1062, -1058, -1053, -1049, -1044, -1040, -1035, -1030,
-1026, -1022, -1019, -1017, -1014, -1011, -1009, -1006, -1003, -1000,  -998,  -995,
 -992,  -989,  -987,  -984,  -981,  -979,  -976,  -973,  -970,  -968,  -965,  -962,
 -960,  -957,  -954,  -951,  -949,  -946,  -943,  -940,  -938,  -935,  -932,  -930,
 -927,  -924,  -921,  -919,  -916,  -913,  -910,  -908,  -905,  -902,  -900,  -897,
 -895,  -893,  -891,  -889,  -888,  -886,  -884,  -883,  -881,  -879,  -877,  -876,
 -874,  -872,  -870,  -869,  -867,  -865,  -864,  -862,  -860,  -858,  -857,  -855,
 -853,  -851,  -850,  -848,  -846,  -844,  -843,  -841,  -839,  -838,  -836,  -834,
 -832,  -831,  -829,  -827,  -825,  -824,  -822,  -820,  -819,  -817,  -815,  -813,
 -812,  -810,  -808,  -806,  -805,  -803,  -801,  -800,  -798,  -796,  -794,  -793,
 -791,  -789,  -787,  -786,  -784,  -782,  -780,  -779,  -777,  -775,  -774,  -772,
 -770,  -768,  -767,  -766,  -765,  -764,  -763,  -761,  -760,  -759,  -758,  -757,
 -756,  -755,  -754,  -753,  -752,  -750,  -749,  -748,  -747,  -746,  -745,  -744,
 -743,  -742,  -740,  -739,  -738,  -737,  -736,  -735,  -734,  -733,  -732,  -731,
 -729,  -728,  -727,  -726,  -725,  -724,  -723,  -722,  -721,  -720,  -718,  -717,
 -716,  -715,  -714,  -713,  -712,  -711,  -710,  -708,  -707,  -706,  -705,  -704,
 -703,  -702,  -701,  -700,  -699,  -697,  -696,  -695,  -694,  -693,  -692,  -691,
 -690,  -689,  -688,  -686,  -685,  -684,  -683,  -682,  -681,  -680,  -679,  -678,
 -676,  -675,  -674,  -673,  -672,  -671,  -670,  -669,  -668,  -667,  -665,  -664,
 -663,  -662,  -661,  -660,  -659,  -658,  -657,  -656,  -654,  -653,  -652,  -651,
 -650,  -649,  -648,  -647,  -646,  -644,  -643,  -642,  -641,  -640,  -639,  -638,
 -638,  -637,  -636,  -636,  -635,  -634,  -633,  -633,  -632,  -631,  -631,  -630,
 -629,  -628,  -628,  -627,  -626,  -625,  -625,  -624,  -623,  -623,  -622,  -621,
 -620,  -620,  -619,  -618,  -618,  -617,  -616,  -615,  -615,  -614,  -613,  -613,
 -612,  -611,  -610,  -610,  -609,  -608,  -608,  -607,  -606,  -605,  -605,  -604,
 -603,  -602,  -602,  -601,  -600,  -600,  -599,  -598,  -597,  -597,  -596,  -595,
 -595,  -594,  -593,  -592,  -592,  -591,  -590,  -590,  -589,  -588,  -587,  -587,
 -586,  -585,  -584,  -584,  -583,  -582,  -582,  -581,  -580,  -579,  -579,  -578,
 -577,  -577,  -576,  -575,  -574,  -574,  -573,  -572,  -572,  -571,  -570,  -569,
 -569,  -568,  -567,  -567,  -566,  -565,  -564,  -564,  -563,  -562,  -561,  -561,
 -560,  -559,  -559,  -558,  -557,  -556,  -556,  -555,  -554,  -554,  -553,  -552,
 -551,  -551,  -550,  -549,  -549,  -548,  -547,  -546,  -546,  -545,  -544,  -544,
 -543,  -542,  -541,  -541,  -540,  -539,  -538,  -538,  -537,  -536,  -536,  -535,
 -534,  -533,  -533,  -532,  -531,  -531,  -530,  -529,  -528,  -528,  -527,  -526,
 -526,  -525,  -524,  -523,  -523,  -522,  -521,  -520,  -520,  -519,  -518,  -518,
 -517,  -516,  -515,  -515,  -514,  -513,  -513,  -512,  -511,  -511,  -510,  -510,
 -509,  -509,  -508,  -508,  -507,  -507,  -506,  -506,  -505,  -505,  -504,  -504,
 -503,  -503,  -502,  -502,  -501,  -501,  -500,  -500,  -499,  -499,  -498,  -498,
 -497,  -497,  -496,  -496,  -495,  -495,  -494,  -494,  -493,  -493,  -492,  -492,
 -491,  -491,  -490,  -490,  -490,  -489,  -489,  -488,  -488,  -487,  -487,  -486,
 -486,  -485,  -485,  -484,  -484,  -483,  -483,  -482,  -482,  -481,  -481,  -480,
 -480,  -479,  -479,  -478,  -478,  -477,  -477,  -476,  -476,  -475,  -475,  -474,
 -474,  -473,  -473,  -472,  -472,  -471,  -471,  -470,  -470,  -469,  -469,  -468,
 -468,  -467,  -467,  -466,  -466,  -465,  -465,  -464,  -464,  -463,  -463,  -462,
 -462,  -461,  -461,  -460,  -460,  -459,  -459,  -458,  -458,  -457,  -457,  -456,
 -456,  -455,  -455,  -454,  -454,  -453,  -453,  -452,  -452,  -451,  -451,  -450,
 -450,  -449,  -449,  -448,  -448,  -448,  -447,  -447,  -446,  -446,  -445,  -445,
 -444,  -444,  -443,  -443,  -442,  -442,  -441,  -441,  -440,  -440,  -439,  -439,
 -438,  -438,  -437,  -437,  -436,  -436,  -435,  -435,  -434,  -434,  -433,  -433,
 -432,  -432,  -431,  -431,  -430,  -430,  -429,  -429,  -428,  -428,  -427,  -427,
 -426,  -426,  -425,  -425,  -424,  -424,  -423,  -423,  -422,  -422,  -421,  -421,
 -420,  -420,  -419,  -419,  -418,  -418,  -417,  -417,  -416,  -416,  -415,  -415,
 -414,  -414,  -413,  -413,  -412,  -412,  -411,  -411,  -410,  -410,  -409,  -409,
 -408,  -408,  -407,  -407,  -406,  -406,  -405,  -405,  -405,  -404,  -404,  -403,
 -403,  -402,  -402,  -401,  -401,  -400,  -400,  -399,  -399,  -398,  -398,  -397,
 -397,  -396,  -396,  -395,  -395,  -394,  -394,  -393,  -393,  -392,  -392,  -391,
 -391,  -390,  -390,  -389,  -389,  -388,  -388,  -387,  -387,  -386,  -386,  -385,
 -385,  -384,  -384,  -383,  -383,  -383,  -382,  -382,  -382,  -381,  -381,  -380,
 -380,  -380,  -379,  -379,  -379,  -378,  -378,  -378,  -377,  -377,  -376,  -376,
 -376,  -375,  -375,  -375,  -374,  -374,  -374,  -373,  -373,  -372,  -372,  -372,
 -371,  -371,  -371,  -370,  -370,  -370,  -369,  -369,  -368,  -368,  -368,  -367,
 -367,  -367,  -366,  -366,  -366,  -365,  -365,  -365,  -364,  -364,  -363,  -363,
 -363,  -362,  -362,  -362,  -361,  -361,  -361,  -360,  -360,  -359,  -359,  -359,
 -358,  -358,  -358,  -357,  -357,  -357,  -356,  -356,  -355,  -355,  -355,  -354,
 -354,  -354,  -353,  -353,  -353,  -352,  -352,  -352,  -351,  -351,  -350,  -350,
 -350,  -349,  -349,  -349,  -348,  -348,  -348,  -347,  -347,  -346,  -346,  -346,
 -345,  -345,  -345,  -344,  -344,  -344,  -343,  -343,  -342,  -342,  -342,  -341,
 -341,  -341,  -340,  -340,  -340,  -339,  -339,  -338,  -338,  -338,  -337,  -337,
 -337,  -336,  -336,  -336,  -335,  -335,  -335,  -334,  -334,  -333,  -333,  -333,
 -332,  -332,  -332,  -331,  -331,  -331,  -330,  -330,  -329,  -329,  -329,  -328,
 -328,  -328,  -327,  -327,  -327,  -326,  -326,  -325,  -325,  -325,  -324,  -324,
 -324,  -323,  -323,  -323,  -322,  -322,  -321,  -321,  -321,  -320,  -320,  -320,
 -319,  -319,  -319,  -318,  -318,  -318,  -317,  -317,  -316,  -316,  -316,  -315,
 -315,  -315,  -314,  -314,  -314,  -313,  -313,  -312,  -312,  -312,  -311,  -311,
 -311,  -310,  -310,  -310,  -309,  -309,  -308,  -308,  -308,  -307,  -307,  -307,
 -306,  -306,  -306,  -305,  -305,  -304,  -304,  -304,  -303,  -303,  -303,  -302,
 -302,  -302,  -301,  -301,  -301,  -300,  -300,  -299,  -299,  -299,  -298,  -298,
 -298,  -297,  -297,  -297,  -296,  -296,  -295,  -295,  -295,  -294,  -294,  -294,
 -293,  -293,  -293,  -292,  -292,  -291,  -291,  -291,  -290,  -290,  -290,  -289,
 -289,  -289,  -288,  -288,  -288,  -287,  -287,  -286,  -286,  -286,  -285,  -285,
 -285,  -284,  -284,  -284,  -283,  -283,  -282,  -282,  -282,  -281,  -281,  -281,
 -280,  -280,  -280,  -279,  -279,  -278,  -278,  -278,  -277,  -277,  -277,  -276,
 -276,  -276,  -275,  -275,  -274,  -274,  -274,  -273,  -273,  -273,  -272,  -272,
 -272,  -271,  -271,  -271,  -270,  -270,  -269,  -269,  -269,  -268,  -268,  -268,
 -267,  -267,  -267,  -266,  -266,  -265,  -265,  -265,  -264,  -264,  -264,  -263,
 -263,  -263,  -262,  -262,  -261,  -261,  -261,  -260,  -260,  -260,  -259,  -259,
 -259,  -258,  -258,  -257,  -257,  -257,  -256,  -256,  -256,  -255,  -255,  -255,
 -254,  -254,  -254,  -254,  -253,  -253,  -253,  -252,  -252,  -252,  -252,  -251,
 -251,  -251,  -250,  -250,  -250,  -250,  -249,  -249,  -249,  -248,  -248,  -248,
 -248,  -247,  -247,  -247,  -246,  -246,  -246,  -246,  -245,  -245,  -245,  -244,
 -244,  -244,  -244,  -243,  -243,  -243,  -242,  -242,  -242,  -242,  -241,  -241,
 -241,  -240,  -240,  -240,  -240,  -239,  -239,  -239,  -238,  -238,  -238,  -238,
 -237,  -237,  -237,  -236,  -236,  -236,  -236,  -235,  -235,  -235,  -234,  -234,
 -234,  -233,  -233,  -233,  -233,  -232,  -232,  -232,  -231,  -231,  -231,  -231,
 -230,  -230,  -230,  -229,  -229,  -229,  -229,  -228,  -228,  -228,  -227,  -227,
 -227,  -227,  -226,  -226,  -226,  -225,  -225,  -225,  -225,  -224,  -224,  -224,
 -223,  -223,  -223,  -223,  -222,  -222,  -222,  -221,  -221,  -221,  -221,  -220,
 -220,  -220,  -219,  -219,  -219,  -219,  -218,  -218,  -218,  -217,  -217,  -217,
 -217,  -216,  -216,  -216,  -215,  -215,  -215,  -215,  -214,  -214,  -214,  -213,
 -213,  -213,  -212,  -212,  -212,  -212,  -211,  -211,  -211,  -210,  -210,  -210,
 -210,  -209,  -209,  -209,  -208,  -208,  -208,  -208,  -207,  -207,  -207,  -206,
 -206,  -206,  -206,  -205,  -205,  -205,  -204,  -204,  -204,  -204,  -203,  -203,
 -203,  -202,  -202,  -202,  -202,  -201,  -201,  -201,  -200,  -200,  -200,  -200,
 -199,  -199,  -199,  -198,  -198,  -198,  -198,  -197,  -197,  -197,  -196,  -196,
 -196,  -196,  -195,  -195,  -195,  -194,  -194,  -194,  -194,  -193,  -193,  -193,
 -192,  -192,  -192,  -192,  -191,  -191,  -191,  -190,  -190,  -190,  -189,  -189,
 -189,  -189,  -188,  -188,  -188,  -187,  -187,  -187,  -187,  -186,  -186,  -186,
 -185,  -185,  -185,  -185,  -184,  -184,  -184,  -183,  -183,  -183,  -183,  -182,
 -182,  -182,  -181,  -181,  -181,  -181,  -180,  -180,  -180,  -179,  -179,  -179,
 -179,  -178,  -178,  -178,  -177,  -177,  -177,  -177,  -176,  -176,  -176,  -175,
 -175,  -175,  -175,  -174,  -174,  -174,  -173,  -173,  -173,  -173,  -172,  -172,
 -172,  -171,  -171,  -171,  -171,  -170,  -170,  -170,  -169,  -169,  -169,  -168,
 -168,  -168,  -168,  -167,  -167,  -167,  -166,  -166,  -166,  -166,  -165,  -165,
 -165,  -164,  -164,  -164,  -164,  -163,  -163,  -163,  -162,  -162,  -162,  -162,
 -161,  -161,  -161,  -160,  -160,  -160,  -160,  -159,  -159,  -159,  -158,  -158,
 -158,  -158,  -157,  -157,  -157,  -156,  -156,  -156,  -156,  -155,  -155,  -155,
 -154,  -154,  -154,  -154,  -153,  -153,  -153,  -152,  -152,  -152,  -152,  -151,
 -151,  -151,  -150,  -150,  -150,  -150,  -149,  -149,  -149,  -148,  -148,  -148,
 -147,  -147,  -147,  -147,  -146,  -146,  -146,  -145,  -145,  -145,  -145,  -144,
 -144,  -144,  -143,  -143,  -143,  -143,  -142,  -142,  -142,  -141,  -141,  -141,
 -141,  -140,  -140,  -140,  -139,  -139,  -139,  -139,  -138,  -138,  -138,  -137,
 -137,  -137,  -137,  -136,  -136,  -136,  -135,  -135,  -135,  -135,  -134,  -134,
 -134,  -133,  -133,  -133,  -133,  -132,  -132,  -132,  -131,  -131,  -131,  -131,
 -130,  -130,  -130,  -129,  -129,  -129,  -129,  -128,  -128,  -128,  -127,  -127,
 -127,  -127,  -126,  -126,  -126,  -126,  -125,  -125,  -125,  -125,  -124,  -124,
 -124,  -124,  -123,  -123,  -123,  -123,  -122,  -122,  -122,  -121,  -121,  -121,
 -121,  -120,  -120,  -120,  -120,  -119,  -119,  -119,  -119,  -118,  -118,  -118,
 -118,  -117,  -117,  -117,  -117,  -116,  -116,  -116,  -116,  -115,  -115,  -115,
 -115,  -114,  -114,  -114,  -114,  -113,  -113,  -113,  -113,  -112,  -112,  -112,
 -112,  -111,  -111,  -111,  -111,  -110,  -110,  -110,  -109,  -109,  -109,  -109,
 -108,  -108,  -108,  -108,  -107,  -107,  -107,  -107,  -106,  -106,  -106,  -106,
 -105,  -105,  -105,  -105,  -104,  -104,  -104,  -104,  -103,  -103,  -103,  -103,
 -102,  -102,  -102,  -102,  -101,  -101,  -101,  -101,  -100,  -100,  -100,  -100,
  -99,   -99,   -99,   -99,   -98,   -98,   -98,   -97,   -97,   -97,   -97,   -96,
  -96,   -96,   -96,   -95,   -95,   -95,   -95,   -94,   -94,   -94,   -94,   -93,
  -93,   -93,   -93,   -92,   -92,   -92,   -92,   -91,   -91,   -91,   -91,   -90,
  -90,   -90,   -90,   -89,   -89,   -89,   -89,   -88,   -88,   -88,   -88,   -87,
  -87,   -87,   -86,   -86,   -86,   -86,   -85,   -85,   -85,   -85,   -84,   -84,
  -84,   -84,   -83,   -83,   -83,   -83,   -82,   -82,   -82,   -82,   -81,   -81,
  -81,   -81,   -80,   -80,   -80,   -80,   -79,   -79,   -79,   -79,   -78,   -78,
  -78,   -78,   -77,   -77,   -77,   -77,   -76,   -76,   -76,   -76,   -75,   -75,
  -75,   -74,   -74,   -74,   -74,   -73,   -73,   -73,   -73,   -72,   -72,   -72,
  -72,   -71,   -71,   -71,   -71,   -70,   -70,   -70,   -70,   -69,   -69,   -69,
  -69,   -68,   -68,   -68,   -68,   -67,   -67,   -67,   -67,   -66,   -66,   -66,
  -66,   -65,   -65,   -65,   -65,   -64,   -64,   -64,   -64,   -63,   -63,   -63,
  -62,   -62,   -62,   -62,   -61,   -61,   -61,   -61,   -60,   -60,   -60,   -60,
  -59,   -59,   -59,   -59,   -58,   -58,   -58,   -58,   -57,   -57,   -57,   -57,
  -56,   -56,   -56,   -56,   -55,   -55,   -55,   -55,   -54,   -54,   -54,   -54,
  -53,   -53,   -53,   -53,   -52,   -52,   -52,   -51,   -51,   -51,   -51,   -50,
  -50,   -50,   -50,   -49,   -49,   -49,   -49,   -48,   -48,   -48,   -48,   -47,
  -47,   -47,   -47,   -46,   -46,   -46,   -46,   -45,   -45,   -45,   -45,   -44,
  -44,   -44,   -44,   -43,   -43,   -43,   -43,   -42,   -42,   -42,   -42,   -41,
  -41,   -41,   -41,   -40,   -40,   -40,   -39,   -39,   -39,   -39,   -38,   -38,
  -38,   -38,   -37,   -37,   -37,   -37,   -36,   -36,   -36,   -36,   -35,   -35,
  -35,   -35,   -34,   -34,   -34,   -34,   -33,   -33,   -33,   -33,   -32,   -32,
  -32,   -32,   -31,   -31,   -31,   -31,   -30,   -30,   -30,   -30,   -29,   -29,
  -29,   -28,   -28,   -28,   -28,   -27,   -27,   -27,   -27,   -26,   -26,   -26,
  -26,   -25,   -25,   -25,   -25,   -24,   -24,   -24,   -24,   -23,   -23,   -23,
  -23,   -22,   -22,   -22,   -22,   -21,   -21,   -21,   -21,   -20,   -20,   -20,
  -20,   -19,   -19,   -19,   -19,   -18,   -18,   -18,   -18,   -17,   -17,   -17,
  -16,   -16,   -16,   -16,   -15,   -15,   -15,   -15,   -14,   -14,   -14,   -14,
  -13,   -13,   -13,   -13,   -12,   -12,   -12,   -12,   -11,   -11,   -11,   -11,
  -10,   -10,   -10,   -10,    -9,    -9,    -9,    -9,    -8,    -8,    -8,    -8,
   -7,    -7,    -7,    -7,    -6,    -6,    -6,    -6,    -5,    -5,    -5,    -4,
   -4,    -4,    -4,    -3,    -3,    -3,    -3,    -2,    -2,    -2,    -2,    -1,
   -1,    -1,    -1,     0,     0,     0,     0,     1,     1,     1,     1,     2,
    2,     2,     2,     3,     3,     3,     3,     4,     4,     4,     4,     5,
    5,     5,     5,     6,     6,     6,     6,     7,     7,     7,     8,     8,
    8,     8,     9,     9,     9,     9,    10,    10,    10,    10,    11,    11,
   11,    11,    12,    12,    12,    12,    13,    13,    13,    13,    14,    14,
   14,    14,    15,    15,    15,    15,    16,    16,    16,    16,    17,    17,
   17,    17,    18,    18,    18,    18,    19,    19,    19,    19,    20,    20,
   20,    21,    21,    21,    21,    22,    22,    22,    22,    23,    23,    23,
   23,    24,    24,    24,    24,    25,    25,    25,    25,    26,    26,    26,
   26,    27,    27,    27,    27,    28,    28,    28,    28,    29,    29,    29,
   29,    30,    30,    30,    30,    31,    31,    31,    31,    32,    32,    32,
   32,    33,    33,    33,    34,    34,    34,    34,    35,    35,    35,    35,
   36,    36,    36,    36,    37,    37,    37,    37,    38,    38,    38,    38,
   39,    39,    39,    39,    40,    40,    40,    40,    41,    41,    41,    41,
   42,    42,    42,    42,    43,    43,    43,    43,    44,    44,    44,    44,
   45,    45,    45,    46,    46,    46,    46,    47,    47,    47,    47,    48,
   48,    48,    48,    49,    49,    49,    49,    50,    50,    50,    50,    51,
   51,    51,    51,    52,    52,    52,    52,    53,    53,    53,    53,    54,
   54,    54,    54,    55,    55,    55,    55,    56,    56,    56,    56,    57,
   57,    57,    57,    58,    58,    58,    59,    59,    59,    59,    60,    60,
   60,    60,    61,    61,    61,    61,    62,    62,    62,    62,    63,    63,
   63,    63,    64,    64,    64,    64,    65,    65,    65,    65,    66,    66,
   66,    66,    67,    67,    67,    67,    68,    68,    68,    68,    69,    69,
   69,    69,    70,    70,    70,    70,    71,    71,    71,    72,    72,    72,
   72,    73,    73,    73,    73,    74,    74,    74,    74,    75,    75,    75,
   75,    76,    76,    76,    76,    77,    77,    77,    77,    78,    78,    78,
   78,    79,    79,    79,    79,    80,    80,    80,    80,    81,    81,    81,
   81,    82,    82,    82,    82,    83,    83,    83,    83,    84,    84,    84,
   85,    85,    85,    85,    86,    86,    86,    86,    87,    87,    87,    87,
   88,    88,    88,    88,    89,    89,    89,    89,    90,    90,    90,    90,
   91,    91,    91,    91,    92,    92,    92,    92,    93,    93,    93,    93,
   94,    94,    94,    94,    95,    95,    95,    95,    96,    96,    96,    96,
   97,    97,    97,    98,    98,    98,    98,    99,    99,    99,    99,   100,
  100,   100,   100,   101,   101,   101,   101,   102,   102,   102,   102,   103,
  103,   103,   103,   104,   104,   104,   104,   105,   105,   105,   105,   106,
  106,   106,   106,   107,   107,   107,   107,   108,   108,   108,   108,   109,
  109,   109,   110,   110,   110,   110,   111,   111,   111,   111,   112,   112,
  112,   112,   113,   113,   113,   113,   114,   114,   114,   114,   115,   115,
  115,   115,   116,   116,   116,   116,   117,   117,   117,   117,   118,   118,
  118,   118,   119,   119,   119,   119,   120,   120,   120,   120,   121,   121,
  121,   121,   122,   122,   122,   123,   123,   123,   123,   124,   124,   124,
  124,   125,   125,   125,   125,   126,   126,   126,   126,   127,   127,   127,
  127,   128,   128,   128,   128,   129,   129,   129,   130,   130,   130,   130,
  131,   131,   131,   132,   132,   132,   132,   133,   133,   133,   134,   134,
  134,   134,   135,   135,   135,   136,   136,   136,   136,   137,   137,   137,
  138,   138,   138,   138,   139,   139,   139,   140,   140,   140,   140,   141,
  141,   141,   142,   142,   142,   142,   143,   143,   143,   144,   144,   144,
  144,   145,   145,   145,   146,   146,   146,   146,   147,   147,   147,   148,
  148,   148,   148,   149,   149,   149,   150,   150,   150,   151,   151,   151,
  151,   152,   152,   152,   153,   153,   153,   153,   154,   154,   154,   155,
  155,   155,   155,   156,   156,   156,   157,   157,   157,   157,   158,   158,
  158,   159,   159,   159,   159,   160,   160,   160,   161,   161,   161,   161,
  162,   162,   162,   163,   163,   163,   163,   164,   164,   164,   165,   165,
  165,   165,   166,   166,   166,   167,   167,   167,   167,   168,   168,   168,
  169,   169,   169,   169,   170,   170,   170,   171,   171,   171,   172,   172,
  172,   172,   173,   173,   173,   174,   174,   174,   174,   175,   175,   175,
  176,   176,   176,   176,   177,   177,   177,   178,   178,   178,   178,   179,
  179,   179,   180,   180,   180,   180,   181,   181,   181,   182,   182,   182,
  182,   183,   183,   183,   184,   184,   184,   184,   185,   185,   185,   186,
  186,   186,   186,   187,   187,   187,   188,   188,   188,   188,   189,   189,
  189,   190,   190,   190,   190,   191,   191,   191,   192,   192,   192,   192,
  193,   193,   193,   194,   194,   194,   195,   195,   195,   195,   196,   196,
  196,   197,   197,   197,   197,   198,   198,   198,   199,   199,   199,   199,
  200,   200,   200,   201,   201,   201,   201,   202,   202,   202,   203,   203,
  203,   203,   204,   204,   204,   205,   205,   205,   205,   206,   206,   206,
  207,   207,   207,   207,   208,   208,   208,   209,   209,   209,   209,   210,
  210,   210,   211,   211,   211,   211,   212,   212,   212,   213,   213,   213,
  213,   214,   214,   214,   215,   215,   215,   216,   216,   216,   216,   217,
  217,   217,   218,   218,   218,   218,   219,   219,   219,   220,   220,   220,
  220,   221,   221,   221,   222,   222,   222,   222,   223,   223,   223,   224,
  224,   224,   224,   225,   225,   225,   226,   226,   226,   226,   227,   227,
  227,   228,   228,   228,   228,   229,   229,   229,   230,   230,   230,   230,
  231,   231,   231,   232,   232,   232,   232,   233,   233,   233,   234,   234,
  234,   234,   235,   235,   235,   236,   236,   236,   237,   237,   237,   237,
  238,   238,   238,   239,   239,   239,   239,   240,   240,   240,   241,   241,
  241,   241,   242,   242,   242,   243,   243,   243,   243,   244,   244,   244,
  245,   245,   245,   245,   246,   246,   246,   247,   247,   247,   247,   248,
  248,   248,   249,   249,   249,   249,   250,   250,   250,   251,   251,   251,
  251,   252,   252,   252,   253,   253,   253,   253,   254,   254,   254,   255,
  255,   255,   255,   256,   256,   256,   257,   257,   257,   258,   258,   258,
  259,   259,   260,   260,   260,   261,   261,   261,   262,   262,   262,   263,
  263,   264,   264,   264,   265,   265,   265,   266,   266,   266,   267,   267,
  268,   268,   268,   269,   269,   269,   270,   270,   270,   271,   271,   272,
  272,   272,   273,   273,   273,   274,   274,   274,   275,   275,   275,   276,
  276,   277,   277,   277,   278,   278,   278,   279,   279,   279,   280,   280,
  281,   281,   281,   282,   282,   282,   283,   283,   283,   284,   284,   285,
  285,   285,   286,   286,   286,   287,   287,   287,   288,   288,   288,   289,
  289,   290,   290,   290,   291,   291,   291,   292,   292,   292,   293,   293,
  294,   294,   294,   295,   295,   295,   296,   296,   296,   297,   297,   298,
  298,   298,   299,   299,   299,   300,   300,   300,   301,   301,   302,   302,
  302,   303,   303,   303,   304,   304,   304,   305,   305,   305,   306,   306,
  307,   307,   307,   308,   308,   308,   309,   309,   309,   310,   310,   311,
  311,   311,   312,   312,   312,   313,   313,   313,   314,   314,   315,   315,
  315,   316,   316,   316,   317,   317,   317,   318,   318,   319,   319,   319,
  320,   320,   320,   321,   321,   321,   322,   322,   322,   323,   323,   324,
  324,   324,   325,   325,   325,   326,   326,   326,   327,   327,   328,   328,
  328,   329,   329,   329,   330,   330,   330,   331,   331,   332,   332,   332,
  333,   333,   333,   334,   334,   334,   335,   335,   336,   336,   336,   337,
  337,   337,   338,   338,   338,   339,   339,   339,   340,   340,   341,   341,
  341,   342,   342,   342,   343,   343,   343,   344,   344,   345,   345,   345,
  346,   346,   346,   347,   347,   347,   348,   348,   349,   349,   349,   350,
  350,   350,   351,   351,   351,   352,   352,   352,   353,   353,   354,   354,
  354,   355,   355,   355,   356,   356,   356,   357,   357,   358,   358,   358,
  359,   359,   359,   360,   360,   360,   361,   361,   362,   362,   362,   363,
  363,   363,   364,   364,   364,   365,   365,   366,   366,   366,   367,   367,
  367,   368,   368,   368,   369,   369,   369,   370,   370,   371,   371,   371,
  372,   372,   372,   373,   373,   373,   374,   374,   375,   375,   375,   376,
  376,   376,   377,   377,   377,   378,   378,   379,   379,   379,   380,   380,
  380,   381,   381,   381,   382,   382,   383,   383,   383,   384,   384,   384,
  385,   385,   386,   386,   387,   387,   388,   388,   389,   389,   390,   390,
  391,   391,   392,   392,   393,   393,   394,   394,   395,   395,   396,   396,
  397,   397,   398,   398,   399,   399,   400,   400,   401,   401,   402,   402,
  403,   403,   404,   404,   405,   405,   406,   406,   406,   407,   407,   408,
  408,   409,   409,   410,   410,   411,   411,   412,   412,   413,   413,   414,
  414,   415,   415,   416,   416,   417,   417,   418,   418,   419,   419,   420,
  420,   421,   421,   422,   422,   423,   423,   424,   424,   425,   425,   426,
  426,   427,   427,   428,   428,   429,   429,   430,   430,   431,   431,   432,
  432,   433,   433,   434,   434,   435,   435,   436,   436,   437,   437,   438,
  438,   439,   439,   440,   440,   441,   441,   442,   442,   443,   443,   444,
  444,   445,   445,   446,   446,   447,   447,   448,   448,   448,   449,   449,
  450,   450,   451,   451,   452,   452,   453,   453,   454,   454,   455,   455,
  456,   456,   457,   457,   458,   458,   459,   459,   460,   460,   461,   461,
  462,   462,   463,   463,   464,   464,   465,   465,   466,   466,   467,   467,
  468,   468,   469,   469,   470,   470,   471,   471,   472,   472,   473,   473,
  474,   474,   475,   475,   476,   476,   477,   477,   478,   478,   479,   479,
  480,   480,   481,   481,   482,   482,   483,   483,   484,   484,   485,   485,
  486,   486,   487,   487,   488,   488,   489,   489,   490,   490,   491,   491,
  491,   492,   492,   493,   493,   494,   494,   495,   495,   496,   496,   497,
  497,   498,   498,   499,   499,   500,   500,   501,   501,   502,   502,   503,
  503,   504,   504,   505,   505,   506,   506,   507,   507,   508,   508,   509,
  509,   510,   510,   511,   511,   512,   512,   513,   514,   514,   515,   516,
  516,   517,   518,   519,   519,   520,   521,   521,   522,   523,   524,   524,
  525,   526,   527,   527,   528,   529,   529,   530,   531,   532,   532,   533,
  534,   534,   535,   536,   537,   537,   538,   539,   539,   540,   541,   542,
  542,   543,   544,   544,   545,   546,   547,   547,   548,   549,   550,   550,
  551,   552,   552,   553,   554,   555,   555,   556,   557,   557,   558,   559,
  560,   560,   561,   562,   562,   563,   564,   565,   565,   566,   567,   568,
  568,   569,   570,   570,   571,   572,   573,   573,   574,   575,   575,   576,
  577,   578,   578,   579,   580,   580,   581,   582,   583,   583,   584,   585,
  585,   586,   587,   588,   588,   589,   590,   591,   591,   592,   593,   593,
  594,   595,   596,   596,   597,   598,   598,   599,   600,   601,   601,   602,
  603,   603,   604,   605,   606,   606,   607,   608,   608,   609,   610,   611,
  611,   612,   613,   614,   614,   615,   616,   616,   617,   618,   619,   619,
  620,   621,   621,   622,   623,   624,   624,   625,   626,   626,   627,   628,
  629,   629,   630,   631,   632,   632,   633,   634,   634,   635,   636,   637,
  637,   638,   639,   639,   640,   641,   642,   643,   644,   645,   647,   648,
  649,   650,   651,   652,   653,   654,   655,   656,   658,   659,   660,   661,
  662,   663,   664,   665,   666,   668,   669,   670,   671,   672,   673,   674,
  675,   676,   677,   679,   680,   681,   682,   683,   684,   685,   686,   687,
  688,   690,   691,   692,   693,   694,   695,   696,   697,   698,   700,   701,
  702,   703,   704,   705,   706,   707,   708,   709,   711,   712,   713,   714,
  715,   716,   717,   718,   719,   720,   722,   723,   724,   725,   726,   727,
  728,   729,   730,   732,   733,   734,   735,   736,   737,   738,   739,   740,
  741,   743,   744,   745,   746,   747,   748,   749,   750,   751,   752,   754,
  755,   756,   757,   758,   759,   760,   761,   762,   764,   765,   766,   767,
  768,   769,   771,   773,   775,   776,   778,   780,   781,   783,   785,   787,
  788,   790,   792,   794,   795,   797,   799,   800,   802,   804,   806,   807,
  809,   811,   813,   814,   816,   818,   820,   821,   823,   825,   826,   828,
  830,   832,   833,   835,   837,   839,   840,   842,   844,   845,   847,   849,
  851,   852,   854,   856,   858,   859,   861,   863,   864,   866,   868,   870,
  871,   873,   875,   877,   878,   880,   882,   884,   885,   887,   889,   890,
  892,   894,   896,   898,   901,   903,   906,   909,   911,   914,   917,   920,
  922,   925,   928,   931,   933,   936,   939,   941,   944,   947,   950,   952,
  955,   958,   960,   963,   966,   969,   971,   974,   977,   980,   982,   985,
  988,   990,   993,   996,   999,  1001,  1004,  1007,  1010,  1012,  1015,  1018,
 1020,  1023,  1027,  1031,  1036,  1040,  1045,  1050,  1054,  1059,  1063,  1068,
 1072,  1077,  1082,  1086,  1091,  1095,  1100,  1104,  1109,  1114,  1118,  1123,
 1127,  1132,  1136,  1141,  1146,  1150,  1156,  1163,  1170,  1177,  1184,  1192,
 1199,  1206,  1213,  1220,  1227,  1234,  1241,  1248,  1256,  1263,  1270,  1277,
 1286,  1298,  1310,  1321,  1333,  1344,  1356,  1368,  1379,  1391,  1403,  1419,
 1440,  1462,  1483,  1504,  1526,  1552,  1584,  1616,  1648,  1686,  1728,  1771,
 1856,  1984,  2047];
