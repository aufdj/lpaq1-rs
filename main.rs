use std::{
    io::{Read, Write, BufReader, BufWriter, BufRead, Seek},
    fs::{File, metadata},
    path::Path,
    time::Instant,
    env,
};
    

const MEM: usize = 1 << 23;

// Convenience functions for buffered I/O ---------------------------------------------------------- Convenience functions for buffered I/O
#[derive(PartialEq, Eq)]
enum BufferState {
    NotEmpty,
    Empty,
}

trait BufferedRead {
    fn read_byte(&mut self, input: &mut [u8; 1]);
    fn read_usize(&mut self, input: &mut [u8; 8]);
    fn fill_buffer(&mut self) -> BufferState;
}
impl BufferedRead for BufReader<File> {
    fn read_byte(&mut self, input: &mut [u8; 1]) {
        match self.read(input) {
            Ok(_)  => {},
            Err(e) => { 
                println!("Function read_byte failed."); 
                println!("Error: {}", e);
            },
        };
        if self.buffer().is_empty() { 
            self.consume(self.capacity()); 
            match self.fill_buf() {
                Ok(_)  => {},
                Err(e) => {
                    println!("Function read_byte failed.");
                    println!("Error: {}", e);
                },
            }
        }
    }
    fn read_usize(&mut self, input: &mut [u8; 8]) {
        match self.read(input) {
            Ok(_)  => {},
            Err(e) => { 
                println!("Function read_usize failed."); 
                println!("Error: {}", e);
            },
        };
        if self.buffer().is_empty() { 
            self.consume(self.capacity()); 
            match self.fill_buf() {
                Ok(_)  => {},
                Err(e) => { 
                    println!("Function read_usize failed."); 
                    println!("Error: {}", e);
                },
            }
        }
    }
    fn fill_buffer(&mut self) -> BufferState {
        self.consume(self.capacity());
        match self.fill_buf() {
            Ok(_)  => {},
            Err(e) => { 
                println!("Function fill_buffer failed."); 
                println!("Error: {}", e);
            },
        }
        if self.buffer().is_empty() { 
            return BufferState::Empty; 
        }
        BufferState::NotEmpty
    }
}
trait BufferedWrite {
    fn write_byte(&mut self, output: u8);
    fn write_usize(&mut self, output: usize);
    fn flush_buffer(&mut self);
}
impl BufferedWrite for BufWriter<File> {
    fn write_byte(&mut self, output: u8) {
        match self.write(&[output]) {
            Ok(_)  => {},
            Err(e) => { 
                println!("Function write_byte failed."); 
                println!("Error: {}", e);
            },
        }
        if self.buffer().len() >= self.capacity() { 
            match self.flush() {
                Ok(_)  => {},
                Err(e) => { 
                    println!("Function write_byte failed."); 
                    println!("Error: {}", e);
                },
            } 
        }
    }
    fn write_usize(&mut self, output: usize) {
        match self.write(&output.to_le_bytes()[..]) {
            Ok(_)  => {},
            Err(e) => { 
                println!("Function write_usize failed."); 
                println!("Error: {}", e);
            },
        }
        if self.buffer().len() >= self.capacity() { 
            match self.flush() {
                Ok(_)  => {},
                Err(e) => { 
                    println!("Function write_usize failed."); 
                    println!("Error: {}", e);
                },
            } 
        }
    }
    fn flush_buffer(&mut self) {
        match self.flush() {
            Ok(_)  => {},
            Err(e) => { 
                println!("Function flush_buffer failed."); 
                println!("Error: {}", e);
            },
        }    
    }
}
fn new_input_file(capacity: usize, file_name: &str) -> BufReader<File> {
    BufReader::with_capacity(capacity, File::open(file_name).unwrap())
}
fn new_output_file(capacity: usize, file_name: &str) -> BufWriter<File> {
    BufWriter::with_capacity(capacity, File::create(file_name).unwrap())
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// Logistic Functions -------------------------------------------------------------------------------------------------- Logistic Functions
fn squash(d: i32) -> i32 {
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
struct Stretch {
    stretch_table: [i16; 4096],
}
impl Stretch {
    fn new() -> Stretch {
        let mut st = Stretch {
            stretch_table: [0; 4096],
        };
        let mut pi = 0;
        for x in -2047..=2047 {
            let i = squash(x);
            for j in pi..=i {
                st.stretch_table[j as usize] = x as i16;
            }
            pi = i + 1;
        }
        st.stretch_table[4095] = 2047;
        st
    }
    fn stretch(&self, p: i32) -> i32 {
        assert!(p < 4096);
        self.stretch_table[p as usize] as i32
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// Adaptive Probability Map -------------------------------------------------------------------------------------- Adaptive Probability Map
struct Apm {
    s:         Stretch,
    bin:       usize,    
    num_cxts:  usize, 
    bin_map:   Vec<u16>, 
}
impl Apm {
    fn new(n: usize) -> Apm {
        let mut apm = Apm {  
            s:         Stretch::new(), 
            bin:       0, 
            num_cxts:  n,
            bin_map:   vec![0; n * 33],
        };
        for cxt in 0..apm.num_cxts {
            for bin in 0usize..33 {
                apm.bin_map[(cxt*33)+bin] = 
                if cxt == 0 {
                    (squash(((bin as i32) - 16) * 128) * 16) as u16
                } 
                else {
                    apm.bin_map[bin]
                }
            }
        }
        apm
    }
    fn p(&mut self, bit: i32, rate: i32, mut pr: i32, cxt: u32) -> i32 {
        assert!(bit == 0 || bit == 1 && pr >= 0 && pr < 4096);
        assert!(cxt < self.num_cxts as u32);
        self.update(bit, rate);
        
        pr = self.s.stretch(pr); // -2047 to 2047
        let i_w = pr & 127;      // Interpolation weight (33 points)
        
        self.bin = (((pr + 2048) >> 7) + ((cxt as i32) * 33)) as usize;

        let a = self.bin_map[self.bin] as i32;
        let b = self.bin_map[self.bin+1] as i32;
        ((a * (128 - i_w)) + (b * i_w)) >> 11
    }
    fn update(&mut self, bit: i32, rate: i32) {
        assert!(bit == 0 || bit == 1 && rate > 0 && rate < 32);
        
        // g controls direction of update (bit = 1: increase, bit = 0: decrease)
        let g: i32 = (bit << 16) + (bit << rate) - bit - bit;
        let a = self.bin_map[self.bin] as i32;
        let b = self.bin_map[self.bin+1] as i32;
        self.bin_map[self.bin]   = (a + ((g - a) >> rate)) as u16;
        self.bin_map[self.bin+1] = (b + ((g - b) >> rate)) as u16;
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// State Map -------------------------------------------------------------------------------------------------------------------- State Map
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

fn next_state(state: u8, bit: i32) -> u8 {
    STATE_TABLE[state as usize][bit as usize]
}

#[allow(overflowing_literals)]
const HI_22_MSK: i32 = 0xFFFFFC00; // High 22 bit mask
const LIMIT: usize = 127; // Controls rate of adaptation (higher = slower) (0..1024)

struct StateMap {
    cxt:      usize,       // Context of last prediction
    cxt_map:  Vec<u32>,    // Maps a context to a prediction and a count 
    rec_t:    [i32; 1024], // Reciprocal table: controls the size of each adjustment to cxt_map
}
impl StateMap {
    fn new(n: usize) -> StateMap {
        let mut sm = StateMap { 
            cxt:      0,
            cxt_map:  vec![1 << 31; n],
            rec_t:    [0; 1024],
        };
        for i in 0..1024 { 
            sm.rec_t[i] = (16_384 / (i + i + 3)) as i32; 
        }
        sm
    }
    fn p(&mut self, bit: i32, cxt: i32) -> i32 {
        assert!(bit == 0 || bit == 1);
        self.update(bit);                      
        self.cxt = cxt as usize;
        (self.cxt_map[self.cxt] >> 20) as i32  
    }
    fn update(&mut self, bit: i32) {
        let count = (self.cxt_map[self.cxt] & 1023) as usize; // Low 10 bits
        let pr    = (self.cxt_map[self.cxt] >> 10 ) as i32;   // High 22 bits

        if count < LIMIT { self.cxt_map[self.cxt] += 1; }

        // Update cxt_map based on prediction error
        self.cxt_map[self.cxt] = self.cxt_map[self.cxt].wrapping_add(
        ((((bit << 22) - pr) >> 3) * self.rec_t[count] & HI_22_MSK) as u32); 
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// Mixer ---------------------------------------------------------------------------------------------------------------------------- Mixer
fn train(inputs: &[i32], weights: &mut [i32], error: i32) {
    for (input, weight) in inputs.iter().zip(weights.iter_mut()) {
        *weight += ((*input * error) + 0x8000) >> 16;
    }
}
fn dot_product(inputs: &[i32], weights: &[i32]) -> i32 {
    (inputs.iter().zip(weights.iter())
    .map(|(i, w)| i * w).sum::<i32>()) >> 8
}

struct Mixer {
    max_in:   usize,
    inputs:   Vec<i32>,
    weights:  Vec<i32>,
    cxt:      usize,
    pr:       i32,
}
impl Mixer {
    fn new(n: usize, m: usize) -> Mixer {
        Mixer {
            max_in:   n,
            inputs:   Vec::with_capacity(n),
            weights:  vec![0; n * m],
            cxt:      0,
            pr:       2048,
        }
    }
    fn add(&mut self, pr: i32) {
        assert!(self.inputs.len() < self.inputs.capacity());
        self.inputs.push(pr);
    }
    fn set(&mut self, cxt: u32) {
        self.cxt = cxt as usize;
    }
    fn p(&mut self) -> i32 {
        let d = dot_product(&self.inputs[..], &self.weights[self.cxt*self.max_in..]);
        self.pr = squash(d >> 8);
        self.pr
    }
    fn update(&mut self, bit: i32) {
        let error: i32 = ((bit << 12) - self.pr) * 7;
        assert!(error >= -32768 && error < 32768);
        train(&self.inputs[..], &mut self.weights[self.cxt*self.max_in..], error);
        self.inputs.clear();
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// Match Model ---------------------------------------------------------------------------------------------------------------- Match Model
const BUF_END: usize = (MEM / 2) - 1;
const HT_END:  usize = (MEM / 8) - 1;
const MAX_LEN: usize = 62;

struct MatchModel {
    mch_ptr:  usize,    hash_s:   usize,
    mch_len:  usize,    hash_l:   usize,
    cxt:      usize,    buf_pos:  usize,  
    bits:     usize,    s:        Stretch,                 
    sm:       StateMap,
    buf:      Vec<u8>,
    ht:       Vec<u32>,
}
impl MatchModel {
    fn new() -> MatchModel {
        MatchModel {
            mch_ptr:  0,    hash_s:   0,
            mch_len:  0,    hash_l:   0,
            cxt:      1,    buf_pos:  0,     
            bits:     0,    s:        Stretch::new(),
            sm:       StateMap::new(56 << 8),     
            buf:      vec![0; BUF_END + 1],
            ht:       vec![0;  HT_END + 1],
        }
    }
    fn find_or_extend_match(&mut self, hash: usize) {
        self.mch_ptr = self.ht[hash] as usize; 
        if self.mch_ptr != self.buf_pos {               
            let mut i = self.mch_ptr - self.mch_len - 1 & BUF_END;

            while i != self.buf_pos  
            && self.mch_len < MAX_LEN  
            && self.buf[i] == self.buf[self.buf_pos-self.mch_len-1 & BUF_END] 
            {
                self.mch_len += 1;
                i = self.mch_ptr - self.mch_len - 1 & BUF_END;
            }
        }
    }
    fn p(&mut self, bit: i32, mxr: &mut Mixer) -> usize { 
        self.cxt += self.cxt + bit as usize;
        self.bits += 1;
        if self.bits == 8 {
            self.bits = 0;
            self.hash_s = self.hash_s * (3 << 3) + self.cxt & HT_END;
            self.hash_l = self.hash_l * (5 << 5) + self.cxt & HT_END;
            self.buf[self.buf_pos] = self.cxt as u8;
            self.buf_pos += 1;
            self.cxt = 1;
            self.buf_pos &= BUF_END;

            if self.mch_len > 0 {
                self.mch_ptr += 1;
                self.mch_ptr &= BUF_END;
                if self.mch_len < MAX_LEN { self.mch_len += 1; }
            } 
            else {
                self.find_or_extend_match(self.hash_s);
            }

            if self.mch_len < 2 {
                self.mch_len = 0;
                self.find_or_extend_match(self.hash_l);
            }
        }

        // Predict -----
        let mut cxt = self.cxt;
        if self.mch_len > 0 
        && (self.buf[self.mch_ptr] as usize) + 256 >> 8 - self.bits == cxt {
            let b = (self.buf[self.mch_ptr] >> 7 - self.bits & 1) as usize;
            if self.mch_len < 16 { 
                cxt = self.mch_len * 2 + b; 
            } 
            else { 
                cxt = (self.mch_len >> 2) * 2 + b + 24; 
            }
            cxt = cxt * 256 + self.buf[self.buf_pos-1 & BUF_END] as usize;
        } 
        else {
            self.mch_len = 0;
        }
        // -------------
        let pr = self.s.stretch(self.sm.p(bit, cxt as i32));
        mxr.add(pr);

        // Update index
        if self.bits == 0 {
            self.ht[self.hash_s] = self.buf_pos as u32;
            self.ht[self.hash_l] = self.buf_pos as u32;
        }
        // -------------
        self.mch_len
    }
} 
// ----------------------------------------------------------------------------------------------------------------------------------------


// Hash Table ------------------------------------------------------------------------------------------------------------------ Hash Table
const B: usize = 16;

struct HashTable {
    t:     Vec<u8>,
    size:  usize,
}
impl HashTable {
    fn new(n: usize) -> HashTable {
        assert!(B >= 2       && B.is_power_of_two());
        assert!(n >= (B * 4) && n.is_power_of_two());
        HashTable {
            t:     vec![0; n],
            size:  n,
        }
    }
    fn hash(&mut self, mut i: u32) -> *mut u8 {
        i = i.wrapping_mul(123456791).rotate_right(16).wrapping_mul(234567891);
        let chksum = (i >> 24) as u8;
        let mut i = i as usize; // Convert to usize for indexing
        i = (i * B) & (self.size - B); // Restrict i to valid ht index
        if self.t[i]     == chksum { return &mut self.t[i];     }
        if self.t[i^B]   == chksum { return &mut self.t[i^B];   }
        if self.t[i^B*2] == chksum { return &mut self.t[i^B*2]; }
        if self.t[i+1] > self.t[i+1^B]
        || self.t[i+1] > self.t[i+1^B*2] { i ^= B; }
        if self.t[i+1] > self.t[i+1^B^B*2] { i ^= B ^ (B * 2); }
        for x in self.t[i..i+B].iter_mut() {
            *x = 0;
        }
        self.t[i] = chksum;
        &mut self.t[i]
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// Predictor -------------------------------------------------------------------------------------------------------------------- Predictor
struct Predictor {
    cxt:   u32,            mm:    MatchModel,    
    cxt4:  u32,            ht:    HashTable, 
    bits:  usize,          apm1:  Apm,            
    pr:    i32,            apm2:  Apm,  
    h:     [u32; 6],       sm0:   StateMap,              
    sp:    [*mut u8; 6],   sm1:   StateMap,
    t0:    [u8; 65_536],   sm2:   StateMap,
    mxr:   Mixer,          sm3:   StateMap,
    s:     Stretch,        sm4:   StateMap,
                           sm5:   StateMap,     
}
impl Predictor {
    fn new() -> Predictor {
        let mut p = Predictor {
            cxt:   1,                   mm:    MatchModel::new(),           
            cxt4:  0,                   ht:    HashTable::new(MEM*2),    
            bits:  0,                   apm1:  Apm::new(256), 
            pr:    2048,                apm2:  Apm::new(16384), 
            h:     [0; 6],              sm0:   StateMap::new(256),
            sp:    [&mut 0; 6],         sm1:   StateMap::new(256),
            t0:    [0; 65_536],         sm2:   StateMap::new(256),
            mxr:   Mixer::new(7, 80),   sm3:   StateMap::new(256),
            s:     Stretch::new(),      sm4:   StateMap::new(256),
                                        sm5:   StateMap::new(256),  
        };
        for i in 0..6 {
            p.sp[i] = &mut p.t0[0];
        }
        p
    }
    fn p(&mut self) -> i32 { 
        assert!(self.pr >= 0 && self.pr < 4096);
        self.pr 
    } 
    fn update_sp(&mut self, cxt: [u32; 6], nibble: u32) {
        unsafe { 
            self.sp[1] = self.ht.hash(cxt[1]+nibble).add(1);
            self.sp[2] = self.ht.hash(cxt[2]+nibble).add(1);
            self.sp[3] = self.ht.hash(cxt[3]+nibble).add(1);
            self.sp[4] = self.ht.hash(cxt[4]+nibble).add(1);
            self.sp[5] = self.ht.hash(cxt[5]+nibble).add(1);
        }
    }
    fn update(&mut self, bit: i32) {
        assert!(bit == 0 || bit == 1);
        unsafe { 
        *self.sp[0] = next_state(*self.sp[0], bit);
        *self.sp[1] = next_state(*self.sp[1], bit);
        *self.sp[2] = next_state(*self.sp[2], bit);
        *self.sp[3] = next_state(*self.sp[3], bit);
        *self.sp[4] = next_state(*self.sp[4], bit);
        *self.sp[5] = next_state(*self.sp[5], bit);
        }
        self.mxr.update(bit);

        self.cxt += self.cxt + bit as u32;
        self.bits += 1;
        if self.cxt >= 256 {
            self.cxt -= 256;
            self.cxt4 = (self.cxt4 << 8) | self.cxt;  
            self.h[0] =  self.cxt << 8;                         // Order 1
            self.h[1] = (self.cxt4 & 0xFFFF) << 5 | 0x57000000; // Order 2
            self.h[2] = (self.cxt4 << 8).wrapping_mul(3);       // Order 3
            self.h[3] =  self.cxt4.wrapping_mul(5);             // Order 4
            self.h[4] =  self.h[4].wrapping_mul(11 << 5)        // Order 6
                         + self.cxt * 13 & 0x3FFFFFFF;
            
            match self.cxt { // Unigram Word Order
                65..=90 => {
                    self.cxt += 32; // Fold to lowercase
                    self.h[5] = (self.h[5] + self.cxt).wrapping_mul(7 << 3);
                }
                97..=122 => {
                    self.h[5] = (self.h[5] + self.cxt).wrapping_mul(7 << 3);
                },
                _ => self.h[5] = 0,
            }

            self.update_sp(self.h, 0);
            self.cxt = 1;
            self.bits = 0;
        }
        if self.bits == 4 {
            self.update_sp(self.h, self.cxt);
        }
        else if self.bits > 0 {
            let j = ((bit as usize) + 1) << (self.bits & 3) - 1;
            unsafe { 
            self.sp[1] = self.sp[1].add(j);
            self.sp[2] = self.sp[2].add(j);
            self.sp[3] = self.sp[3].add(j);
            self.sp[4] = self.sp[4].add(j);
            self.sp[5] = self.sp[5].add(j);
            }
        }
        unsafe { 
        self.sp[0] = ((&mut self.t0[0] as *mut u8)
                     .add(self.h[0] as usize))
                     .add(self.cxt as usize);
        }
        
        let len = self.mm.p(bit, &mut self.mxr);
        let mut order: u32 = 0;
        if len == 0 {
            unsafe { 
            if *self.sp[4] != 0 { order += 1; }
            if *self.sp[3] != 0 { order += 1; }
            if *self.sp[2] != 0 { order += 1; }
            if *self.sp[1] != 0 { order += 1; }
            }
        }
        else {
            order = 5 +
            if len >= 8  { 1 } else { 0 } +
            if len >= 12 { 1 } else { 0 } +
            if len >= 16 { 1 } else { 0 } +
            if len >= 32 { 1 } else { 0 };
        }
        
        unsafe { 
        self.mxr.add(self.s.stretch(self.sm0.p(bit, *self.sp[0] as i32)));
        self.mxr.add(self.s.stretch(self.sm1.p(bit, *self.sp[1] as i32)));
        self.mxr.add(self.s.stretch(self.sm2.p(bit, *self.sp[2] as i32)));
        self.mxr.add(self.s.stretch(self.sm3.p(bit, *self.sp[3] as i32)));
        self.mxr.add(self.s.stretch(self.sm4.p(bit, *self.sp[4] as i32)));
        self.mxr.add(self.s.stretch(self.sm5.p(bit, *self.sp[5] as i32)));
        }
        self.mxr.set(order + 10 * (self.h[0] >> 13));
        self.pr = self.mxr.p();
        self.pr = self.pr + 3 * self.apm1.p(bit, 7, self.pr, self.cxt) >> 2;
        self.pr = self.pr + 3 * self.apm2.p(bit, 7, self.pr, self.cxt ^ self.h[0] >> 2) >> 2;
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


// Encoder ------------------------------------------------------------------------------------------------------------------------ Encoder
#[derive(PartialEq, Eq)]
enum Mode {
    Compress,
    Decompress,
}

struct Encoder {
    high:       u32,
    low:        u32,
    predictor:  Predictor,
    file_in:    BufReader<File>,
    file_out:   BufWriter<File>,
    x:          u32,
    mode:       Mode,  
}
impl Encoder {
    fn new(file_in: BufReader<File>, file_out: BufWriter<File>, mode: Mode) -> Encoder {
        let mut enc = Encoder {
            high: 0xFFFFFFFF, 
            low: 0, 
            x: 0, 
            predictor: Predictor::new(), 
            file_in, file_out, mode,
        };  
        if enc.mode == Mode::Compress {
            enc.file_out.write_usize(0);
            enc.file_out.write_usize(0);
            enc.file_out.write_usize(0);
        } 
        enc
    }
    fn compress_bit(&mut self, bit: i32) {
        let mut p = self.predictor.p() as u32;
        if p < 2048 { p += 1; } 

        let mid: u32 = self.low + ((self.high - self.low) >> 12) * p 
                       + ((self.high - self.low & 0x0FFF) * p >> 12);
                       
        if bit == 1 {
            self.high = mid;
        } 
        else {
            self.low = mid + 1;
        }
        self.predictor.update(bit);
        
        while ( (self.high ^ self.low) & 0xFF000000) == 0 {
            self.file_out.write_byte((self.high >> 24) as u8);
            self.high = (self.high << 8) + 255;
            self.low <<= 8;  
        }
    }
    fn decompress_bit(&mut self) -> i32 {
        let mut byte = [0u8; 1];
        let mut p = self.predictor.p() as u32;
        if p < 2048 { p += 1; }   

        let mid: u32 = self.low + ((self.high - self.low) >> 12) * p 
                       + ((self.high - self.low & 0x0FFF) * p >> 12);

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
            self.file_in.read_byte(&mut byte); 
            self.x = (self.x << 8) + byte[0] as u32; 
        }
        bit
    }
    fn flush(&mut self) {
        while ( (self.high ^ self.low) & 0xFF000000) == 0 {
            self.file_out.write_byte((self.high >> 24) as u8);
            self.high = (self.high << 8) + 255;
            self.low <<= 8; 
        }
        self.file_out.write_byte((self.high >> 24) as u8);
        self.file_out.flush_buffer();
    }

    fn compress_block(&mut self, block: &[u8]) {
        for byte in block.iter() {
            for i in (0..=7).rev() {
                self.compress_bit(((*byte >> i) & 1) as i32);
            }   
        }
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

    // Write 24 byte block data header
    fn write_block_data(&mut self, final_block_size: usize, block_size: usize, num_blocks: usize) {
        self.file_out.get_ref().rewind().unwrap();
        self.file_out.write_usize(final_block_size);
        self.file_out.write_usize(block_size);
        self.file_out.write_usize(num_blocks);    
    }
    // Read 24 byte block data header
    fn read_block_data(&mut self) -> (usize, usize, usize) {
        let mut final_block_size = [0u8; 8];
        let mut block_size = [0u8; 8];
        let mut num_blocks = [0u8; 8];
        self.file_in.read_usize(&mut final_block_size);
        self.file_in.read_usize(&mut block_size);
        self.file_in.read_usize(&mut num_blocks);
        (usize::from_le_bytes(final_block_size), 
         usize::from_le_bytes(block_size),
         usize::from_le_bytes(num_blocks)) 
    }

    fn init_x(&mut self) {
        assert!(self.mode == Mode::Decompress);
        let mut byte = [0u8; 1];
        for _ in 0..4 {
            self.file_in.read_byte(&mut byte);
            self.x = (self.x << 8) + byte[0] as u32;
        }
    }
}
// ----------------------------------------------------------------------------------------------------------------------------------------


fn main() {
    let start_time = Instant::now();
    let args: Vec<String> = env::args().collect();

    let e_file_in  = new_input_file(4096, &args[2]);
    let e_file_out = new_output_file(4096, &args[3]);

    match (&args[1]).as_str() {
        "c" => {  
            let block_size = 1 << 20;
            let mut final_block_size = 0;
            let mut num_blocks = 0;

            let mut file_in = new_input_file(block_size, &args[2]);
            let mut enc = Encoder::new(e_file_in, e_file_out, Mode::Compress);

            // Compress ---------------------------------------------------
            loop {
                if file_in.fill_buffer() == BufferState::Empty { break; }
                final_block_size = file_in.buffer().len();
                enc.compress_block(&file_in.buffer());
                num_blocks += 1;
            } 
            // ------------------------------------------------------------
            enc.flush();
            enc.write_block_data(final_block_size, block_size, num_blocks);
            println!("Finished Compressing.");
        }
        "d" => {
            let mut file_out = new_output_file(4096, &args[3]);
            let mut dec = Encoder::new(e_file_in, e_file_out, Mode::Decompress);

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
    let file_in_size  = metadata(Path::new(&args[2])).unwrap().len();
    let file_out_size = metadata(Path::new(&args[3])).unwrap().len();   
    println!("{} bytes -> {} bytes in {:.2?}", 
    file_in_size, file_out_size, start_time.elapsed());  
}


