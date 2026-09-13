//! Chain links c4 and c5 (see `chain`).
use super::chain_tail::c6;

pub fn c4(x: u32) -> u32 {
    let mut v = x;
    c5(&mut v);
    v
}

pub fn c5(v: &mut u32) {
    *v = *v * 2;
    c6(v)
}
