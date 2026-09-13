//! Chain links c2 and c3 (see `chain`).
use super::chain_end::c4;

pub fn c2(v: &mut u32) {
    *v += 1;
    let w = c3(*v);
    *v = w;
}

pub fn c3(x: u32) -> u32 {
    c4(x) + 1
}
