//! Shape "chain": c0 → c1 → c2 → c3 → c4 → c5 → c6 → c7, each calling exactly
//! the next. c0,c1 live here; c2,c3 in `chain_mid`; c4,c5 in `chain_end`;
//! c6,c7 in `chain_tail`, so the links c1→c2, c3→c4 and c5→c6 cross module
//! boundaries. Links c1→c2 and c5→c6 pass a `&mut u32` that the callee modifies.
use super::chain_mid::c2;

pub fn c0(x: u32) -> u32 {
    let mut v = x;
    c1(&mut v);
    v
}

pub fn c1(v: &mut u32) {
    *v = *v % 1000;
    c2(v)
}
