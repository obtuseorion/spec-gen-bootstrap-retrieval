//! Chain links c6 and c7 (see `chain`). c7 is the leaf.

pub fn c6(v: &mut u32) {
    *v += 3;
    *v = c7(*v);
}

pub fn c7(x: u32) -> u32 {
    x ^ 1
}
