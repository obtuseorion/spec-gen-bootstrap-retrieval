//! Shape "wide fan-out": `hub` calls 14 distinct helpers from 5 Phase 1
//! modules (bitwise, tutorial, no_nested_borrows, loops, paper).
use crate::bitwise;
use crate::loops;
use crate::no_nested_borrows;
use crate::paper;
use crate::tutorial;

pub fn hub(x: u32) -> u32 {
    let small = x % 8;
    let a = bitwise::shift_u32(small);
    let b = bitwise::xor_u32(a, small);
    let c = bitwise::or_u32(b, 1);
    let d = bitwise::and_u32(c, 0xFF);
    let e = tutorial::mul2_add1(d);
    let f = tutorial::mul2_add1_add(e, small);
    let g = no_nested_borrows::get_max(f, e);
    let h = loops::sum(small);
    let i = loops::iter(small);
    let mut acc: i32 = no_nested_borrows::cast_u32_to_i32(small);
    paper::ref_incr(&mut acc);
    let j = no_nested_borrows::copy_int(acc);
    let parity = if tutorial::even(small) { 1 } else { 0 };
    let parity2 = if tutorial::odd(small) { 1 } else { 0 };
    g + h + i + (j as u32) + parity + parity2
}
