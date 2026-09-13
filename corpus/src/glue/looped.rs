//! Shape "loop with cross-module callee": a `while` loop mutating a `Vec`
//! through `&mut` and calling `tutorial::mul2_add1` and `arrays::incr` from
//! inside the loop body. Aeneas emits the loop as a `bump_all_loop` auxiliary.
use crate::arrays;
use crate::tutorial;

pub fn bump_all(v: &mut Vec<u32>) {
    let mut i: usize = 0;
    while i < v.len() {
        let x = tutorial::mul2_add1(v[i]);
        v[i] = x;
        arrays::incr(&mut v[i]);
        i += 1;
    }
}
