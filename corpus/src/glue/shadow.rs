//! Shape "name shadowing": `arrays::incr` and `tutorial::incr` have the same
//! name and signature (`fn incr(x: &mut u32)`); both are called from here.
//! Likewise `tutorial::choose` and `no_nested_borrows::choose`.
use crate::arrays;
use crate::no_nested_borrows;
use crate::tutorial;

pub fn incr_twice(x: &mut u32) {
    arrays::incr(x);
    tutorial::incr(x);
}

pub fn choose_both(b: bool, x: u32, y: u32) -> u32 {
    let mut a = x;
    let mut c = y;
    *tutorial::choose(b, &mut a, &mut c) += 1;
    *no_nested_borrows::choose(!b, &mut a, &mut c) += 10;
    a + c
}
