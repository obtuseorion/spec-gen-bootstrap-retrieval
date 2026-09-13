//! Shape "trait dispatch": the generic `traits::test_get_trait<T: GetTrait>(x: &T)`
//! and `tutorial::use_counter<T: Counter>(cnt: &mut T)` from Phase 1 trait
//! modules, called here at two concrete types each.
use crate::traits::{self, GetTrait};
use crate::tutorial::{self, Counter};

pub struct Celsius(pub u32);
pub struct Label(pub bool);

impl GetTrait for Celsius {
    type W = u32;
    fn get_w(&self) -> u32 {
        self.0
    }
}

impl GetTrait for Label {
    type W = bool;
    fn get_w(&self) -> bool {
        self.0
    }
}

pub fn get_celsius(c: &Celsius) -> u32 {
    traits::test_get_trait(c)
}

pub fn get_label(l: &Label) -> bool {
    traits::test_get_trait(l)
}

pub struct Ticker {
    pub ticks: usize,
}

impl Counter for Ticker {
    fn incr(&mut self) -> usize {
        self.ticks += 2;
        self.ticks
    }
}

pub fn count_usize(n: &mut usize) -> usize {
    tutorial::use_counter(n)
}

pub fn count_ticker(t: &mut Ticker) -> usize {
    tutorial::use_counter(t)
}
