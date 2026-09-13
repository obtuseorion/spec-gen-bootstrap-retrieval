//! Shape "dead code": a public function and a type that nothing calls or uses.

pub struct Unused {
    pub a: u32,
    pub b: bool,
}

pub fn never_called(x: u32) -> u32 {
    x + 42
}
