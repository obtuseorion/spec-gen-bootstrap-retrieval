//! Shape "diamond": `top` calls `left` and `right`; both call `shared`.
//! `left` relies on `shared(x) <= x` (so the subtraction cannot underflow);
//! `right` relies on `shared(x)` being even (so halving is exact).

/// Rounds down to the nearest even number: result ≤ input and result is even.
pub fn shared(x: u32) -> u32 {
    (x / 2) * 2
}

/// Needs "shared(x) ≤ x".
pub fn left(x: u32) -> u32 {
    let y = shared(x);
    assert!(y <= x);
    x - y
}

/// Needs "shared(x) is even".
pub fn right(x: u32) -> u32 {
    let y = shared(x);
    assert!(y % 2 == 0);
    y / 2
}

pub fn top(x: u32) -> u32 {
    left(x) + right(x)
}
