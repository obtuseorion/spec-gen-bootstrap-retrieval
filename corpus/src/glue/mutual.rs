//! Shape "mutual recursion": `is_even`/`is_odd` on u32, and a size count over a
//! pair of mutually recursive enums `Tree`/`Forest`.

pub fn is_even(n: u32) -> bool {
    if n == 0 { true } else { is_odd(n - 1) }
}

pub fn is_odd(n: u32) -> bool {
    if n == 0 { false } else { is_even(n - 1) }
}

pub enum Tree {
    Leaf(u32),
    Node(u32, Box<Forest>),
}

pub enum Forest {
    Nil,
    Cons(Box<Tree>, Box<Forest>),
}

pub fn tree_size(t: &Tree) -> u32 {
    match t {
        Tree::Leaf(_) => 1,
        Tree::Node(_, f) => 1 + forest_size(f),
    }
}

pub fn forest_size(f: &Forest) -> u32 {
    match f {
        Forest::Nil => 0,
        Forest::Cons(t, rest) => tree_size(t) + forest_size(rest),
    }
}
