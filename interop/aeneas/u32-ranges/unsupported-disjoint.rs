#![feature(pattern_type_macro, pattern_types)]
pub type Disjoint = std::pat::pattern_type!(i32 is ..=-1 | 1..);
pub fn identity(value: Disjoint) -> Disjoint {
    value
}
