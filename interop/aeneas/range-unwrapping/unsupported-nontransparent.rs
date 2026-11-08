#![feature(pattern_type_macro, pattern_types, core_intrinsics)]
pub type Bounded = std::pat::pattern_type!(usize is 0..=19);
pub struct Wrapper(pub Bounded);
pub fn unwrap(value: Wrapper) -> usize { unsafe { core::intrinsics::transmute_unchecked(value) } }
