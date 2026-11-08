#![feature(pattern_type_macro, pattern_types)]
pub type Window = std::pat::pattern_type!(u64 is 7..=19);
pub fn preserve(value: Window) -> Window { value }
