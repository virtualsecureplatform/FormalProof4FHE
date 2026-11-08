#![feature(pattern_type_macro, pattern_types)]
pub type Signed = std::pat::pattern_type!(i32 is -3..=3);
pub fn identity(value: Signed) -> Signed {
    value
}
