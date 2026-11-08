#![feature(core_intrinsics, pattern_type_macro, pattern_types)]
pub type Positive = std::pat::pattern_type!(u64 is 1..=18446744073709551615);
pub fn convert(value: u64) -> Positive { unsafe { core::intrinsics::transmute_unchecked(value) } }
