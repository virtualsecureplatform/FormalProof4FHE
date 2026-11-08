#![feature(pattern_type_macro, pattern_types, core_intrinsics)]
pub type NoHighBit = std::pat::pattern_type!(usize is 0..=9223372036854775807);
pub type Window = std::pat::pattern_type!(u32 is 7..=19);
#[repr(transparent)]
pub struct Capacity(pub NoHighBit);
#[repr(transparent)]
pub struct Small(pub Window);
pub fn capacity(value: Capacity) -> usize { unsafe { core::intrinsics::transmute_unchecked(value) } }
pub fn small(value: Small) -> u32 { unsafe { core::intrinsics::transmute_unchecked(value) } }
pub fn direct(value: NoHighBit) -> usize { unsafe { core::intrinsics::transmute_unchecked(value) } }
