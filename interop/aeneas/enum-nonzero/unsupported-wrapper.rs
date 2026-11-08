#![feature(core_intrinsics)]
#[repr(u64)]
pub enum Positive { One = 1, Two = 2 }
pub struct Output(pub core::num::NonZeroU64);
pub fn convert(value: Positive) -> Output { unsafe { core::intrinsics::transmute_unchecked(value) } }
