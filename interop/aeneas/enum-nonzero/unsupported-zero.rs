#![feature(core_intrinsics)]
#[repr(u64)]
pub enum HasZero { Zero = 0, One = 1 }
#[repr(transparent)]
pub struct Input(pub HasZero);
pub fn convert(value: Input) -> core::num::NonZeroU64 { unsafe { core::intrinsics::transmute_unchecked(value) } }
