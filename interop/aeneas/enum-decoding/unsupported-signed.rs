#![feature(core_intrinsics)]
#[repr(i32)]
pub enum Signed { Negative = -1, One = 1 }
pub fn decode(input: u32) -> Signed { unsafe { core::intrinsics::transmute_unchecked(input) } }
