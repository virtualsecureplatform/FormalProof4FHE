#![feature(core_intrinsics)]
#[repr(u32)]
pub enum Sparse { One = 1, Eight = 8 }
pub struct Wrapper(pub Sparse);
pub fn decode(input: u32) -> Wrapper { unsafe { core::intrinsics::transmute_unchecked(input) } }
