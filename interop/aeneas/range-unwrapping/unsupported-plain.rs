#![feature(core_intrinsics)]
#[repr(transparent)]
pub struct Wrapper(pub usize);
pub fn unwrap(value: Wrapper) -> usize { unsafe { core::intrinsics::transmute_unchecked(value) } }
