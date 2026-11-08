#![feature(core_intrinsics)]
#![allow(internal_features)]
pub fn wrong(input: u32) -> u32 { core::intrinsics::ctpop(input) }
