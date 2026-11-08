#![feature(core_intrinsics)]
#![allow(internal_features)]
pub fn wrong(input: u64) -> u32 { core::intrinsics::ctpop(input) }
