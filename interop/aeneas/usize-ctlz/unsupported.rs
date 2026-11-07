#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

pub unsafe fn unsupported(input: u32) -> u32 {
    unsafe { core::intrinsics::ctlz_nonzero(input) }
}
