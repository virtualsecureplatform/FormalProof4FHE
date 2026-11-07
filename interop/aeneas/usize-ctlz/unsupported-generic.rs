#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

pub unsafe fn generic<T: Copy>(input: T) -> u32 {
    unsafe { core::intrinsics::ctlz_nonzero(input) }
}
