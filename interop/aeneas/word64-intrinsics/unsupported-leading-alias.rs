#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

pub unsafe fn alias(input: u32) -> u32 {
    let operation = core::intrinsics::ctlz_nonzero::<u32>;
    unsafe { operation(input) }
}
