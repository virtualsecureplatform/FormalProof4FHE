#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

pub unsafe fn raw_count(input: usize) -> u32 {
    unsafe { core::intrinsics::ctlz_nonzero(input) }
}

pub fn count(input: usize) -> Option<u32> {
    if input == 0 {
        None
    } else {
        Some(unsafe { core::intrinsics::ctlz_nonzero(input) })
    }
}
