#![feature(core_intrinsics)]
#![allow(internal_features, dead_code)]

pub unsafe fn raw_leading(input: usize) -> u32 {
    unsafe { core::intrinsics::ctlz_nonzero(input) }
}
pub fn checked_leading(input: usize) -> Option<u32> {
    if input == 0 { None } else { Some(unsafe { core::intrinsics::ctlz_nonzero(input) }) }
}
pub fn population(input: usize) -> u32 { input.count_ones() }
pub fn power_of_two(input: usize) -> bool { input.is_power_of_two() }
