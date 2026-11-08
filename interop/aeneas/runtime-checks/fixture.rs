#![feature(core_intrinsics)]

pub fn checks() -> (bool, bool) {
    (core::intrinsics::ub_checks(), core::intrinsics::overflow_checks())
}

pub fn guarded(input: u32) -> u32 {
    if core::intrinsics::ub_checks() && input == 0 { 17 } else { input }
}
