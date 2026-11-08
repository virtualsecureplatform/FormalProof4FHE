#![feature(pattern_type_macro, pattern_types, core_intrinsics)]
#![allow(internal_features)]
pub type NonNullConst = std::pat::pattern_type!(*const u8 is !null);
pub unsafe fn wrong_base(pointer: *mut u8) -> NonNullConst {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
