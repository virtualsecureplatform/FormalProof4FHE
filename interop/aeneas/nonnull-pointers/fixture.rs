#![feature(pattern_type_macro, pattern_types, core_intrinsics)]
#![allow(internal_features)]
pub type NonNullConst = std::pat::pattern_type!(*const u8 is !null);
pub type NonNullMut = std::pat::pattern_type!(*mut u8 is !null);
pub type NonNullSlice = std::pat::pattern_type!(*const [u8] is !null);
pub fn unwrap_const(pointer: NonNullConst) -> *const u8 {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
pub fn unwrap_mut(pointer: NonNullMut) -> *mut u8 {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
pub fn unwrap_slice(pointer: NonNullSlice) -> *const [u8] {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
pub unsafe fn wrap_const(pointer: *const u8) -> NonNullConst {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
pub unsafe fn wrap_mut(pointer: *mut u8) -> NonNullMut {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
pub unsafe fn wrap_slice(pointer: *const [u8]) -> NonNullSlice {
    unsafe { core::intrinsics::transmute_unchecked(pointer) }
}
pub fn original_identity(pointer: core::ptr::NonNull<u8>) -> core::ptr::NonNull<u8> { pointer }
pub fn original_get(pointer: core::ptr::NonNull<u8>) -> *mut u8 { pointer.as_ptr() }
