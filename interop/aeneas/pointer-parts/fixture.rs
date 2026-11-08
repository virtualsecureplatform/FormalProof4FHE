#![feature(ptr_metadata)]
pub fn slice_const(pointer: *const u8, length: usize) -> *const [u8] {
    core::ptr::from_raw_parts(pointer, length)
}
pub fn slice_mut(pointer: *mut u8, length: usize) -> *mut [u8] {
    core::ptr::from_raw_parts_mut(pointer, length)
}
pub fn slice_const_from_mut(pointer: *mut u8, length: usize) -> *const [u8] {
    core::ptr::from_raw_parts(pointer, length)
}
pub fn thin_const(pointer: *const u8) -> *const u64 {
    core::ptr::from_raw_parts(pointer, ())
}
pub fn thin_mut(pointer: *mut u8) -> *mut u64 {
    core::ptr::from_raw_parts_mut(pointer, ())
}
pub fn str_const(pointer: *const u8, bytes: usize) -> *const str {
    core::ptr::from_raw_parts(pointer, bytes)
}
#[repr(C)]
pub struct Pair { pub tag: u8, pub word: u64 }
pub fn pair_const(pointer: *const u8) -> *const Pair {
    core::ptr::from_raw_parts(pointer, ())
}
