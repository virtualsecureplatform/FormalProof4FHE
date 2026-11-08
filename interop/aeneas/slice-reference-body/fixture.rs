pub unsafe fn shared_words(data: *const u64, length: usize) -> &'static [u64] {
    unsafe { core::slice::from_raw_parts(data, length) }
}
pub unsafe fn mutable_words(data: *mut u64, length: usize) -> &'static mut [u64] {
    unsafe { core::slice::from_raw_parts_mut(data, length) }
}
pub unsafe fn shared_bytes(data: *const u8, length: usize) -> &'static [u8] {
    unsafe { core::slice::from_raw_parts(data, length) }
}
pub unsafe fn mutable_bytes(data: *mut u8, length: usize) -> &'static mut [u8] {
    unsafe { core::slice::from_raw_parts_mut(data, length) }
}
pub const WORD_SIZE: usize = core::mem::size_of::<u64>();
pub const WORD_ALIGN: usize = core::mem::align_of::<u64>();
pub const BYTE_SIZE: usize = core::mem::size_of::<u8>();
pub const BYTE_ALIGN: usize = core::mem::align_of::<u8>();
