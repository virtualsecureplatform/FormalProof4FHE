pub unsafe fn shared_scope(data: *const u8, length: usize) {
    let _slice = unsafe { core::slice::from_raw_parts(data, length) };
}
pub unsafe fn mutable_scope(data: *mut u8, length: usize) {
    let _slice = unsafe { core::slice::from_raw_parts_mut(data, length) };
}
pub const BYTE_SIZE: usize = core::mem::size_of::<u8>();
pub const BYTE_ALIGN: usize = core::mem::align_of::<u8>();
