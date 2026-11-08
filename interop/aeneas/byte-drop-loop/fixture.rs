pub unsafe fn drop_bytes(data: *mut u8, length: usize) {
    unsafe { core::ptr::drop_in_place(core::ptr::slice_from_raw_parts_mut(data, length)) }
}
pub const BYTE_SIZE: usize = core::mem::size_of::<u8>();
pub const BYTE_ALIGN: usize = core::mem::align_of::<u8>();
