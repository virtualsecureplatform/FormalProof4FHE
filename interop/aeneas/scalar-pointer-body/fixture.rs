pub unsafe fn read_word(source: *const u64) -> u64 {
    unsafe { core::ptr::read(source) }
}
pub unsafe fn write_word(target: *mut u64, value: u64) {
    unsafe { core::ptr::write(target, value) }
}
pub unsafe fn replace_word(target: *mut u64, value: u64) -> u64 {
    let previous = unsafe { core::ptr::read(target) };
    unsafe { core::ptr::write(target, value) };
    previous
}
pub unsafe fn read_pointer(source: *const *mut u64) -> *mut u64 {
    unsafe { core::ptr::read(source) }
}
pub unsafe fn write_pointer(target: *mut *mut u64, value: *mut u64) {
    unsafe { core::ptr::write(target, value) }
}
pub const WORD_SIZE: usize = core::mem::size_of::<u64>();
pub const WORD_ALIGN: usize = core::mem::align_of::<u64>();
pub const PTR_SIZE: usize = core::mem::size_of::<*mut u64>();
pub const PTR_ALIGN: usize = core::mem::align_of::<*mut u64>();
