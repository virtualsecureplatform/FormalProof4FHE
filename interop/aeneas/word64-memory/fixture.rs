pub fn shared_words(data: *const u64, length: usize) -> *const [u64] {
    core::ptr::slice_from_raw_parts(data, length)
}
pub fn mutable_words(data: *mut u64, length: usize) -> *mut [u64] {
    core::ptr::slice_from_raw_parts_mut(data, length)
}
pub const WORD_SIZE: usize = core::mem::size_of::<u64>();
pub const WORD_ALIGN: usize = core::mem::align_of::<u64>();
pub fn word_layout() -> (usize, usize) { (WORD_SIZE, WORD_ALIGN) }
