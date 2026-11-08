#![allow(dead_code)]

/// Retain the ordinary allocator's original external declaration and callers.
/// Callers must satisfy Rust's allocation/layout contract.
pub unsafe fn deallocate_bytes(data: *mut u8, size: usize, alignment: usize) {
    let layout = unsafe { std::alloc::Layout::from_size_align_unchecked(size, alignment) };
    unsafe { std::alloc::dealloc(data, layout) };
}
