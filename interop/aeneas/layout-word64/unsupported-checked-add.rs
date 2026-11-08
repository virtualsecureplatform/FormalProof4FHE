pub fn preserve(value: core::alloc::Layout) -> core::alloc::Layout { value }
pub fn size(value: core::alloc::Layout) -> usize { value.size() }
pub fn align(value: core::alloc::Layout) -> usize { value.align() }
pub fn word_max() -> usize { usize::MAX }
pub fn signed_min() -> isize { isize::MIN }
pub fn signed_identity(value: isize) -> isize { value }
pub fn add_one(value: usize) -> Option<usize> { value.checked_add(1) }
