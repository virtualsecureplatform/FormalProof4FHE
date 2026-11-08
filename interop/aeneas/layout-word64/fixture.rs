pub fn preserve(value: core::alloc::Layout) -> core::alloc::Layout { value }
pub fn size(value: core::alloc::Layout) -> usize { value.size() }
pub fn align(value: core::alloc::Layout) -> usize { value.align() }
pub fn word_max() -> usize { usize::MAX }
pub fn signed_min() -> isize { isize::MIN }
pub fn signed_identity(value: isize) -> isize { value }
pub fn overflowing_add_one(value: usize) -> (usize, bool) { value.overflowing_add(1) }
pub fn signed_overflowing_add_one(value: isize) -> (isize, bool) { value.overflowing_add(1) }
