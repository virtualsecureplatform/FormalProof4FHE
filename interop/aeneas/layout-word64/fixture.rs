pub fn preserve(value: core::alloc::Layout) -> core::alloc::Layout { value }
pub fn size(value: core::alloc::Layout) -> usize { value.size() }
pub fn align(value: core::alloc::Layout) -> usize { value.align() }
