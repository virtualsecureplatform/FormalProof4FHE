#![feature(allocator_api)]
#![allow(dead_code)]

use std::alloc::{Allocator, Global, Layout};
use std::ptr::NonNull;

/// Retain the original allocator trait method and its zero-size dispatch.
pub unsafe fn deallocate_global(data: NonNull<u8>, layout: Layout) {
    unsafe { Global.deallocate(data, layout) };
}
