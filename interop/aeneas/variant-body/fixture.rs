#![allow(dead_code)]
use std::alloc::Layout;
use std::ptr::NonNull;

pub fn release(_value: Vec<u8>) {}

pub fn present(pointer: NonNull<u8>, layout: Layout) -> Option<(NonNull<u8>, Layout)> {
    Some((pointer, layout))
}

pub fn absent() -> Option<(NonNull<u8>, Layout)> {
    None
}

pub fn selected_layout(value: Option<(NonNull<u8>, Layout)>, fallback: Layout) -> Layout {
    match value {
        Some((_, layout)) => layout,
        None => fallback,
    }
}
