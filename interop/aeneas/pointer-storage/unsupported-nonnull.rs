pub fn get(pointer: core::ptr::NonNull<u8>) -> *mut u8 { pointer.as_ptr() }
