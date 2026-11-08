pub fn mutable_identity(pointer: *mut u8) -> *mut u8 { pointer }
pub fn constant_identity(pointer: *const u8) -> *const u8 { pointer }
pub fn to_constant(pointer: *mut u8) -> *const u8 { pointer as *const u8 }
pub fn to_mutable(pointer: *const u8) -> *mut u8 { pointer as *mut u8 }
pub fn to_word(pointer: *mut u8) -> *mut u64 { pointer as *mut u64 }
