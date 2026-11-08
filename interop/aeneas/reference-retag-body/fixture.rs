#[inline(never)]
fn identity<T>(value: T) -> T { value }

#[inline(never)]
fn borrowed<'a>(value: &'a [u8]) -> &'a [u8] { value }

pub unsafe fn shared_scope(data: *const u8, length: usize) {
    let slice = unsafe { core::slice::from_raw_parts(data, length) };
    let _retagged = borrowed(slice);
}
pub unsafe fn mutable_scope(data: *mut u8, length: usize) {
    let slice = unsafe { core::slice::from_raw_parts_mut(data, length) };
    let _retagged = identity(slice);
}
pub const BYTE_SIZE: usize = core::mem::size_of::<u8>();
pub const BYTE_ALIGN: usize = core::mem::align_of::<u8>();
