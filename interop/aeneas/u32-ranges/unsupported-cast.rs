#![feature(pattern_type_macro, pattern_types)]
pub type Nanos = std::pat::pattern_type!(u32 is 0..=999999999);
pub fn checked(value: u32) -> Option<Nanos> {
    if value <= 999999999 {
        Some(unsafe { std::mem::transmute(value) })
    } else {
        None
    }
}
