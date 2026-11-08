#![feature(pattern_type_macro, pattern_types)]

pub type NoHighBit = std::pat::pattern_type!(usize is 0..=9223372036854775807);
pub type Window = std::pat::pattern_type!(usize is 7..=19);

pub struct Stored {
    pub capacity: NoHighBit,
    pub window: Window,
}

pub fn preserve(value: Stored) -> Stored {
    value
}

pub fn select(value: Stored) -> Window {
    value.window
}

pub fn identity(value: NoHighBit) -> NoHighBit {
    value
}
