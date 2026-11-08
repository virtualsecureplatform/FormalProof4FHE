#![feature(pattern_type_macro, pattern_types)]

pub type Nanos = std::pat::pattern_type!(u32 is 0..=999999999);
pub type Window = std::pat::pattern_type!(u32 is 7..=19);

pub struct Stored {
    pub nanos: Nanos,
    pub window: Window,
}

pub fn preserve(value: Stored) -> Stored {
    value
}

pub fn select(value: Stored) -> Window {
    value.window
}

pub fn identity(value: Nanos) -> Nanos {
    value
}
