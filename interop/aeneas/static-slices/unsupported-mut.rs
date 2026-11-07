pub trait Row { fn domain(&self) -> &'static mut [u8]; }
pub fn domain<C: Row>(code: &C) -> &'static mut [u8] { code.domain() }
