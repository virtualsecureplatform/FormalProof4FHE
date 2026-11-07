pub trait Row { fn domain(&self) -> &'static [&'static [u8]]; }
pub fn domain<C: Row>(code: &C) -> &'static [&'static [u8]] { code.domain() }
