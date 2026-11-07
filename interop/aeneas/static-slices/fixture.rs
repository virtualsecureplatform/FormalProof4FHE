pub trait Row {
    fn width(&self) -> usize;
    fn blocks(&self) -> usize;
    fn domain(&self) -> &'static [u8];
}
pub fn domain<C: Row>(code: &C) -> &'static [u8] { code.domain() }
pub fn dimensions<C: Row>(code: &C) -> (usize,usize) { (code.width(),code.blocks()) }
pub fn metadata<C: Row>(code: &C) -> (usize, usize, &'static [u8]) {
    (code.width(), code.blocks(), code.domain())
}
pub fn copy_domain<C: Row>(code: &C) -> (&'static [u8], &'static [u8]) {
    let domain = code.domain();
    (domain, domain)
}
pub fn after_local<C: Row>(code: &C) -> (&'static [u8], usize) {
    let domain = code.domain();
    let width = code.width();
    (domain, width)
}
pub fn preserve_borrow(input: &[u8]) -> &[u8] { input }
