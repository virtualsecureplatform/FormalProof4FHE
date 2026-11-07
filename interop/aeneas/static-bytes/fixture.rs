pub fn domain() -> &'static [u8] {
    b"block-rs/negacyclic-ntt/v1"
}
pub fn array() -> &'static [u8; 4] {
    b"\x00\x7f\x80\xff"
}
pub fn empty() -> &'static [u8] {
    b""
}
pub fn copy_domain() -> (&'static [u8], &'static [u8]) {
    let bytes = domain();
    (bytes, bytes)
}
pub fn escaped() -> &'static [u8] {
    b"\"\\\n\t\r\0\x7f\xcf\x80"
}
pub fn preserve_borrow(input: &[u8]) -> &[u8] {
    input
}
