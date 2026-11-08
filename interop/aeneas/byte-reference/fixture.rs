pub fn checked_read(bytes: &[u8], index: usize) -> Option<u8> {
    if index < bytes.len() { Some(bytes[index]) } else { None }
}
pub fn checked_write(bytes: &mut [u8], index: usize, value: u8) -> bool {
    if index < bytes.len() { bytes[index] = value; true } else { false }
}
