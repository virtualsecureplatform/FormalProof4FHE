pub const WIDTH: usize = 31;
pub const MASK: u64 = 0x0123456789abcdef;
pub const ZERO: u8 = 0;
pub const NEGATIVE: i64 = -17;
pub const WIDE: u128 = u128::MAX;
pub fn values() -> (usize, u64, u8, i64, u128) {
    (WIDTH, MASK, ZERO, NEGATIVE, WIDE)
}
