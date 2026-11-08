pub fn unsigned(value: usize, rhs: usize) -> (usize, bool) { value.overflowing_mul(rhs) }
pub fn signed(value: isize, rhs: isize) -> (isize, bool) { value.overflowing_mul(rhs) }
