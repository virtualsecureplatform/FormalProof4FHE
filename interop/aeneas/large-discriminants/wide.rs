#![feature(repr128)]

#[repr(u64)]
pub enum Wide64 {
    Zero = 0,
    High = 9223372036854775808,
    Last = 18446744073709551615,
}

#[repr(u128)]
pub enum Wide128 {
    Zero = 0,
    Last = 340282366920938463463374607431768211455,
}

pub fn preserve(value: Wide64) -> Wide64 { value }
pub fn cast_u64(value: Wide64) -> u64 { value as u64 }
pub fn cast_u128(value: Wide128) -> u128 { value as u128 }
