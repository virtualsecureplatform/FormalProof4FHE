#![allow(dead_code)]

pub struct Error(pub &'static str);

pub fn literal() -> &'static str {
    "invalid dimensions or query count"
}

pub fn nested_error() -> Result<u64, Error> {
    Err(Error("table size overflow"))
}

pub fn conditional_error(valid: bool) -> Result<u64, Error> {
    if valid {
        Ok(7)
    } else {
        Err(Error("encoded size overflow"))
    }
}

pub fn unicode_literal() -> &'static str {
    "π/秘密"
}

pub fn preserve_borrow(input: &str) -> &str {
    input
}

pub fn escaped_literal() -> &'static str {
    "\"\\\n\t\r\0\x7f"
}
