#![feature(try_reserve_kind)]
#![allow(dead_code)]
pub fn error_kind(error: &std::collections::TryReserveError) -> std::collections::TryReserveErrorKind {
    error.kind()
}
