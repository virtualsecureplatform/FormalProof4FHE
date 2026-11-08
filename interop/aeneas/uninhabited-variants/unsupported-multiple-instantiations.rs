#![feature(try_trait_v2)]

pub enum Never {}
pub enum Only { Impossible(Never), Live(u64) }
pub fn take(value: Only) -> u64 { match value { Only::Live(n) => n } }
pub struct EmptyWrapper { pub hole: Never }
pub enum NestedOnly { Impossible(EmptyWrapper), Live(u64) }
pub fn nested_take(value: NestedOnly) -> u64 { match value { NestedOnly::Live(n) => n } }
pub fn residual(value: Result<core::convert::Infallible, u64>) -> Result<u64, u64> {
    <Result<u64, u64> as core::ops::FromResidual<Result<core::convert::Infallible, u64>>>::from_residual(value)
}
pub struct Error(pub &'static str);
pub fn residual_error(value: Result<core::convert::Infallible, Error>) -> Result<u64, Error> {
    <Result<u64, Error> as core::ops::FromResidual<Result<core::convert::Infallible, Error>>>::from_residual(value)
}
