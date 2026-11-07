// Two Copy parents have the same trait name but different instantiated types.
pub trait Pair<T: Copy>: Copy {
    fn same(self) -> Self;
    fn other(self, value: T) -> T;
}

pub fn both<T: Copy, P: Pair<T>>(pair: P, value: T) -> (P, T) {
    (pair.same(), pair.other(value))
}

// Include core::result during extraction: branch has a retained, infallible Rust
// body while the builtin Lean model explicitly returns Std.Result.
pub fn propagate(value: Result<usize, usize>) -> Result<usize, usize> {
    let result = value?;
    Ok(result)
}
