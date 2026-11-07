pub fn mutable(value: Option<usize>, output: &mut usize) -> bool {
    value.is_none_or(|actual| { *output = actual; true })
}
