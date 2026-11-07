pub fn captured_option(value: Option<usize>, expected: &usize) -> bool {
    value.is_none_or(|actual| actual != *expected)
}
