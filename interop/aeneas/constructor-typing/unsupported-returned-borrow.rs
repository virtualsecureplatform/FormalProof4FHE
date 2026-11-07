pub fn returned<'a>(value: Option<&'a usize>, fallback: &'a usize) -> &'a usize {
    value.unwrap_or_else(|| fallback)
}
