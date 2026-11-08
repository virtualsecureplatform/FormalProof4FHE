pub struct Error(pub &'static str);

pub fn propagate(value: Option<usize>) -> Result<usize, Error> {
    let value = value.ok_or(Error("table size overflow"))?;
    Ok(value)
}

pub fn error_field(error: Error) -> &'static str {
    error.0
}

pub fn choose(value: Result<usize, Error>) -> Result<usize, Error> {
    match value {
        Ok(value) => Ok(value),
        Err(error) => Err(Error(error.0)),
    }
}
