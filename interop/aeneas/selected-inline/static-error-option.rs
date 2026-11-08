pub struct Error(pub &'static str);

pub fn convert(value: Option<usize>) -> Result<usize, Error> {
    value.ok_or(Error("table size overflow"))
}

pub fn direct(value: Option<usize>) -> Result<usize, Error> {
    match value {
        Some(value) => Ok(value),
        None => Err(Error("table size overflow")),
    }
}

pub fn eager_match(value: Option<usize>) -> Result<usize, Error> {
    let error = Error("table size overflow");
    match value {
        Some(value) => Ok(value),
        None => Err(error),
    }
}
