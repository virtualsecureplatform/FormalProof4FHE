pub struct Own<T> {
    pub bytes: Vec<u8>,
    pub other: T,
}

pub fn process<T>(
    input: Result<(), String>,
    bytes: Vec<u8>,
    other: T,
) -> Result<Vec<u8>, String> {
    let live = Own { bytes, other };
    input?;
    Ok(live.bytes)
}
