pub fn encode_word(value: u64) -> Result<Vec<u8>, bincode::error::EncodeError> {
    bincode::encode_to_vec(value, bincode::config::standard())
}
