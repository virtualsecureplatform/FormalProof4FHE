pub fn code_bytes(
    code: &pcs::utils::code::BlockReedSolomonCode<algebra::Goldilocks>,
) -> Result<Vec<u8>, bincode::error::EncodeError> {
    bincode::serde::encode_to_vec(code, bincode::config::standard())
}
