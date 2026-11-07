// Calls the unchanged native trait implementation; no copied accessor body.
pub fn row_metadata<F: algebra::NTTField>(code: &pcs::utils::code::BlockReedSolomonCode<F>) -> (usize, usize, &'static [u8]) {
    use pcs::utils::code::RowCode;
    (code.block_width(), code.codeword_blocks(), code.domain_separator())
}
