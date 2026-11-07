use pcs::matrix_weighted::{Error, Parameters};

// Call the unchanged dependency. Keep its actual field/code trait requirements.
pub fn generic_new_encoded<F: algebra::PrimeField, C: pcs::utils::code::RowCode<F>>(
    n: usize, w: usize, left: usize, q: usize, code: C,
) -> Result<Parameters<C>, Error> {
    Parameters::new_encoded::<F>(n, w, left, q, code)
}
