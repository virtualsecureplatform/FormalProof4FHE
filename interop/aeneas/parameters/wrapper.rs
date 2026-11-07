use algebra::Goldilocks;
use pcs::{matrix_weighted::{Parameters, Error}, utils::code::BlockReedSolomonCode};
type Code = BlockReedSolomonCode<Goldilocks>;
type Params = Parameters<Code>;

// These wrappers call the original dependency; they contain no copied constructor.
pub fn new_encoded(n: usize, w: usize, left: usize, q: usize, code: Code) -> Result<Params, Error> {
    Parameters::new_encoded::<Goldilocks>(n, w, left, q, code)
}
pub fn header(params: &Params) -> (usize, usize, usize, usize) {
    (params.num_vars(), params.width(), params.left_vars(), params.queries())
}
pub fn retained_code(params: &Params) -> &Code {
    params.code()
}
