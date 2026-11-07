use snarks::packed_oracle::CanonicalVerifierOracle;

pub fn fields<'a, O, P>(oracle: &CanonicalVerifierOracle<'a, O, P>) -> (&'a P, &'a O) {
    (oracle.parameters, &oracle.commitment.root)
}
pub fn registry_len<O, P>(registry: &[CanonicalVerifierOracle<'_, O, P>]) -> usize {
    registry.len()
}
pub fn registry_get<'a, O, P>(registry: &[CanonicalVerifierOracle<'a, O, P>], index: usize) -> Option<(&'a P, &'a O)> {
    match registry.get(index) {
        Some(oracle) => Some((oracle.parameters, &oracle.commitment.root)),
        None => None,
    }
}

pub fn root_bytes<'a, P>(oracle: &CanonicalVerifierOracle<'a, pcs::utils::hash::Digest512, P>) -> &'a [u8; 64] {
    &oracle.commitment.root.0
}
