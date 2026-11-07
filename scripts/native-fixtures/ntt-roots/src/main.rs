//! Direct locked native-plan evidence, not a Rust/Lean refinement proof.
fn main() {
    for (modulus, size, expected) in [
        (97_u64, 16_usize, 51),
        (193, 16, 151),
        (193, 32, 94),
        (18446744069414584321, 32, 549755813888),
        (18446744069414584321, 1024, 455906449640507599),
    ] {
        let plan = concrete_ntt::prime64::Plan::try_new(size, modulus)
            .expect("fixture domain must be supported");
        assert_eq!(plan.root(), expected);
        println!("ROOT modulus={modulus} size={size} value={}", plan.root());
    }
    assert!(concrete_ntt::prime64::Plan::try_new(8, 97).is_none());
    assert!(concrete_ntt::prime64::Plan::try_new(16, 17).is_none());
    println!("REJECT small-domain=true unsupported-order=true");
}
