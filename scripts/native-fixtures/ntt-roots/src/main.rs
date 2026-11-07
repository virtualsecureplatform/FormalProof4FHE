//! Direct locked native-plan evidence, not a Rust/Lean refinement proof.
fn reference_power(modulus: u64, base: u64, mut exponent: u64) -> u64 {
    let mut result = 1_u128;
    let mut base = base as u128 % modulus as u128;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = result * base % modulus as u128;
        }
        base = base * base % modulus as u128;
        exponent >>= 1;
    }
    result as u64
}

fn arithmetic() {
    use concrete_ntt::{
        fastdiv::Div64,
        prime::{exp_mod64, mul_mod64},
    };
    let divisors = [2_u64, 3, 17, 97, 65536, 18446744069414584321, u64::MAX];
    let inputs = [0_u128, 1, u64::MAX as u128, 1_u128 << 64, u128::MAX];
    let values = [0_u64, 1, 2, 18446744069414584320, u64::MAX];
    let exponents = [0_u64, 1, 2, 63, 64, u64::MAX];
    for modulus in divisors {
        let divisor = Div64::new(modulus);
        for input in inputs {
            assert_eq!(
                Div64::rem_u128(input, divisor),
                (input % modulus as u128) as u64
            );
        }
        for left in values {
            for right in values {
                assert_eq!(
                    mul_mod64(divisor, left, right),
                    ((left as u128 * right as u128) % modulus as u128) as u64
                );
            }
            for exponent in exponents {
                assert_eq!(
                    exp_mod64(divisor, left, exponent),
                    reference_power(modulus, left, exponent)
                );
            }
        }
    }
    println!("ARITH rem-cases=35 mul-cases=175 power-cases=210");
}

fn main() {
    arithmetic();
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
