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

fn limb_products() {
    use concrete_ntt::fastdiv::Div64;
    let max = u64::MAX;
    let inputs = [
        [0, 0, 0, 0],
        [max, max, max, max],
        [1, 0, 0, 0],
        [0, 0, 0, 1],
        [max, 0, max, 0],
        [0, max, 0, max],
        [max - 1, max, 1, max],
    ];
    for input in inputs {
        // The backend exposes its otherwise unnamed u256 through Div64.
        let mut word = Div64::new(2).double_reciprocal;
        word.x0 = input[0];
        word.x1 = input[1];
        word.x2 = input[2];
        word.x3 = input[3];
        for right in [0, 1, 2, (1_u64 << 32) + 1, max] {
            let (low, high) = word.mul_u256_u64(right);
            println!(
                "LIMB64 {} {} {} {} {} {} {} {} {} {}",
                input[0], input[1], input[2], input[3], right, low.x0, low.x1, low.x2, low.x3, high
            );
        }
        for right in [
            0_u128,
            1,
            (1_u128 << 64) - 1,
            1_u128 << 64,
            (1_u128 << 64) + 1,
            u128::MAX,
        ] {
            let low = word.wrapping_mul_u256_u128(right);
            println!(
                "LIMB128 {} {} {} {} {} {} {} {} {}",
                input[0], input[1], input[2], input[3], right, low.x0, low.x1, low.x2, low.x3
            );
        }
        for divisor in [2_u64, 3, 17, 97, 65536, 18446744069414584321, max] {
            let (quotient, remainder) = word.div_rem_u256_u64(divisor);
            println!(
                "LIMBDIV {} {} {} {} {} {} {} {} {} {}",
                input[0],
                input[1],
                input[2],
                input[3],
                divisor,
                quotient.x0,
                quotient.x1,
                quotient.x2,
                quotient.x3,
                remainder
            );
        }
        for other in inputs {
            let mut right = Div64::new(2).double_reciprocal;
            right.x0 = other[0];
            right.x1 = other[1];
            right.x2 = other[2];
            right.x3 = other[3];
            let (low, carry) = word.overflowing_add(right);
            println!(
                "LIMBADD {} {} {} {} {} {} {} {} {} {} {} {} {}",
                input[0],
                input[1],
                input[2],
                input[3],
                other[0],
                other[1],
                other[2],
                other[3],
                low.x0,
                low.x1,
                low.x2,
                low.x3,
                u8::from(carry)
            );
        }
    }
}

fn reciprocal_states() {
    for divisor in [2_u64, 3, 17, 97, 65536, 18446744069414584321, u64::MAX] {
        let state = concrete_ntt::fastdiv::Div64::new(divisor);
        let reciprocal = state.double_reciprocal;
        println!(
            "DIVINIT {} {} {} {} {} {}",
            divisor,
            reciprocal.x0,
            reciprocal.x1,
            reciprocal.x2,
            reciprocal.x3,
            state.single_reciprocal
        );
    }
}

fn primality() {
    for modulus in (0_u64..200).chain([
        2013265921,
        18446744069414584321,
        u64::MAX,
        341550071728321,
        3825123056546413051,
    ]) {
        println!(
            "PRIME {} {}",
            modulus,
            u8::from(concrete_ntt::prime::is_prime64(modulus))
        );
    }
}

fn main() {
    primality();
    limb_products();
    reciprocal_states();
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
        assert_eq!(plan.modulus(), modulus);
        assert_eq!(plan.ntt_size(), size);
        assert_eq!(plan.root(), expected);
        println!("ROOT modulus={modulus} size={size} value={}", plan.root());
        if modulus == 18446744069414584321 {
            assert!(plan.root_powers_shoup().is_empty());
            let mut normalized = vec![1_u64; size];
            plan.normalize(&mut normalized);
            for (index, value) in normalized.iter().enumerate() {
                println!("NORM {modulus} {size} {index} {value}");
            }
            for degree in [0, 1, size / 2, size - 1] {
                let mut monomial = vec![0_u64; size];
                plan.fwd_coeff_one_monomial(degree, &mut monomial);
                for (index, value) in monomial.iter().enumerate() {
                    println!("MONOMIAL {modulus} {size} {degree} {index} {value}");
                }
                let mut values = vec![0_u64; size];
                values[degree] = 1;
                plan.fwd(&mut values);
                for (index, value) in values.iter().enumerate() {
                    println!("NTTFWD {modulus} {size} {degree} {index} {value}");
                }
                plan.inv(&mut values);
                plan.normalize(&mut values);
                for (index, value) in values.iter().enumerate() {
                    println!("NTTINV {modulus} {size} {degree} {index} {value}");
                    assert_eq!(*value, u64::from(index == degree));
                }
            }
        }
        assert_eq!(plan.root_powers().len(), 2 * size);
        for (index, value) in plan.root_powers().iter().enumerate() {
            println!("POWER {modulus} {size} {index} {value}");
        }
    }
    assert!(concrete_ntt::prime64::Plan::try_new(8, 97).is_none());
    assert!(concrete_ntt::prime64::Plan::try_new(16, 17).is_none());
    println!("REJECT small-domain=true unsupported-order=true");
}
