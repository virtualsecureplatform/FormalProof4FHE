#!/usr/bin/env python3
"""Check a square-zero secret lift and its Boolean-bootstrap interface.

The lift uses source modulus Q and ciphertext modulus q=Q^2, secret S=Q*x,
and error Q*e+f with f uniform in a centered interval of length Q. It gives
explicit source embeddings for zero and self-coordinate GSW phase columns.
This diagnostic does not establish a bootstrappable scheme or a Lean theorem.
"""

import argparse
import itertools
import json
from pathlib import Path
import random


def fine_values(Q):
    return range(-(Q // 2), Q - Q // 2)


def simulate_column(Q, source_mask, source_body, high, fine, shift):
    q = Q * Q
    mask = [((a - d) % Q) + Q * h for a, d, h in zip(source_mask, shift, high)]
    body = (Q * source_body + fine) % q
    return mask, body


def phase(secret, column, q):
    mask, body = column
    return (body - sum(x * a for x, a in zip(secret, mask))) % q


def uniform_source_bijections():
    records = []
    for Q in (2, 4, 8, 16):
        q = Q * Q
        for shift in sorted({0, 1, Q // 2, Q}):
            seen = set()
            for a, y, high, fine in itertools.product(range(Q), range(Q), range(Q), fine_values(Q)):
                mask, body = simulate_column(Q, [a], y, [high], fine, [shift])
                output = (mask[0], body)
                assert output not in seen
                seen.add(output)
                # The centered fine part is uniquely determined by body mod Q.
                residue = body % Q
                recovered_fine = residue if residue < Q - Q // 2 else residue - Q
                assert recovered_fine == fine
                assert ((body - recovered_fine) // Q) % Q == y
                assert (mask[0] % Q + shift) % Q == a
                assert mask[0] // Q == high
            assert len(seen) == q * q
            records.append(dict(Q=Q, q=q, source_mask_shift=shift, checked_outputs=len(seen)))
    return records


def real_phase_trial(Q, n, radius, seed):
    rng = random.Random(seed)
    q = Q * Q
    levels = q.bit_length() - 1
    keys = list(itertools.product((0, 1), repeat=n))
    keys += [tuple(rng.randrange(Q) for _ in range(n)) for _ in range(4)]
    public_checks = control_checks = zero_products = 0
    for key in keys:
        secret = [Q * x for x in key]
        for first, second in itertools.product(secret, repeat=2):
            assert first * second % q == 0
            zero_products += 1
        for index, block, level in itertools.product(range(n), range(n + 1), range(levels)):
            weight = 1 << level
            # block n is the body feature; other blocks have phase -S_i*S_j*g=0.
            shift = [0] * n
            if block == n:
                shift[index] = weight
            a = [rng.randrange(Q) for _ in range(n)]
            error = rng.randint(-radius, radius)
            fine = rng.choice(fine_values(Q))
            y = (sum(x * v for x, v in zip(key, a)) + error) % Q
            high = [rng.randrange(Q) for _ in range(n)]
            column = simulate_column(Q, a, y, high, fine, shift)
            message = secret[index]
            target = message * weight if block == n else -message * secret[block] * weight
            expected_error = Q * error + fine
            assert phase(secret, column, q) == (target + expected_error) % q
            assert abs(expected_error) <= Q * radius + Q // 2
            control_checks += 1
        for _ in range(8):
            a = [rng.randrange(Q) for _ in range(n)]
            error = rng.randint(-radius, radius)
            fine = rng.choice(fine_values(Q))
            y = (sum(x * v for x, v in zip(key, a)) + error) % Q
            high = [rng.randrange(Q) for _ in range(n)]
            column = simulate_column(Q, a, y, high, fine, [0] * n)
            assert phase(secret, column, q) == (Q * error + fine) % q
            public_checks += 1
    return dict(Q=Q, q=q, n=n, source_radius=radius, seed=seed,
                key_draws=len(keys), public_zero_phase_checks=public_checks,
                self_coordinate_control_phase_checks=control_checks,
                square_zero_secret_products=zero_products,
                output_error_bound=Q * radius + Q // 2)


def missing_boolean_interface():
    records = []
    for Q in (2, 4, 8, 16):
        q = Q * Q
        max_and_matches = 0
        polynomial_restrictions = 0
        # On {0,Q}^2 every ring polynomial reduces to c + a*z0 + b*z1:
        # all quadratic and higher terms in these inputs are zero modulo q.
        for c, a, b in itertools.product(range(q), range(Q), range(Q)):
            outputs = [(c + a * Q * x + b * Q * y) % q
                       for x, y in itertools.product((0, 1), repeat=2)]
            target = [0, 0, 0, Q]
            assert (outputs[0] - outputs[1] - outputs[2] + outputs[3]) % q == 0
            matches = sum(x == y for x, y in zip(outputs, target))
            assert matches < 4
            max_and_matches = max(max_and_matches, matches)
            polynomial_restrictions += 1
        assert max_and_matches == 3
        bit_extractors = 0
        for c, a in itertools.product(range(q), range(Q)):
            outputs = [c % q, (c + a * Q) % q]
            assert outputs[0] % Q == outputs[1] % Q
            assert outputs != [0, 1]
            bit_extractors += 1
        and_wrong = nand_wrong = 0
        for x, y in itertools.product((0, 1), repeat=2):
            product = (Q * x) * (Q * y) % q
            assert product == 0
            and_wrong += product != Q * x * y
            nand_wrong += (Q - product) % q != Q * (1 - x * y)
        assert and_wrong == nand_wrong == 1
        records.append(dict(Q=Q, q=q, all_two_input_polynomial_restrictions=polynomial_restrictions,
                            largest_encoded_AND_truth_table_match=max_and_matches,
                            all_one_input_polynomial_restrictions=bit_extractors,
                            polynomial_bit_extractors=0,
                            native_encoded_AND_wrong_corners=and_wrong,
                            native_encoded_NAND_wrong_corners=nand_wrong))
    return records


def no_fine_noise_disclosure():
    records = []
    for Q in (4, 8, 16, 64):
        q = Q * Q
        rng = random.Random(20261018 + Q)
        # Zero-column bodies are all multiples of Q when the fine noise is absent.
        bodies = [Q * rng.randrange(Q) for _ in range(8)]
        checks = 0
        for selectors, bit in itertools.product(itertools.product((0, 1), repeat=8), (0, 1)):
            # Body-feature gadget level zero has weight one. Its public body
            # coordinate alone reveals the bit, regardless of secret or masks.
            encrypted_body = (sum(take * body for take, body in zip(selectors, bodies)) + bit) % q
            assert encrypted_body % Q == bit
            checks += 1
        records.append(dict(Q=Q, q=q, public_bit_disclosure_checks=checks))
    return records


def rescale_body_column(Q, column):
    """Publicly recover the coarse source body and lift it to top gadget weight."""
    mask, body = column
    q, weight = Q * Q, Q * Q // 2
    residue = body % Q
    fine = residue if residue < Q - Q // 2 else residue - Q
    coarse_body = ((body - fine) // Q) % Q
    return ([(weight // Q) * (a % Q) % q for a in mask],
            weight * coarse_body % q)


def body_rescaling_trials():
    records = []
    for Q, n in itertools.product((4, 8, 16, 64), (1, 2, 3)):
        rng = random.Random(2026101802 + 100 * Q + n)
        q, weight = Q * Q, Q * Q // 2
        checks = failures = 0
        for key in itertools.product((0, 1), repeat=n):
            secret = [Q * x for x in key]
            for index, error in itertools.product(range(n), range(-3, 4)):
                source_mask = [rng.randrange(Q) for _ in range(n)]
                source_body = (sum(x * a for x, a in zip(key, source_mask)) + error) % Q
                shift = [int(i == index) for i in range(n)]
                column = simulate_column(Q, source_mask, source_body,
                                         [rng.randrange(Q) for _ in range(n)],
                                         rng.choice(fine_values(Q)), shift)
                converted = rescale_body_column(Q, column)
                actual = phase(secret, converted, q)
                assert actual == weight * (key[index] + error) % q
                decoded = int(min((actual - weight) % q, (weight - actual) % q) <
                              min(actual, (-actual) % q))
                failed = decoded != key[index]
                assert failed == bool(error % 2)
                failures += failed
                checks += 1
        records.append(dict(Q=Q, q=q, n=n, body_rescale_phase_checks=checks,
                            body_rescale_decode_failures=failures,
                            failure_exactly_odd_source_error=True))
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('docs/GSWNilpotentSecretExploration.json'))
    args = parser.parse_args()
    bijections = uniform_source_bijections()
    phases = [real_phase_trial(Q, n, radius, 20261018 + 1000 * Q + 100 * n + 10 * radius + seed)
              for Q, n, radius, seed in itertools.product((4, 8, 16, 64), (1, 2, 3), (0, 1), range(2))]
    boolean = missing_boolean_interface()
    disclosure = no_fine_noise_disclosure()
    rescaling = body_rescaling_trials()
    summary = dict(
        phase_families=len(phases), key_draws=sum(r['key_draws'] for r in phases),
        public_zero_phase_checks=sum(r['public_zero_phase_checks'] for r in phases),
        self_coordinate_control_phase_checks=sum(r['self_coordinate_control_phase_checks'] for r in phases),
        square_zero_secret_products=sum(r['square_zero_secret_products'] for r in phases),
        exact_uniform_source_bijections=len(bijections),
        exact_uniform_source_outputs=sum(r['checked_outputs'] for r in bijections),
        two_input_polynomial_restrictions=sum(r['all_two_input_polynomial_restrictions'] for r in boolean),
        one_input_polynomial_restrictions=sum(r['all_one_input_polynomial_restrictions'] for r in boolean),
        no_polynomial_encoded_AND=True, no_polynomial_normalized_bit_extraction=True,
        no_fine_noise_public_bit_disclosures=sum(r['public_bit_disclosure_checks'] for r in disclosure),
        body_rescale_phase_checks=sum(r['body_rescale_phase_checks'] for r in rescaling),
        body_rescale_decode_failures=sum(r['body_rescale_decode_failures'] for r in rescaling))
    args.output.write_text(json.dumps(dict(
        scope='A public ordinary-LWE source lift with q=Q^2 and square-zero secret S=Q*x; '
              'checks full uniform-source columns and real self-coordinate phase targets.',
        limitations='Not a Lean theorem or FHE security/correctness proof. Self-coordinate targets '
                    'S_i are not the bits of the secret encoding and are not Boolean controls. '
                    'Diagnostic source errors do not instantiate an asymptotic hardness family. '
                    'Polynomial exclusions cover fixed plaintext-ring polynomials; '
                    'they do not exclude a new non-polynomial public rescaling/conversion '
                    'algorithm with its own complete security and correctness proofs.',
        summary=summary, uniform_source_bijections=bijections, real_phase_trials=phases,
        boolean_interface=boolean, absent_fine_noise_disclosure=disclosure,
        body_rescaling_trials=rescaling), indent=2) + '\n')
    print(json.dumps(summary))
    print(f'Wrote {args.output}')


if __name__ == '__main__':
    main()
