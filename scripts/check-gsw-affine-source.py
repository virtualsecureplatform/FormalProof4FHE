#!/usr/bin/env python3
"""Exact phase checks for affine maps of complete same-key LWE transcripts.

The output key is binary; masks range uniformly over all residues. Source
errors and affine-map coefficients are fixed independently of that key.
The source key may be an arbitrary fixed function of the output key.
The scalar phase image is an exactly counted coset, not a sampled estimate.
These maps are not claimed to have the fresh ciphertext distribution.
"""

import argparse
from fractions import Fraction
import itertools
import json
from math import gcd
from pathlib import Path
import random


def magnitude(x, q):
    x %= q
    return min(x, q - x)


def decrypt_weights(bits):
    return [-a * b for a in bits for b in bits] + list(bits) + [1]


def source_raw(bits, masks, errors, p, q):
    n = len(bits)
    return list(masks) + [
        (sum(bits[i] * masks[i * p + j] for i in range(n)) + errors[j]) % q
        for j in range(p)]


def direct_phase(bits, masks, errors, p, q, transform, offset):
    raw = source_raw(bits, masks, errors, p, q)
    cipher = [(sum(a * b for a, b in zip(row, raw)) + c) % q
              for row, c in zip(transform, offset)]
    return sum(a * b for a, b in zip(decrypt_weights(bits), cipher)) % q


def phase_coefficients(bits, errors, p, q, transform, offset, source_secret=None):
    weights = decrypt_weights(bits)
    raw_coeff = [sum(weights[r] * transform[r][j] for r in range(len(weights))) % q
                 for j in range(len(transform[0]))]
    source_secret = bits if source_secret is None else source_secret
    d = len(source_secret)
    linear = [(raw_coeff[i * p + j] + source_secret[i] * raw_coeff[d * p + j]) % q
              for i in range(d) for j in range(p)]
    constant = (sum(a * b for a, b in zip(weights, offset)) +
                sum(raw_coeff[d * p + j] * errors[j] for j in range(p))) % q
    return linear, constant


def exact_failure(n, p, q, errors, transform, offset, bound, source_secret=None):
    failure = Fraction(0)
    nonzero_linear_keys = 0
    for bits in itertools.product((0, 1), repeat=n):
        transported = None if source_secret is None else source_secret(bits)
        linear, constant = phase_coefficients(bits, errors, p, q, transform, offset, transported)
        divisor = gcd(q, *linear)
        nonzero_linear_keys += divisor != q
        target = (q // 2) * bits[0] * bits[1] * bits[2]
        values = range(0, q, divisor)
        bad = sum(magnitude(constant + x - target, q) > bound for x in values)
        failure += Fraction(bad, q // divisor)
    return failure / (2 ** n), nonzero_linear_keys


def sharp_map(q):
    # Only T[0,1] = w*(a[0]+a[1]-y); all other output entries are zero.
    transform = [[0] * 4 for _ in range(13)]
    w = q // 2
    transform[1] = [w, w, 0, -w]
    return transform, [0] * 13


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('docs/GSWAffineSourceExploration.json'))
    args = parser.parse_args()
    rng = random.Random(20261017)
    groups = []
    total_maps = total_cases = 0
    for n, p, q in itertools.product((3, 4, 5), (1, 2), (8, 16, 64, 256)):
        output_size, input_size = n * n + n + 1, n * p + p
        bound = (q // 2 - 1) // 8
        rates, active_counts = [], []
        for _ in range(8):
            transform = [[rng.randrange(q) for _ in range(input_size)]
                         for _ in range(output_size)]
            offset = [rng.randrange(q) for _ in range(output_size)]
            total_maps += 1
            for error in (-1, 0, 1):
                rate, active = exact_failure(n, p, q, [error] * p,
                                             transform, offset, bound)
                assert rate >= Fraction(1, 16)
                rates.append(rate)
                active_counts.append(active)
                total_cases += 1
        groups.append(dict(n=n, samples=p, q=q, bound=bound, maps=8, error_vectors=3,
                           minimum_failure=str(min(rates)), maximum_failure=str(max(rates)),
                           minimum_nonzero_linear_keys=min(active_counts)))

    transport_checks = []
    for n, d, p, q in itertools.product((3, 4), (1, 3, 6), (1, 2), (16, 64)):
        keys = list(itertools.product((0, 1), repeat=n))
        transport = {bits: [rng.randrange(q) for _ in range(d)] for bits in keys}
        rates = []
        for _ in range(4):
            transform = [[rng.randrange(q) for _ in range(d * p + p)]
                         for _ in range(n * n + n + 1)]
            offset = [rng.randrange(q) for _ in range(n * n + n + 1)]
            for error in (-1, 0, 1):
                rate, _ = exact_failure(n, p, q, [error] * p, transform, offset,
                                        (q // 2 - 1) // 8, transport.__getitem__)
                assert rate >= Fraction(1, 16)
                rates.append(rate)
        transport_checks.append(dict(output_key_bits=n, source_dimension=d, samples=p,
                                     q=q, maps=4, error_vectors=3,
                                     minimum_failure=str(min(rates))))
    packed_checks = []
    for p in (1, 2):
        def pack(bits):
            return [sum(bit << i for i, bit in enumerate(bits))]
        assert len({tuple(pack(bits)) for bits in itertools.product((0, 1), repeat=4)}) == 16
        rates = []
        for _ in range(4):
            transform = [[rng.randrange(16) for _ in range(2 * p)] for _ in range(21)]
            offset = [rng.randrange(16) for _ in range(21)]
            for error in (-1, 0, 1):
                rate, _ = exact_failure(4, p, 16, [error] * p, transform, offset, 0, pack)
                assert rate >= Fraction(1, 16)
                rates.append(rate)
        packed_checks.append(dict(output_key_bits=4, source_dimension=1, q=16, samples=p,
                                  source_key_uniform=True, maps=4, error_vectors=3,
                                  minimum_failure=str(min(rates))))

    exhaustive_draws = 0
    for q in (4, 8):
        for _ in range(4):
            transform = [[rng.randrange(q) for _ in range(4)] for _ in range(13)]
            offset = [rng.randrange(q) for _ in range(13)]
            for error in (-1, 0, 1):
                counted_bad = 0
                for bits in itertools.product((0, 1), repeat=3):
                    linear, constant = phase_coefficients(bits, [error], 1, q, transform, offset)
                    for masks in itertools.product(range(q), repeat=3):
                        phase = direct_phase(bits, masks, [error], 1, q, transform, offset)
                        assert phase == (sum(a * b for a, b in zip(linear, masks)) + constant) % q
                        counted_bad += phase != (q // 2) * bits[0] * bits[1] * bits[2]
                        exhaustive_draws += 1
                predicted, _ = exact_failure(3, 1, q, [error], transform, offset, 0)
                assert predicted == Fraction(counted_bad, 8 * q ** 3)

    sharpness = []
    for q in (4, 8, 16, 64, 256):
        transform, offset = sharp_map(q)
        for error in (-1, 0, 1):
            rate, _ = exact_failure(3, 1, q, [error], transform, offset, 0)
            assert rate == (Fraction(1, 16) if error == 0 else Fraction(3, 16))
            sharpness.append(dict(q=q, source_error=error, failure=str(rate)))

    # Public mask rejection escapes the uniform-mask premise. The same simple
    # construction still fails on 1/4 of keys when the retained source error is odd.
    rejection = []
    q = 16
    transform, offset = sharp_map(q)
    for error in (-1, 0, 1):
        good = total = 0
        for bits in itertools.product((0, 1), repeat=3):
            for masks in itertools.product(range(q), repeat=3):
                if masks[2] % 2 == 0:
                    continue
                phase = direct_phase(bits, masks, [error], 1, q, transform, offset)
                # Native source-to-phase identity, including the amplified error.
                expected = (q // 2) * bits[0] * bits[1] * (bits[2] * masks[2] + error)
                assert phase == expected % q
                good += phase == (q // 2) * bits[0] * bits[1] * bits[2]
                total += 1
        rate = 1 - Fraction(good, total)
        assert rate == (0 if error == 0 else Fraction(1, 4))
        rejection.append(dict(q=q, source_error=error, retained_draws=total,
                              failure=str(rate), mask_acceptance='1/2'))

    result = dict(
        scope='Affine maps of complete LWE inputs, uniform masks independent of the binary output key; '
              'source secret may be any fixed function of that key.',
        limitations='A phase-simulation bound, not an IND-CPA attack. Does not cover nonlinear maps, '
                    'public rejection, mask-dependent hidden-key coupling, or key-dependent map coins. '
                    'The sharpness witness is not a fresh ciphertext sampler.',
        seed=20261017, same_key_affine_maps=total_maps, same_key_fixed_error_cases=total_cases,
        transported_key_affine_maps=sum(x['maps'] for x in transport_checks + packed_checks),
        transported_key_fixed_error_cases=sum(x['maps'] * x['error_vectors']
                                             for x in transport_checks + packed_checks),
        exact_source_draw_checks=exhaustive_draws,
        proved_lower_bound='1/16', groups=groups, source_key_transports=transport_checks,
        packed_uniform_source_transports=packed_checks, sharpness=sharpness,
        public_mask_rejection=rejection)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in (
        'same_key_affine_maps', 'same_key_fixed_error_cases', 'transported_key_affine_maps',
        'transported_key_fixed_error_cases', 'exact_source_draw_checks', 'proved_lower_bound')}))
    print('Sharp zero-error witness: 1/16 failure; odd source error: 3/16.')
    print('Source-key transport: 288 random-transport cases and 24 packed-uniform-source cases passed.')
    print('Conditioning mask[2] odd: zero-error failure 0; odd-error failure 1/4.')
    print(f'Wrote {args.output}')


if __name__ == '__main__':
    main()
