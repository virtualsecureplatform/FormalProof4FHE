#!/usr/bin/env python3
"""Check native midpoint products with signed digits as dimension grows.

The first raw mask is normalized to zero for exact phase diagnostics: its
noise is independent of that mask, and the product-noise identity eliminates
it. The second raw mask remains uniformly sampled. These are finite product
checks, not full larger-dimension refresh trials or a security reduction.
"""
import argparse
import importlib.util
import json
from pathlib import Path

import numpy as np

spec = importlib.util.spec_from_file_location(
    "redundant_scaling", Path(__file__).with_name("try-gsw-redundant-digits.py"))
redundant = importlib.util.module_from_spec(spec)
spec.loader.exec_module(redundant)
t = redundant.midpoint.transcript


def experiment(n, radius, samples, seed):
    levels, q = 24, 1 << 24
    rng = np.random.default_rng(seed)
    g = t.gadget(n, levels)
    width = g.shape[1]
    h, c = np.zeros((n, width), dtype=np.int64), np.zeros(width, dtype=np.int64)
    for row in range(n + 1):
        for level in range(levels):
            column, w = row * levels + level, 1 << level
            if row == 0:
                h[0, column] = w
            else:
                c[column] = w // 4
                h[0, column] -= w // 2
                h[row - 1, column] -= w // 2
    masks = (-h) % q
    results = [{"policy": policy, "products": samples, "correct": 0,
                "zero_products": 0, "correct_zero_products": 0,
                "one_products": 0, "correct_one_products": 0,
                "full_product_noise_margin": 0}
               for policy in ("unsigned", "signed_quarter_minimax")]
    identities = reconstructions = 0
    for _ in range(samples):
        secret = rng.integers(0, 2, size=n, dtype=np.int64)
        extended = np.array([1, *[-int(s) for s in secret]], dtype=np.int64)
        fresh = rng.integers(-radius, radius + 1, size=width, dtype=np.int64)
        second_error = int(rng.integers(-radius, radius + 1))
        first = np.vstack(((c + fresh) % q, masks))
        first_noise = (extended @ first - int(secret[0]) * (extended @ g)) % q
        raw_second = rng.integers(0, q, size=n, dtype=np.int64)
        actual_second = raw_second.copy()
        actual_second[1] = (actual_second[1] - q // 2) % q
        second = np.array([(int(secret @ raw_second) + second_error) % q,
                           *[int(a) for a in actual_second]], dtype=np.int64).reshape(n + 1, 1)
        second_phase = int(extended @ second[:, 0]) % q
        assert (second_phase - int(secret[1]) * (q // 2)) % q == second_error % q
        expected = int(secret[0] * secret[1])
        for result, decompose in zip(results, (redundant.unsigned, redundant.signed_quarter_digits)):
            d = decompose(second, levels)
            assert np.array_equal((g @ d) % q, second)
            assert np.max(np.abs(d)) <= 1
            reconstructions += 1
            product = (first @ d[:, 0]) % q
            phase = int(extended @ product) % q
            noise = (phase - expected * (q // 2)) % q
            predicted = (int(first_noise @ d[:, 0]) + int(secret[0]) * second_error) % q
            assert noise == predicted
            identities += 1
            centered = abs(t.centered(noise, q))
            decoded = int(abs(t.centered(phase - q // 2, q)) < abs(t.centered(phase, q)))
            correct = int(decoded == expected)
            result["correct"] += correct
            result["full_product_noise_margin"] += int(4 * centered < q)
            key = "one" if expected else "zero"
            result[key + "_products"] += 1
            result["correct_" + key + "_products"] += correct
    return {"n": n, "levels": levels, "fresh_error_bound": radius, "seed": seed,
            "samples": samples, "uniform_binary_key_draw": True,
            "first_raw_mask": "zero normalization; exact noise law independent of this mask",
            "second_raw_mask": "uniform", "source_resampled": False,
            "product_noise_identity_checks": identities,
            "short_digit_reconstruction_checks": reconstructions, "results": results}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = [experiment(n, radius, 256, 20261011 + n * 10 + radius)
             for n in (2, 4, 8, 16, 32, 64) for radius in (0, 1)]
    result = {"scope": "Native selected-column product scaling for unsigned and signed midpoint digits",
              "limitations": "Finite samples and a normalized first mask; no negligible-failure theorem or full larger-dimension refresh",
              "product_noise_identity_checks": sum(c["product_noise_identity_checks"] for c in cases),
              "short_digit_reconstruction_checks": sum(c["short_digit_reconstruction_checks"] for c in cases),
              "cases": cases}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
