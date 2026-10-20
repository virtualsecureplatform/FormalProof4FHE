#!/usr/bin/env python3
"""Exact finite checks of midpoint product errors and their window masses.

Counts use integer arithmetic. The convolution calculation is separate from
the native product check; its general distributional connection is explained
mathematically in the research log, not claimed as a Lean probability proof.
"""
import argparse
from fractions import Fraction
import importlib.util
import itertools
import json
from pathlib import Path

import numpy as np

spec = importlib.util.spec_from_file_location(
    "midpoint", Path(__file__).with_name("try-gsw-correlated-midpoint.py"))
midpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(midpoint)
t = midpoint.transcript


def native_checks():
    q, levels, checked = 16, 4, 0
    g = t.gadget(2, levels)

    def control(secret, index, actual_mask):
        shift, constant = np.zeros((2, 12), dtype=np.int64), np.zeros(12, dtype=np.int64)
        for row in range(3):
            for ell in range(4):
                column, w = row * 4 + ell, 1 << ell
                if row == 0:
                    shift[index, column] = w
                else:
                    constant[column] = w // 4
                    shift[index, column] -= w // 2
                    shift[row - 1, column] -= w // 2
        raw = (actual_mask + shift) % q
        return np.vstack(((secret @ raw + constant) % q, actual_mask))

    for bits in itertools.product((0, 1), repeat=2):
        secret = np.array(bits, dtype=np.int64)
        for i, j in itertools.product(range(2), repeat=2):
            first = control(secret, i, np.zeros((2, 12), dtype=np.int64))
            for u, v in itertools.product(range(q), repeat=2):
                actual = np.zeros((2, 12), dtype=np.int64)
                actual[:, 3] = u, v
                second = control(secret, j, actual)
                product = first @ t.digits(second, levels) % q
                noise = int(t.phase(product, secret, q)[3] - bits[i] * bits[j] * 8) % q
                predicted = 0
                for k, value in enumerate((u, v)):
                    predicted += (1 - 2 * bits[i]) * (1 - 2 * bits[k]) * (value // 4)
                    predicted += bits[i] * bits[k] * (value % 2)
                    predicted -= (bits[i] != bits[k]) * ((value // 2) % 2)
                assert noise == predicted % q
                checked += 1
    return checked


def max_window(counts, length):
    q = len(counts)
    if length >= q:
        return sum(counts)
    current, best = sum(counts[:length]), sum(counts[:length])
    for start in range(1, q):
        current += counts[(start + length - 1) % q] - counts[start - 1]
        best = max(best, current)
    return best


def convolution_case(q, terms, dimension, radius):
    quarter = q // 4
    counts = [1] + [0] * (q - 1)
    for _ in range(terms):
        current = sum(counts[(-u) % q] for u in range(quarter))
        output = [current]
        for x in range(1, q):
            current += counts[x] - counts[(x - quarter) % q]
            output.append(current)
        counts = output
    total = quarter ** terms
    assert sum(counts) == total
    levels = q.bit_length() - 1
    perturbation = ((dimension + 1) * levels + 1) * radius
    length = min(q, q // 2 + 1 + 2 * perturbation)
    mass = Fraction(max_window(counts, length), total)
    tv = Fraction(sum(abs(q * c - total) for c in counts), 2 * q * total)
    return {"q": q, "quarter_terms": terms, "dimension": dimension,
            "fresh_error_bound": radius, "product_perturbation_bound": perturbation,
            "widened_decoding_window": length, "largest_window_probability": float(mass),
            "largest_window_probability_exact": str(mass), "tv_to_uniform": float(tv)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checked = native_checks()
    cases = [convolution_case(q, terms, terms, 0) for q in (64, 256, 1024)
             for terms in (2, 4, 8, 16, 32)]
    cases += [convolution_case(65536, terms, terms, 1) for terms in (16, 32)]
    args.output.write_text(json.dumps({"scope": "Exact finite product-law and quarter-convolution checks",
                                      "native_product_checks": checked, "cases": cases}, indent=2) + "\n")
    print(json.dumps({"native_product_checks": checked,
                      "convolution_cases": len(cases),
                      "bounded_noise_cases": [{k: c[k] for k in
                        ("q", "quarter_terms", "largest_window_probability")}
                        for c in cases if c["fresh_error_bound"]]}, sort_keys=True))


if __name__ == "__main__":
    main()
