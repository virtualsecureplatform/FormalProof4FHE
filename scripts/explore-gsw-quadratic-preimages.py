#!/usr/bin/env python3
"""Exhaustive two-coordinate exploration; not a polynomial-time construction.

Find short B for prescribed quadratic coefficients of s^T B A^T s modulo q,
then check the phase/error identity on every binary key and signed unit error.
This does not test cryptographic security or bootstrapping correctness.
"""

import argparse
import itertools
import json
from pathlib import Path
import random


def explore(q, samples, seed):
    rng = random.Random(seed)
    matrix = [[rng.randrange(q) for _ in range(samples)] for _ in range(2)]
    vectors = list(itertools.product((-1, 0, 1), repeat=samples))
    dots = [tuple(sum(a * b for a, b in zip(v, row)) % q for row in matrix)
            for v in vectors]
    witnesses = {}
    for ix, first in enumerate(vectors):
        for jx, second in enumerate(vectors):
            a, b = dots[ix]
            c, d = dots[jx]
            witnesses.setdefault((a, (b + c) % q, d), (first, second))

    records = []
    for weight in (1, 2, 4, 8):
        for first, second in ((0, 0), (0, 1), (1, 1)):
            target = ((weight % q, 0, 0) if first == second == 0 else
                      (0, 0, weight % q) if first == second == 1 else
                      (0, weight % q, 0))
            witness = witnesses.get(target)
            record = {"weight": weight, "indices": [first, second],
                      "found": witness is not None}
            if witness is not None:
                checked = 0
                for secret in itertools.product((0, 1), repeat=2):
                    for error in itertools.product((-1, 0, 1), repeat=samples):
                        body = [(sum(matrix[row][col] * secret[row]
                                     for row in range(2)) + error[col]) % q
                                for col in range(samples)]
                        phase = sum(secret[row] * sum(witness[row][col] * body[col]
                                                      for col in range(samples))
                                    for row in range(2)) % q
                        residual = sum(secret[row] * sum(witness[row][col] * error[col]
                                                         for col in range(samples))
                                       for row in range(2)) % q
                        if phase != (weight * secret[first] * secret[second] + residual) % q:
                            raise AssertionError("phase/error identity failed")
                        checked += 1
                record.update(B=[list(row) for row in witness], phase_checks=checked)
            records.append(record)
    return {"scope": "Exhaustive finite exploration, not security, efficient sampling, or bootstrap correctness",
            "q": q, "n": 2, "m": samples, "seed": seed, "A": matrix,
            "coefficient_classes_with_short_witness": len(witnesses),
            "possible_classes": q ** 3, "records": records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, default=17)
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--seed", type=int, default=417)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.q < 2 or not 1 <= args.samples <= 6:
        parser.error("q must be at least 2; the exhaustive diagnostic supports 1--6 samples")
    result = explore(args.q, args.samples, args.seed)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    records = result["records"]
    print(f"Short witnesses: {sum(row['found'] for row in records)}/{len(records)} targets")
    print(f"Exact phase/error checks: {sum(row.get('phase_checks', 0) for row in records)}")
    print("Exhaustive toy calculation; no security or scalable construction claim.")


if __name__ == "__main__":
    main()
