#!/usr/bin/env python3
"""Signed-source/trace extraction checks; not a secure parameter experiment.

The preimage solver receives only the transformed public matrices and targets.
Requires the same numpy/fpylll dependencies as try-gsw-two-sided-compiler.py.
"""

import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import random

import numpy as np

spec = importlib.util.spec_from_file_location(
    "two_sided", Path(__file__).with_name("try-gsw-two-sided-compiler.py"))
two_sided = importlib.util.module_from_spec(spec)
spec.loader.exec_module(two_sided)
centered = two_sided.centered


def uniformization_checks():
    checks = []
    for q in (2, 4, 8, 16, 32, 64, 3, 5, 17):
        counts = Counter((2 * body + coin) % q
                         for body in range(q) for coin in (0, 1))
        assert set(counts) == set(range(q))
        assert all(count == 2 for count in counts.values())
        checks.append({"q": q, "input_pairs": 2 * q,
                       "preimages_per_output": 2})
    # At an even modulus omitting the parity coin does NOT preserve uniformity.
    assert len({(2 * body) % 16 for body in range(16)}) == 8
    return checks


def experiment(n, p, r, levels, radius, seed):
    rng, q = random.Random(seed), 1 << levels
    masks = np.array([[rng.randrange(q) for _ in range(p + r)]
                      for _ in range(n)], dtype=np.int64)
    bits = np.array([rng.randrange(2) for _ in range(n)], dtype=np.int64)
    error = np.array([rng.randint(-radius, radius) for _ in range(p + r)], dtype=np.int64)
    coins = np.array([rng.randrange(2) for _ in range(p + r)], dtype=np.int64)
    body = (bits @ masks + error) % q
    # This transformation is public and does not use bits or error.
    lifted = np.vstack(((2 * body - masks.sum(axis=0) + coins) % q, masks))
    first, second = lifted[:, :p], lifted[:, p:]
    signed = np.concatenate(([1], 1 - 2 * bits))
    lifted_error = 2 * error + coins
    assert np.all(signed * signed == 1)
    assert np.array_equal(signed @ lifted % q, lifted_error % q)
    pairs, system = two_sided.coefficient_system(
        first.tolist(), second.tolist(), q, free_diagonal=True)
    result = {"n_source": n, "n_builder": n + 1, "p1": p, "p2": r,
              "q": q, "radius": radius, "seed": seed,
              "source_resampled": False, "free_diagonal": True,
              "source_hamming_weight": int(bits.sum()), "targets": []}
    try:
        solve = two_sided.remaining.lattice_solver(system, q)
    except ValueError as exc:
        result["failure"] = str(exc)
        return result
    weight = q // 4
    for index in range(n):
        pair = (0, index + 1)
        vector = solve([weight * int(ij == pair) for ij in pairs])
        d = np.array(vector, dtype=np.int64).reshape(p, r)
        product = ((first @ d % q) @ second.T) % q
        target = np.zeros((n + 1, n + 1), dtype=np.int64)
        target[index + 1, 0] = weight
        diagonal = np.diag(np.diag(product))
        difference = (product - target - diagonal) % q
        witness = np.triu(difference, 1)
        assert np.array_equal(difference, (witness - witness.T) % q)
        # Use Python integers to avoid overflow even in stress cases.
        residual = sum(int(lifted_error[c]) * int(d[c, j]) *
                       int(lifted_error[p + j])
                       for c in range(p) for j in range(r))
        norm = sum(abs(centered(int(value), q)) for value in d.flat)
        bound = (2 * radius + 1) ** 2 * norm
        assert abs(centered(residual, q)) <= bound
        trace = int(np.trace(product)) % q
        observed = (trace + weight) % q
        assert observed == (2 * weight * int(bits[index]) + residual) % q
        guess = int(abs(centered(observed - 2 * weight, q)) <
                    abs(centered(observed, q)))
        margin = 2 * bound < q // 2
        if margin:
            assert guess == bits[index]
        result["targets"].append({"coordinate": index, "l1": norm,
                                  "trace": trace,
                                  "bilinear_residual": centered(residual, q),
                                  "worst_case_bound": bound,
                                  "guaranteed_margin": margin,
                                  "guess_correct": bool(guess == bits[index])})
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parameters = [(3, 8, 8, 16, 1), (3, 8, 8, 24, 1),
                  (3, 8, 8, 24, 64), (3, 8, 8, 24, 32768),
                  (4, 8, 8, 24, 1), (4, 8, 8, 24, 64),
                  (2, 4, 4, 12, 1), (2, 4, 4, 24, 1)]
    cases = [experiment(*params, 11001 + index)
             for index, params in enumerate(parameters)]
    targets = [target for case in cases for target in case["targets"]]
    result = {"scope": "finite signed-source algebra and extraction checks, not a security theorem",
              "uniformization": uniformization_checks(), "cases": cases,
              "totals": {"attempts": len(cases),
                         "solver_failures": sum("failure" in case for case in cases),
                         "certificates_and_trace_identities": len(targets),
                         "guaranteed_recovered_bits": sum(t["guaranteed_margin"] for t in targets),
                         "observed_correct_bits": sum(t["guess_correct"] for t in targets)}}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["totals"], sort_keys=True))


if __name__ == "__main__":
    main()
