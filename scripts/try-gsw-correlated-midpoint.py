#!/usr/bin/env python3
"""Test public midpoint corrections and their correlated native errors.

The correction coefficients are public constants. Source errors, masks and
uniform binary secrets are drawn once. No correctness-conditioned resampling
is performed. These finite refresh trials do not establish a security theorem.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import random

import numpy as np

spec = importlib.util.spec_from_file_location(
    "transcript", Path(__file__).with_name("try-gsw-transcript-routes.py"))
transcript = importlib.util.module_from_spec(spec)
spec.loader.exec_module(transcript)


def experiment(n, levels, radius, seed, variant):
    rng, q = random.Random(seed), 1 << levels
    secret = np.array([rng.randrange(2) for _ in range(n)], dtype=np.int64)
    m = (n + 1) * levels + 80
    a = np.array([[rng.randrange(q) for _ in range(m)] for _ in range(n)], dtype=np.int64)
    e = np.array([rng.randint(-radius, radius) for _ in range(m)], dtype=np.int64)
    source = np.vstack(((secret @ a + e) % q, a))
    g = transcript.gadget(n, levels)
    width, controls, residuals = g.shape[1], [], []
    for i in range(n):
        raw = np.array([[rng.randrange(q) for _ in range(width)] for _ in range(n)], dtype=np.int64)
        fresh = np.array([rng.randint(-radius, radius) for _ in range(width)], dtype=np.int64)
        h, c, delta = np.zeros_like(raw), np.zeros(width, dtype=np.int64), np.zeros(width, dtype=np.int64)
        for row in range(n + 1):
            for level in range(levels):
                column, w = row * levels + level, 1 << level
                if row == 0:
                    h[i, column] = w
                elif row - 1 == i and variant == "exact_diagonal":
                    h[i, column] = -w
                else:
                    j = row - 1
                    c[column] = w // 4
                    h[i, column] -= w // 2
                    h[j, column] -= w // 2
                    delta[column] = (c[column] + secret @ h[:, column] + w * secret[i] * secret[j]) % q
                    if level >= 2:
                        assert delta[column] == (w // 4 * (1 - 2 * secret[i]) * (1 - 2 * secret[j])) % q
        control = np.vstack(((secret @ raw + fresh + c) % q, (raw - h) % q))
        assert transcript.noise(control, secret[i], secret, g, q) == [
            transcript.centered(int(x), q) for x in (fresh + delta) % q]
        controls.append(control)
        residuals.append(delta)
    initial = [(source @ np.array([[rng.randrange(2) for _ in range(width)] for _ in range(m)],
                                  dtype=np.int64) + bit * g) % q for bit in (0, 1)]
    lookup = 1 << (4 * (n + 1)).bit_length()
    result = {"n": n, "levels": levels, "source_radius": radius, "seed": seed,
              "variant": variant, "uniform_binary_key_draw": True, "source_resampled": False,
              "secret_for_diagnostic": [int(x) for x in secret], "phase_checks": n * width,
              "max_compiler_residual": max(abs(transcript.centered(int(x), q))
                                            for row in residuals for x in row),
              "refresh_trials": []}
    assert result["max_compiler_residual"] == q // 8
    current = [c.copy() for c in initial]
    for cycle in range(3):
        output = []
        for branch in (0, 1):
            before = current[branch] if cycle == 0 else (
                g - current[branch] @ transcript.digits(initial[0], levels)) % q
            expected = branch if cycle == 0 else 1
            after = transcript.refresh(before, controls, levels, q, lookup)
            input_bound = max(map(abs, transcript.noise(before, expected, secret, g, q)))
            output_bound = max(map(abs, transcript.noise(after, expected, secret, g, q)))
            phase = int(transcript.phase(after, secret, q)[levels - 1])
            decoded = int(abs(transcript.centered(phase - q // 2, q)) < abs(transcript.centered(phase, q)))
            result["refresh_trials"].append({"cycle": cycle, "branch": branch,
                "correct": decoded == expected, "input_noise": input_bound, "output_noise": output_bound,
                "input_rounding_margin": 2 * (input_bound + (n + 1) * (q // lookup - 1)) < q // 2,
                "output_decoding_margin": 4 * output_bound < q,
                "next_nand_rounding_margin": 2 * ((width + 1) * output_bound +
                                                  (n + 1) * (q // lookup - 1)) < q // 2})
            output.append(after)
        current = output
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    params = [(2, 16, 0), (2, 16, 1), (2, 16, 64), (3, 24, 1),
              (3, 24, 64), (4, 24, 1), (4, 24, 64)]
    cases = [experiment(*p, 14000 + 10 * index + repeat, variant)
             for index, p in enumerate(params) for repeat in range(4)
             for variant in ("exact_diagonal", "full_signed_outer_product")]
    trials = [t for c in cases for t in c["refresh_trials"]]
    totals = {"cases": len(cases), "phase_checks": sum(c["phase_checks"] for c in cases),
              "refresh_calls": len(trials), "selected_correct": sum(t["correct"] for t in trials),
              "output_margins": sum(t["output_decoding_margin"] for t in trials),
              "next_nand_margins": sum(t["next_nand_rounding_margin"] for t in trials)}
    args.output.write_text(json.dumps({"scope": "Correlated public midpoint-error correctness diagnostics",
                                      "totals": totals, "cases": cases}, indent=2) + "\n")
    print(json.dumps(totals, sort_keys=True))


if __name__ == "__main__":
    main()
