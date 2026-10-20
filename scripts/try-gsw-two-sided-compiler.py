#!/usr/bin/env python3
"""Public two-sided quadratic preimage and same-secret refresh diagnostics.

Requires numpy, fpylll 0.6.4 and cysignals. The builder sees A1,A2 and public
targets, never the secret or errors. No source resampling or private trapdoor.
Finite successes do not establish a secure asymptotic parameter family.
"""

import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import random

import numpy as np

spec = importlib.util.spec_from_file_location(
    "transcript", Path(__file__).with_name("try-gsw-transcript-routes.py"))
transcript = importlib.util.module_from_spec(spec)
spec.loader.exec_module(transcript)
remaining = transcript.remaining
centered = remaining.centered


def coefficient_system(a, b, q, free_diagonal=False):
    pairs = list(itertools.combinations_with_replacement(range(len(a)), 2))
    if free_diagonal:
        pairs = [pair for pair in pairs if pair[0] != pair[1]]
    system = [[(a[i][c] * b[j][d] + (a[j][c] * b[i][d] if i != j else 0)) % q
               for c in range(len(a[0])) for d in range(len(b[0]))] for i, j in pairs]
    return pairs, system


def experiment(n, p, r, levels, radius, seed, free_diagonal=False):
    rng, q = random.Random(seed), 1 << levels
    a = [[rng.randrange(q) for _ in range(p)] for _ in range(n)]
    b = [[rng.randrange(q) for _ in range(r)] for _ in range(n)]
    secret = np.array([rng.randrange(2) for _ in range(n)], dtype=np.int64)
    e = np.array([rng.randint(-radius, radius) for _ in range(p)], dtype=np.int64)
    f = np.array([rng.randint(-radius, radius) for _ in range(r)], dtype=np.int64)
    first, second = np.array(a, dtype=np.int64), np.array(b, dtype=np.int64)
    y1, y2 = (secret @ first + e) % q, (secret @ second + f) % q
    source_a, source_y = np.hstack((first, second)), np.concatenate((y1, y2))
    pairs, system = coefficient_system(a, b, q, free_diagonal)
    result = {"n": n, "p1": p, "p2": r, "q": q, "levels": levels,
              "radius": radius, "seed": seed, "source_resampled": False,
              "free_diagonal": free_diagonal,
              "diagnostic_secret_hamming_weight": int(secret.sum()),
              "constraints": len(pairs), "lattice_dimension": p * r,
              "public_linear_recovery_filter": []}
    try:
        solve = remaining.lattice_solver(system, q)
    except ValueError as exc:
        result["failure"] = str(exc)
        return result
    # Observer's PUBLIC recovery diagnostic: only A,y are used by this solver.
    try:
        linear = remaining.lattice_solver(source_a.tolist(), q)
        for index in range(n):
            preimage = linear([q // 2 * int(index == row) for row in range(n)])
            observed = sum(int(x) * int(y) for x, y in zip(preimage, source_y)) % q
            guess = int(abs(centered(observed - q // 2, q)) < abs(centered(observed, q)))
            norm = sum(map(abs, preimage))
            result["public_linear_recovery_filter"].append({
                "coordinate": index, "l1": norm,
                "worst_case_margin": 4 * radius * norm < q,
                "sample_guess_correct": bool(guess == secret[index])})
    except ValueError as exc:
        result["public_linear_recovery_filter"].append({"failure": str(exc)})
    width = (n + 1) * levels
    g = transcript.gadget(n, levels)
    raw_masks = np.array([[[rng.randrange(q) for _ in range(width)] for _ in range(n)]
                          for _ in range(n)], dtype=np.int64)
    fresh_errors = np.array([[rng.randint(-radius, radius) for _ in range(width)]
                             for _ in range(n)], dtype=np.int64)
    controls, records, cache = [], [], {}
    for index in range(n):
        h = np.zeros((n, width), dtype=np.int64)
        c = np.zeros(width, dtype=np.int64)
        residual = np.zeros(width, dtype=np.int64)
        for row in range(n + 1):
            for level in range(levels):
                column, weight = row * levels + level, 1 << level
                if row == 0:
                    h[index, column] = weight
                elif row - 1 == index:
                    h[index, column] = -weight
                else:
                    other = row - 1
                    pair = tuple(sorted((index, other)))
                    key = pair, level
                    if key not in cache:
                        # Positive two-sided product produces the negative native phase.
                        target = [weight * int(ij == pair) for ij in pairs]
                        vector = solve(target)
                        cache[key] = np.array(vector, dtype=np.int64).reshape(p, r)
                    d = cache[key]
                    product = (first @ d % q) @ second.T % q
                    target_matrix = np.zeros((n, n), dtype=np.int64)
                    target_matrix[index, other] = weight
                    difference = (product - target_matrix) % q
                    if free_diagonal:
                        difference = (difference - np.diag(np.diag(product))) % q
                    witness = np.triu(difference, 1)
                    assert np.array_equal(difference, (witness - witness.T) % q)
                    # Intermediate reductions avoid int64 overflow at larger q.
                    h[:, column] = (-(first @ d % q) @ y2 -
                                    (second @ d.T % q) @ y1) % q
                    if free_diagonal:
                        h[:, column] = (h[:, column] + np.diag(product)) % q
                    c[column] = int((y1 @ d % q) @ y2) % q
                    residual[column] = int(e @ d @ f) % q
                    x1, x2 = secret @ first % q, secret @ second % q
                    uncancelled = int((x1 @ d % q) @ f + (e @ d % q) @ x2) % q
                    assert (int(c[column]) + int(secret @ h[:, column]) +
                            weight * int(secret[index]) * int(secret[other]) -
                            int(residual[column])) % q == 0
                    norm = int(np.abs(d).sum())
                    assert abs(centered(int(residual[column]), q)) <= radius * radius * norm
                    records.append({"control": index, "other": other, "level": level,
                                    "d_l1": norm, "actual_bilinear_residual": centered(int(residual[column]), q),
                                    "uncancelled_first_order_term": centered(uncancelled, q),
                                    "contracted_first_l1": sum(abs(centered(int(v), q)) for v in (first @ d % q).flat)})
        masks = (raw_masks[index] - h) % q
        bodies = (secret @ raw_masks[index] + fresh_errors[index] + c) % q
        control = np.vstack((bodies, masks))
        assert transcript.noise(control, secret[index], secret, g, q) == [
            centered(int(x), q) for x in (fresh_errors[index] + residual) % q]
        controls.append(control)
    control_bound = max(abs(x) for i, ct in enumerate(controls)
                        for x in transcript.noise(ct, secret[i], secret, g, q))
    lookup = 1 << (4 * (n + 1)).bit_length()
    public_key = np.vstack((source_y, source_a))
    initial = [(public_key @ np.array([[rng.randrange(2) for _ in range(width)]
                                      for _ in range(p + r)], dtype=np.int64) + bit * g) % q
               for bit in (0, 1)]
    current, refresh_trials = [ct.copy() for ct in initial], []
    for cycle in range(3):
        next_ciphertexts = []
        for bit in (0, 1):
            if cycle:
                before = (g - current[bit] @ transcript.digits(initial[0], levels)) % q
                message = 1
            else:
                before, message = current[bit], bit
            after = transcript.refresh(before, controls, levels, q, lookup)
            input_bound = max(map(abs, transcript.noise(before, message, secret, g, q)))
            output_bound = max(map(abs, transcript.noise(after, message, secret, g, q)))
            out_phase = int(transcript.phase(after, secret, q)[levels - 1])
            decoded = int(abs(centered(out_phase - q // 2, q)) < abs(centered(out_phase, q)))
            refresh_trials.append({"cycle": cycle, "input_branch": bit, "expected": message,
                                   "decoded": decoded, "correct": decoded == message,
                                   "input_noise": input_bound, "output_noise": output_bound,
                                   "input_rounding_margin": 2 * (input_bound + (n + 1) * (q // lookup - 1)) < q // 2,
                                   "output_decoding_margin": 4 * output_bound < q,
                                   "next_nand_rounding_margin": 2 * ((width + 1) * output_bound +
                                       (n + 1) * (q // lookup - 1)) < q // 2})
            next_ciphertexts.append(after)
        current = next_ciphertexts
    result.update(certificates_checked=len(records), full_control_phase_checks=n * width,
                  max_d_l1=max(r["d_l1"] for r in records),
                  max_bilinear_residual=max(abs(r["actual_bilinear_residual"]) for r in records),
                  max_uncancelled_first_order_term=max(abs(r["uncancelled_first_order_term"]) for r in records),
                  max_contracted_first_l1=max(r["contracted_first_l1"] for r in records),
                  max_control_noise=control_bound, lookup=lookup,
                  worst_case_control_bound=radius + radius * radius * max(r["d_l1"] for r in records),
                  triangle_refresh_bound=lookup * n * width * control_bound,
                  refresh_trials=refresh_trials, records=records)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = {"scope": "Finite construction and operation diagnostics only; no secure parameter-family claim",
              "builder": "Public dense tensor-coefficient LLL/Babai; exact alternating certificates",
              "cases": [], "stress_cases": []}
    cases = [(2, 2, 2, 8, 1), (3, 3, 3, 12, 1), (4, 4, 4, 16, 1),
             (4, 8, 8, 16, 1), (4, 4, 4, 24, 1), (4, 8, 8, 24, 1),
             (4, 8, 8, 24, 64), (8, 8, 8, 24, 1)]
    for seed, parameters in enumerate(cases, start=10011):
        for free_diagonal in (False, True):
            record = experiment(*parameters, seed, free_diagonal)
            result["cases"].append(record)
            print({"case": [*parameters, seed], "free_diagonal": free_diagonal,
                   "failure": record.get("failure"), "key_weight": record["diagnostic_secret_hamming_weight"],
                   "d_l1": record.get("max_d_l1"), "control_noise": record.get("max_control_noise"),
                   "correct": sum(r["correct"] for r in record.get("refresh_trials", [])),
                   "reusable_margin": sum(r["next_nand_rounding_margin"] for r in record.get("refresh_trials", []))}, flush=True)
            args.output.write_text(json.dumps(result, indent=2) + "\n")
    # Keep the seed-10017 public matrix geometry and key, while increasing the
    # source-noise radius beyond the displayed public linear recovery margins.
    # This is an additional diagnostic, not source rejection or resampling.
    for radius in (32768, 262144):
        stress = experiment(4, 8, 8, 24, radius, 10017, True)
        result["stress_cases"].append(stress)
        print({"noise_stress_seed": 10017, "radius": radius, "failure": stress.get("failure"),
               "control_noise": stress.get("max_control_noise"),
               "correct": sum(r["correct"] for r in stress.get("refresh_trials", [])),
               "reusable_margin": sum(r["next_nand_rounding_margin"] for r in stress.get("refresh_trials", []))}, flush=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
