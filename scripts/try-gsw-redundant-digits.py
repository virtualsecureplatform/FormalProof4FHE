#!/usr/bin/env python3
"""Try public signed digits minimizing four midpoint residual patterns.

All choices use only the input ciphertext and modulus. Source/control draws
match the previous midpoint trials exactly. The executable compares actual
NAND/refresh/next-refresh cycles, with no secret-dependent digit choices.
"""
import argparse
import importlib.util
import itertools
import json
from pathlib import Path

import numpy as np

spec = importlib.util.spec_from_file_location(
    "midpoint_redundant", Path(__file__).with_name("try-gsw-correlated-midpoint.py"))
midpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(midpoint)
unsigned = midpoint.transcript.digits


def signed_quarter_digits(ciphertext, levels):
    """Minimize max(|H|,|-H-b|,|H+a|), subject to x=a+2b+4H mod q.

Low digits a,b are in {-1,0,1}; H uses signed magnitude binary digits.
Both canonical lifts x and x-q are examined. Every output digit is short.
"""
    assert levels >= 3
    q = 1 << levels
    values = np.asarray(ciphertext, dtype=np.int64) % q
    best = np.full_like(values, q * q)
    best_tie = np.full_like(values, q * q)
    low_a, low_b, high = (np.zeros_like(values) for _ in range(3))
    for lift in (values, values - q):
        for a, b in itertools.product((-1, 0, 1), repeat=2):
            h = (lift - a - 2 * b) // 4
            score = np.maximum(np.abs(h), np.maximum(np.abs(-h - b), np.abs(h + a)))
            tie = np.abs(h) + abs(a) + abs(b)
            take = ((lift - a - 2 * b) % 4 == 0) & (
                (score < best) | ((score == best) & (tie < best_tie)))
            best = np.where(take, score, best)
            best_tie = np.where(take, tie, best_tie)
            low_a, low_b = np.where(take, a, low_a), np.where(take, b, low_b)
            high = np.where(take, h, high)
    assert np.all(best < q * q)
    return np.vstack([digit for row in range(len(values))
                      for digit in [low_a[row], low_b[row], *[
                          np.sign(high[row]) * ((np.abs(high[row]) >> k) & 1)
                          for k in range(levels - 2)]]])


def finite_checks():
    entries = corners = lower_bound_cases = 0
    for levels in range(3, 10):
        q = 1 << levels
        values = np.arange(q, dtype=np.int64).reshape(1, q)
        d = signed_quarter_digits(values, levels)
        weights = np.array([1 << k for k in range(levels)], dtype=np.int64)
        assert np.array_equal((weights @ d) % q, values[0])
        assert np.max(np.abs(d)) <= 1
        entries += q
        for column, value in enumerate(values[0]):
            residues = []
            for a, b in itertools.product((0, 1), repeat=2):
                error = sum((w // 4 - (w // 2) * (a + b) + w * a * b) * digit
                            for w, digit in zip(weights, d[:, column])) % q
                residues.append(int(error))
                corners += 1
            assert (residues[3] - residues[2] - residues[1] + residues[0]) % q == value
            target_size = abs(midpoint.transcript.centered(int(value), q))
            worst = max(abs(midpoint.transcript.centered(error, q)) for error in residues)
            assert target_size <= 4 * worst
            lower_bound_cases += 1
    return {"scalar_reconstruction_checks": entries,
            "scalar_midpoint_corner_checks": corners,
            "scalar_four_corner_lower_bound_checks": lower_bound_cases}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    totals = finite_checks()
    counters = {"digit_calls": 0, "reconstructed_entries": 0}

    def checked_signed(ciphertext, levels):
        result = signed_quarter_digits(ciphertext, levels)
        q = 1 << levels
        g = midpoint.transcript.gadget(len(ciphertext) - 1, levels)
        assert np.array_equal((g @ result) % q, np.asarray(ciphertext) % q)
        assert np.max(np.abs(result)) <= 1
        counters["digit_calls"] += 1
        counters["reconstructed_entries"] += int(np.asarray(ciphertext).size)
        return result

    params = [(2, 16, 0), (2, 16, 1), (2, 16, 64), (3, 24, 1),
              (3, 24, 64), (4, 24, 1), (4, 24, 64)]
    cases = []
    for policy, decompose in (("unsigned", unsigned), ("signed_quarter_minimax", checked_signed)):
        midpoint.transcript.digits = decompose
        for index, param in enumerate(params):
            for repeat in range(4):
                for variant in ("exact_diagonal", "full_signed_outer_product"):
                    case = midpoint.experiment(*param, 14000 + 10 * index + repeat, variant)
                    case["digit_policy"] = policy
                    cases.append(case)
    midpoint.transcript.digits = unsigned
    summaries = []
    for policy in ("unsigned", "signed_quarter_minimax"):
        selected = [case for case in cases if case["digit_policy"] == policy]
        trials = [trial for case in selected for trial in case["refresh_trials"]]
        summaries.append({"digit_policy": policy, "cases": len(selected),
                          "phase_checks": sum(case["phase_checks"] for case in selected),
                          "refresh_calls": len(trials), "selected_correct": sum(t["correct"] for t in trials),
                          "output_margins": sum(t["output_decoding_margin"] for t in trials),
                          "next_nand_margins": sum(t["next_nand_rounding_margin"] for t in trials),
                          "all_six_selected_correct_cases": sum(all(t["correct"] for t in c["refresh_trials"])
                                                                  for c in selected)})
    result = {"scope": "Public signed redundant digits with existing midpoint controls",
              "limitations": "Fixed finite correctness diagnostics; no secure parameter family or LWE theorem",
              "finite_checks": totals, "signed_reconstruction_checks": counters,
              "summaries": summaries, "cases": cases}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("finite_checks", "signed_reconstruction_checks", "summaries")},
                     sort_keys=True))


if __name__ == "__main__":
    main()
