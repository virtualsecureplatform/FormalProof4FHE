#!/usr/bin/env python3
"""Exact finite coupling and convolution bounds for signed midpoint digits.

The general probability argument connecting them is in the research log.
This executable uses integer counts and rational bounds, not floating FFTs.
"""
import argparse
from fractions import Fraction
import importlib.util
import json
from pathlib import Path

import numpy as np

spec = importlib.util.spec_from_file_location(
    "signed_law_redundant", Path(__file__).with_name("try-gsw-redundant-digits.py"))
redundant = importlib.util.module_from_spec(spec)
spec.loader.exec_module(redundant)


def coupling_checks():
    good = exceptional = 0
    for levels in range(3, 13):
        q, quarter = 1 << levels, 1 << (levels - 2)
        values = np.arange(q, dtype=np.int64).reshape(1, q)
        d = redundant.signed_quarter_digits(values, levels)
        high = np.array([1 << k for k in range(levels - 2)], dtype=np.int64) @ d[2:]
        u = values[0] // 4
        centered = np.where(u < quarter // 2, u, u - quarter)
        regular = u != quarter // 2
        assert np.all(np.abs(high[regular] - centered[regular]) <= 1)
        low = values[0] % 4
        expected_high = centered + ((low == 3) | (((low == 1) | (low == 2)) & (centered < 0)))
        expected_a = np.where(low == 1, np.where(centered >= 0, 1, -1), np.where(low == 3, -1, 0))
        expected_b = np.where(low == 2, np.where(centered >= 0, 1, -1),
                              np.where((low == 1) & (centered < 0), -1, 0))
        assert np.array_equal(high[regular], expected_high[regular])
        assert np.array_equal(d[0, regular], expected_a[regular])
        assert np.array_equal(d[1, regular], expected_b[regular])
        assert np.sum(~regular) == 4
        good += int(np.sum(regular))
        exceptional += 4
    return {"regular_scalar_couplings": good, "exceptional_scalars": exceptional,
            "explicit_digit_case_table_checks": good,
            "coupled_high_digit_distance": 1, "exception_probability_per_scalar": "1/(q/4)",
            "levels_checked": list(range(3, 13))}


def max_window(counts, length):
    q = len(counts)
    if length >= q:
        return sum(counts)
    current = best = sum(counts[:length])
    for start in range(1, q):
        current += counts[(start + length - 1) % q] - counts[start - 1]
        best = max(best, current)
    return best


def bounds():
    q, levels, quarter = 65536, 16, 16384
    counts, cases = [1] + [0] * (q - 1), []
    for terms in range(1, 65):
        current = sum(counts[(-u) % q] for u in range(quarter))
        output = [current]
        for x in range(1, q):
            current += counts[x] - counts[(x - quarter) % q]
            output.append(current)
        counts = output
        if terms not in (16, 32, 64):
            continue
        total = quarter ** terms
        assert sum(counts) == total
        for radius in (0, 1):
            perturbation = 3 * terms + ((terms + 1) * levels + 1) * radius
            length = min(q, q // 2 + 1 + 2 * perturbation)
            mass = Fraction(max_window(counts, length), total)
            exceptional = Fraction(terms, quarter)
            bound = min(Fraction(1), mass + exceptional)
            cases.append({"q": q, "n": terms, "fresh_error_bound": radius,
                          "bounded_perturbation": perturbation,
                          "window_length": length, "largest_quarter_convolution_window_mass": float(mass),
                          "coupling_exception_bound_exact": str(exceptional),
                          "selected_product_correctness_upper_bound": float(bound),
                          "selected_product_correctness_upper_bound_exact": str(bound)})
    return cases


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = {"scope": "Exact finite signed-digit coupling checks and quarter-convolution window bounds",
              "limitations": "The general coupling/product probability argument is mathematical, not Lean-checked",
              "coupling": coupling_checks(), "cases": bounds()}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"coupling": result["coupling"], "bounds": [
        {key: c[key] for key in ("q", "n", "fresh_error_bound", "selected_product_correctness_upper_bound")}
        for c in result["cases"]]}, sort_keys=True))


if __name__ == "__main__":
    main()
