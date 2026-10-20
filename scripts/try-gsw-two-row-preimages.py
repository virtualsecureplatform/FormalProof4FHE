#!/usr/bin/env python3
"""Exact two-target-row builder and public pair-decoding diagnostics.

Requires fpylll 0.6.4 and cysignals. Builders see only A and the target.
Uses power-of-two moduli, without matrix resampling or private trapdoors.
An elimination failure is recorded, not conditioned away. Toy instances do
not establish a useful asymptotic norm or a negligible failure probability.
"""

import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import random


spec = importlib.util.spec_from_file_location(
    "rowwise", Path(__file__).with_name("try-gsw-rowwise-preimages.py"))
rowwise = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rowwise)
remaining = rowwise.remaining


def pair_solver(a, q, first, second):
    n, m = len(a), len(a[0])
    # Diagonal and symmetric off-diagonal equations involving either row.
    pairs = [(i, j) for i, j in itertools.combinations_with_replacement(range(n), 2)
             if i in (first, second) or j in (first, second)]
    system = [[a[j][c] if r == i else a[i][c] if r == j else 0
               for r in (first, second) for c in range(m)] for i, j in pairs]
    solve = remaining.lattice_solver(system, q)

    def builder(weight):
        solution = solve([weight * int((i, j) == (first, second)) for i, j in pairs])
        b = [[0] * m for _ in range(n)]
        b[first], b[second] = solution[:m], solution[m:]
        target = [[weight * int((i, j) == (first, second)) % q for j in range(n)]
                  for i in range(n)]
        u = rowwise.certify(a, b, target, q)
        return b, u

    return builder


def run_case(n, m, q, seed):
    rng = random.Random(seed)
    a = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
    # Secret and errors are used exclusively by the diagnostic observer.
    bits = [rng.randrange(2) for _ in range(n)]
    error = [rng.choice((-1, 0, 1)) for _ in range(m)]
    body = [(sum(a[r][c] * bits[r] for r in range(n)) + error[c]) % q for c in range(m)]
    records, attacks, failures = [], [], []
    known = set()
    worst = None
    for first, second in itertools.combinations(range(n), 2):
        try:
            builder = pair_solver(a, q, first, second)
        except ValueError as exc:
            failures.append({"pair": [first, second], "failure": str(exc)})
            continue
        for level in range(q.bit_length() - 1):
            weight = 1 << level
            b, u = builder(weight)
            norm = rowwise.l1(b)
            record = {"pair": [first, second], "level": level, "weight": weight, "l1": norm}
            records.append(record)
            if worst is None or norm > worst["l1"]:
                worst = {**record, "B": b, "U": u}
            if weight != q // 2:
                continue
            c = sum(x * y for x, y in zip(b[first], a[second])) % q
            d = sum(x * y for x, y in zip(b[second], a[first])) % q
            assert (c + d) % q == weight
            for index, other, coefficient in [(first, second, c), (second, first, d)]:
                assert all(sum(x * y for x, y in zip(row, b[index])) % q ==
                           coefficient * int(r == other) for r, row in enumerate(a))
            rows = [sum(map(abs, b[index])) for index in (first, second)]
            distances = [abs(remaining.centered(x, q)) for x in (c, d)]
            guaranteed = [2 * h < dist for h, dist in zip(rows, distances)]
            assert not 4 * norm < q // 2 or any(guaranteed)
            observed = []
            for k, (index, other, coefficient) in enumerate([(first, second, c), (second, first, d)]):
                if not guaranteed[k]:
                    continue
                projection = sum(x * y for x, y in zip(b[index], body)) % q
                guess = int(abs(remaining.centered(projection - coefficient, q)) <
                            abs(remaining.centered(projection, q)))
                assert guess == bits[other]
                known.add(other)
                observed.append({"row": index, "coordinate": other, "guess": guess})
            attacks.append({"pair": [first, second], "weights": [c, d], "row_l1": rows,
                            "code_distances": distances, "unit_error_guaranteed": guaranteed,
                            "sufficient_total_norm_margin": 4 * norm < q // 2,
                            "observed": observed, "B": b, "U": u})
    all_pairs = not failures and all(any(a["unit_error_guaranteed"]) for a in attacks)
    verification = None
    if all_pairs:
        assert len(known) >= n - 1
        observations = {o["coordinate"]: o["guess"] for attack in attacks for o in attack["observed"]}
        completions = [[observations.get(i, fallback) for i in range(n)] for fallback in (0, 1)]
        assert bits in completions
        # A fresh verification row is independent of all earlier observations.
        mask = [rng.randrange(q) for _ in range(n)]
        verification_error = rng.choice((-1, 0, 1))
        real_body = (sum(s * x for s, x in zip(bits, mask)) + verification_error) % q
        shifts = [sum(s * x for s, x in zip(candidate, mask)) % q for candidate in completions]

        def accepts(value):
            return any(abs(remaining.centered(value - shift, q)) <= 1 for shift in shifts)

        assert accepts(real_body)
        accepted = sum(accepts(value) for value in range(q))
        assert accepted <= 2 * (2 * 1 + 1)
        verification = {"completions": completions, "mask": mask,
                        "real_body_accepted": True, "uniform_bodies_accepted": accepted,
                        "uniform_body_count": q, "uniform_acceptance_count_bound": 6}
    return {"n": n, "m": m, "q": q, "seed": seed, "A": a,
            "lattice_dimension": 2 * m, "constraints_per_pair": 2 * n - 1,
            "targets_checked": len(records), "failures": failures,
            "worst_witness": worst, "records": records, "pair_attacks": attacks,
            "known_coordinates": sorted(known), "missing_coordinates": sorted(set(range(n)) - known),
            "all_pairs_guaranteed": all_pairs, "fresh_verification": verification}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    results = []
    for k, (n, m, q) in enumerate([(2, 8, 256), (4, 16, 256), (4, 16, 65536),
                                   (8, 8, 256), (8, 8, 65536), (8, 32, 65536)]):
        result = run_case(n, m, q, 517 + k)
        results.append(result)
        print({"n": n, "m": m, "q": q, "targets": result["targets_checked"],
               "failures": len(result["failures"]),
               "worst_l1": None if result["worst_witness"] is None else result["worst_witness"]["l1"],
               "known": result["known_coordinates"]}, flush=True)
    args.output.write_text(json.dumps({"scope": "Finite exact algebra and unit-error attack diagnostics",
                                      "cases": results}, indent=2) + "\n")


if __name__ == "__main__":
    main()
