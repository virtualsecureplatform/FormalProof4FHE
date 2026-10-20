#!/usr/bin/env python3
"""Prefix-lattice builder attempts and attack filters; not FHE parameters.

Dependencies: fpylll 0.6.4, cysignals. Reuses exact modular kernel/Babai code
from try-gsw-remaining-routes.py. No source matrix resampling or secret input
is used in any builder. All returned certificates are checked exactly.
"""

import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random


spec = importlib.util.spec_from_file_location(
    "remaining", Path(__file__).with_name("try-gsw-remaining-routes.py"))
remaining = importlib.util.module_from_spec(spec)
spec.loader.exec_module(remaining)


def rowwise_solver(a, q, mode):
    n = len(a)
    solvers = [remaining.lattice_solver(a[:i + 1], q) for i in range(n)]
    nulls = sorted(solvers[0].kernel_basis(), key=lambda v: sum(map(abs, v)))
    assert all(any(v) and sum(x * y for x, y in zip(a[0], v)) % q == 0 for v in nulls)

    def solve(target):
        rows = []
        for i in range(n):
            rhs = [(target[i][j] + target[j][i] -
                    sum(x * y for x, y in zip(rows[j], a[i]))) % q
                   for j in range(i)] + [target[i][i] % q]
            vector = solvers[i](rhs)
            if i == 0 and mode != "zero":
                selected = 0
                if mode == "target_dependent" and any(any(row) for row in target):
                    encoded = json.dumps(target, separators=(",", ":")).encode()
                    selected = 1 + hashlib.sha256(encoded).digest()[0] % max(1, len(nulls) // 2 - 1)
                vector = [x + z for x, z in zip(vector, nulls[selected])]
            rows.append(vector)
        certify(a, rows, target, q)
        return rows

    return solve, solvers[-1]


def certify(a, b, target, q):
    n = len(a)
    product = [[sum(x * y for x, y in zip(b[i], a[j])) % q
                for j in range(n)] for i in range(n)]
    difference = [[(product[i][j] - target[i][j]) % q for j in range(n)] for i in range(n)]
    u = [[difference[i][j] if i < j else 0 for j in range(n)] for i in range(n)]
    assert all((difference[i][j] - u[i][j] + u[j][i]) % q == 0
               for i in range(n) for j in range(n))
    return u


def l1(matrix):
    return sum(abs(x) for row in matrix for x in row)


def run_case(n, m, q, seed, mode, exhaustive):
    rng = random.Random(seed)
    a = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
    solver, linear_solver = rowwise_solver(a, q, mode)
    weights = [1 << j for j in range((q - 1).bit_length())]
    pairs = list(itertools.combinations_with_replacement(range(n), 2)) if exhaustive else [
        (0, 0), (0, n - 1), (n - 1, n - 1)]
    if not exhaustive:
        weights = [1, q // 2]
    worst = None
    records = []
    for i, j in pairs:
        for w in weights:
            target = [[w * int((r, t) == (i, j)) % q for t in range(n)] for r in range(n)]
            b = solver(target)
            norm = l1(b)
            records.append({"indices": [i, j], "weight": w, "l1": norm,
                            "max_entry": max(abs(x) for row in b for x in row)})
            if worst is None or norm > worst["l1"]:
                worst = {**records[-1], "B": b, "U": certify(a, b, target, q)}
    zero = [[0] * n for _ in range(n)]
    last = [[(q // 2) * int(i == j == n - 1) for j in range(n)] for i in range(n)]
    bz, bw = solver(zero), solver(last)
    difference = [[x - y for x, y in zip(wr, zr)] for wr, zr in zip(bw, bz)]
    prefix_equal = all(bw[i] == bz[i] for i in range(n - 1))
    attack = {"same_prefix_as_zero_target": prefix_equal,
              "zero_target_l1": l1(bz), "last_diagonal_l1": l1(bw)}
    if prefix_equal:
        pi = difference[-1]
        assert all(sum(x * y for x, y in zip(row, pi)) % q ==
                   (q // 2) * int(i == n - 1) for i, row in enumerate(a))
        attack.update(linear_preimage=pi, linear_preimage_l1=sum(map(abs, pi)))
    # This target remains necessary after replacing binary diagonal products
    # by affine shifts. A shared prefix exposes coordinate 0 from the last row.
    off = [[(q // 2) * int(i == 0 and j == n - 1) for j in range(n)] for i in range(n)]
    bo = solver(off)
    off_prefix_equal = all(bo[i] == bz[i] for i in range(n - 1))
    off_attack = {"same_prefix_as_zero_target": off_prefix_equal,
                  "off_diagonal_l1": l1(bo), "recovered_coordinate": 0}
    if off_prefix_equal:
        pi = [x - y for x, y in zip(bo[-1], bz[-1])]
        assert all(sum(x * y for x, y in zip(row, pi)) % q ==
                   (q // 2) * int(i == 0) for i, row in enumerate(a))
        off_attack.update(linear_preimage=pi, linear_preimage_l1=sum(map(abs, pi)),
                          unit_error_guaranteed=2 * sum(map(abs, pi)) < q // 2)
    # General linear attack filter uses the same final prefix lattice.
    recovery = []
    for i in range(n):
        pi = linear_solver([(q // 2) * int(r == i) for r in range(n)])
        norm = sum(map(abs, pi))
        recovery.append({"coordinate": i, "l1": norm,
                         "unit_error_guaranteed": 2 * norm < min(q // 2, q - q // 2)})
    return {"n": n, "m": m, "q": q, "seed": seed, "mode": mode, "A": a,
            "prefix_lattice_dimension": m, "prefix_lattices": n,
            "monolithic_lattice_dimension": n * m,
            "targets_checked": len(records), "worst_l1": worst["l1"],
            "records": records, "worst_witness": worst,
            "zero_difference_attack": attack, "off_diagonal_difference_attack": off_attack,
            "linear_recovery_filter": recovery}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = [(2, 8, 257), (4, 16, 257), (4, 16, 65537), (8, 8, 257),
             (8, 8, 65537), (8, 32, 65537), (16, 64, 65537)]
    results = []
    for index, (n, m, q) in enumerate(cases):
        seed = 417 + index
        for mode in ("zero", "shared", "target_dependent"):
            try:
                record = run_case(n, m, q, seed, mode, exhaustive=n <= 8)
            except ValueError as error:
                record = {"n": n, "m": m, "q": q, "seed": seed, "mode": mode,
                          "failure": str(error)}
            results.append(record)
            print({key: record[key] for key in
                   ["n", "m", "q", "mode", "targets_checked", "worst_l1", "failure"]
                   if key in record}, flush=True)
    args.output.write_text(json.dumps({"scope": "Exact finite diagnostics only; no secure parameter or polynomial norm claim",
                                     "cases": results}, indent=2) + "\n")


if __name__ == "__main__":
    main()
