#!/usr/bin/env python3
"""Reproducible construction attempts, not a cryptographic parameter claim.

Requires fpylll 0.6.4 and cysignals. The lattice experiment uses only A,
never the secret or source errors. Every returned preimage is checked exactly.
"""

import argparse
import itertools
import json
from pathlib import Path
import random

from fpylll import CVP, IntegerMatrix, LLL


def centered(x, q):
    return (x + q // 2) % q - q // 2


def lattice_solver(matrix, q):
    """Full kernel lattice of a full-row-rank modular system; unit pivots only.

    Works over prime fields and over composite moduli when elimination finds
    unit pivots. Failure is explicit, rather than conditioning the matrix law.
    """
    import math
    rows, cols = len(matrix), len(matrix[0])
    reduced = [[x % q for x in row] for row in matrix]
    transform = [[int(i == j) for j in range(rows)] for i in range(rows)]
    pivots = []
    for col in range(cols):
        rank = len(pivots)
        pivot = next((i for i in range(rank, rows)
                      if math.gcd(reduced[i][col], q) == 1), None)
        if pivot is None:
            continue
        for mat in (reduced, transform):
            mat[rank], mat[pivot] = mat[pivot], mat[rank]
        inverse = pow(reduced[rank][col], -1, q)
        reduced[rank] = [x * inverse % q for x in reduced[rank]]
        transform[rank] = [x * inverse % q for x in transform[rank]]
        for i in range(rows):
            if i == rank:
                continue
            factor = reduced[i][col]
            reduced[i] = [(x - factor * y) % q
                          for x, y in zip(reduced[i], reduced[rank])]
            transform[i] = [(x - factor * y) % q
                            for x, y in zip(transform[i], transform[rank])]
        pivots.append(col)
        if len(pivots) == rows:
            break
    if len(pivots) != rows:
        raise ValueError("no full unit-pivot elimination; source not resampled")
    free = [j for j in range(cols) if j not in pivots]
    basis = []
    for pivot in pivots:
        basis.append([q * int(j == pivot) for j in range(cols)])
    for col in free:
        vector = [int(j == col) for j in range(cols)]
        for i, pivot in enumerate(pivots):
            vector[pivot] = centered(-reduced[i][col], q)
        basis.append(vector)
    # Exact checks also catch row/column convention errors in lattice APIs.
    assert all(all(sum(a * b for a, b in zip(row, v)) % q == 0
                   for row in matrix) for v in basis)
    lattice = IntegerMatrix.from_matrix(basis)
    LLL.reduction(lattice)

    def solve(target):
        particular = [0] * cols
        for i, pivot in enumerate(pivots):
            particular[pivot] = centered(sum(a * b for a, b in
                                             zip(transform[i], target)), q)
        # CVP.babai returns a lattice vector; GSO.babai has a different API.
        nearby = CVP.babai(lattice, particular)
        solution = [x - y for x, y in zip(particular, nearby)]
        assert all(sum(a * b for a, b in zip(row, solution)) % q == t % q
                   for row, t in zip(matrix, target))
        return solution

    # Optional diagnostic access; constructing these vectors uses public A
    # and the same already-reduced lattice, not a private trapdoor.
    solve.kernel_basis = lambda: [tuple(int(lattice[i, j]) for j in range(cols))
                                 for i in range(cols)]
    return solve


def quadratic_system(a):
    n, m = len(a), len(a[0])
    pairs = list(itertools.combinations_with_replacement(range(n), 2))
    matrix = []
    for i, j in pairs:
        matrix.append([a[j][c] if r == i else a[i][c] if r == j else 0
                       for r in range(n) for c in range(m)])
    return pairs, matrix


def preimage_attempt(n, m, q, seed):
    rng = random.Random(seed)
    a = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
    pairs, system = quadratic_system(a)
    quadratic = lattice_solver(system, q)
    linear = lattice_solver(a, q)
    weights = [1 << j for j in range((q - 1).bit_length())]
    records = []
    worst_witness = None
    for p, indices in enumerate(pairs):
        for weight in weights:
            target = [weight if i == p else 0 for i in range(len(pairs))]
            b = quadratic(target)
            product = [[sum(b[r * m + c] * a[t][c] for c in range(m)) % q
                        for t in range(n)] for r in range(n)]
            target_matrix = [[weight * int((r, t) == indices) % q
                              for t in range(n)] for r in range(n)]
            difference = [[(product[r][t] - target_matrix[r][t]) % q
                           for t in range(n)] for r in range(n)]
            witness = [[difference[r][t] if r < t else 0
                        for t in range(n)] for r in range(n)]
            assert all((product[r][t] - target_matrix[r][t] - witness[r][t] +
                        witness[t][r]) % q == 0 for r in range(n) for t in range(n))
            # l1 controls the integer residual for |s_i|, |e_c| <= 1.
            records.append({"indices": list(indices), "weight": weight,
                            "max_entry": max(map(abs, b)), "l1": sum(map(abs, b))})
            if worst_witness is None or records[-1]["l1"] > worst_witness["l1"]:
                worst_witness = {**records[-1], "B": [b[r*m:(r+1)*m] for r in range(n)],
                                 "alternating_certificate_U": witness}
    # Compare against a direct key-recovery filter at these toy parameters.
    # Linear preimages with small projected errors publicly decode key bits.
    secret = [rng.randrange(2) for _ in range(n)]
    error = [rng.choice((-1, 0, 1)) for _ in range(m)]
    y = [(sum(a[r][c] * secret[r] for r in range(n)) + error[c]) % q
         for c in range(m)]
    recovery = []
    weight = q // 2
    for i in range(n):
        pi = linear([weight * int(r == i) for r in range(n)])
        l1 = sum(map(abs, pi))
        # This guarantees recovery for EVERY binary key and EVERY unit error,
        # beyond the one explicitly sampled transcript below.
        guaranteed = 2 * l1 < min(weight, q - weight)
        observed = sum(x * z for x, z in zip(pi, y)) % q
        guess = int(abs(centered(observed - weight, q)) < abs(centered(observed, q)))
        recovery.append({"coordinate": i, "l1": l1,
                         "guaranteed_for_all_binary_keys_and_unit_errors": guaranteed,
                         "projected_error": sum(x * e for x, e in zip(pi, error)),
                         "correct": guess == secret[i]})
    return {"n": n, "m": m, "q": q, "seed": seed, "A": a,
            "constraints": len(pairs), "lattice_dimension": n * m,
            "targets_checked": len(records), "max_entry": max(r["max_entry"] for r in records),
            "worst_l1": max(r["l1"] for r in records),
            "binary_unit_error_one_column_bound": 1 + max(r["l1"] for r in records),
            "q_over_4": q / 4, "records": records, "worst_witness": worst_witness,
            "ordinary_linear_key_recovery_filter": recovery}


def direct_game_attempt(q=256, n=4):
    """Rank-zero lossy BK with a high gadget weight and bounded noise.

    This refutes this particular statistical endpoint, not a computational
    direct-game proof or any general lossy-matrix construction.
    """
    recovered = 0
    for secret in itertools.product((0, 1), repeat=n):
        for error in itertools.product((-1, 0, 1), repeat=n):
            # Native body-row controls: phase = weight*s_i + error_i.
            weight = q // 2
            bodies = [(weight * s + e) % q for s, e in zip(secret, error)]
            guess = [int(abs(centered(b - weight, q)) < abs(centered(b, q)))
                     for b in bodies]
            assert guess == list(secret)
            # After recovering s, the two challenge branches are distinguishable.
            mask = tuple((17 + 13 * i) % q for i in range(n))
            for bit in (0, 1):
                body = (sum(x * s for x, s in zip(mask, secret)) + weight * bit) % q
                phase = (body - sum(x * s for x, s in zip(mask, guess))) % q
                assert phase == weight * bit
                recovered += 1
    return {"construction": "rank-zero replacement of all masks, narrow real key-message bodies",
            "n": n, "q": q, "challenge_cases": recovered,
            "key_and_challenge_recovery": "all enumerated cases",
            "scope": "This proposed statistical lossy endpoint fails; no universal no-go."}


def specialized_format_attempt(n=5):
    """Try a cycle of anchor-specific degree-two star formats, same binary key.

    A target feature needs an encryption of its product with every receiving
    format feature. This audits the natural GSW linear switching interface.
    """
    def star(anchor):
        return {frozenset(), *[frozenset([i]) for i in range(n)],
                *[frozenset([anchor, i]) for i in range(n) if i != anchor]}
    records = []
    for anchor in range(n):
        other = (anchor + 1) % n
        missing = star(anchor) - star(other)
        required = {left | right for left in missing for right in star(other)}
        high = sorted([sorted(x) for x in required if len(x) > 2])
        records.append({"from_anchor": anchor, "to_anchor": other,
                        "missing_features": sorted([sorted(x) for x in missing]),
                        "required_degree": max(map(len, required), default=0),
                        "higher_degree_products": high})
    # Alternative: lookup for the fixed scalar decryption circuit. A mask
    # (q/2,...,q/2) and zero body give exactly parity on noiseless binary keys.
    # Compute its integer multilinear coefficients by Mobius inversion.
    parity = [i.bit_count() % 2 for i in range(1 << n)]
    coeff = parity[:]
    for bit in range(n):
        for mask in range(1 << n):
            if mask & (1 << bit):
                coeff[mask] -= coeff[mask ^ (1 << bit)]
    assert coeff[-1] == (-2) ** (n - 1)
    return {"n": n, "same_key_star_cycle": records,
            "scalar_noiseless_decryption_parity_degree": n,
            "parity_top_coefficient": coeff[-1],
            "lookup_entries": 1 << n,
            "scope": "Tests star switching and full-table refresh only; does not exclude reusable garbling or another interface."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    experiments = [(2, 8, 257), (3, 12, 257), (4, 16, 257),
                   (4, 16, 65537), (6, 24, 65537), (4, 16, 256),
                   (8, 8, 257), (8, 8, 65537)]
    result = {"scope": "Construction diagnostics only: no security or bootstrap claim",
              "solver": "fpylll 0.6.4 LLL plus Babai nearest plane, no trapdoor",
              "direct_game": direct_game_attempt(),
              "specialized_refresh": specialized_format_attempt(), "preimages": []}
    for seed, (n, m, q) in enumerate(experiments, start=417):
        try:
            record = preimage_attempt(n, m, q, seed)
        except ValueError as error:
            record = {"n": n, "m": m, "q": q, "seed": seed, "failure": str(error)}
        result["preimages"].append(record)
        print({k: v for k, v in record.items() if k not in
               ("records", "ordinary_linear_key_recovery_filter", "A", "worst_witness")}, flush=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print("Direct lossy endpoint and star-format cycle tested; all exact checks passed.")


if __name__ == "__main__":
    main()
