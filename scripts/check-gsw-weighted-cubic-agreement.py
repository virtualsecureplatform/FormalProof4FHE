#!/usr/bin/env python3
"""Exact diagnostics for weighted cubic/quad agreement over Z/(2^k).

The socle argument and VC bound are mathematical derivations, not Lean
security theorems. Noisy ciphertext cancellation is outside their scope.
"""
import argparse
from collections import Counter
from fractions import Fraction
import itertools
import json
from math import comb
from pathlib import Path
import random


def valuation(value, exponent):
    return exponent if value == 0 else (value & -value).bit_length() - 1


def diagonal_test(matrix, targets, exponent):
    """Row/column elimination over the finite principal ideal ring.

    Returns feasibility for all RHS columns and the number of nonzero
    invariant factors. Minimal valuation makes each elimination quotient
    integral. Row/column swaps and odd-unit rescaling are invertible.
    """
    q = 1 << exponent
    A = [[x % q for x in row] for row in matrix]
    B = [[x % q for x in row] for row in targets]
    m = len(A)
    d = len(A[0]) if m else 0
    width = len(B[0]) if m else 0
    r = 0
    consistent = True
    for pivot in range(min(m, d)):
        best = min(((valuation(A[i][j], exponent), i, j)
                    for i in range(pivot, m) for j in range(pivot, d)))
        v, row, col = best
        if v == exponent:
            break
        A[pivot], A[row] = A[row], A[pivot]
        B[pivot], B[row] = B[row], B[pivot]
        for line in A:
            line[pivot], line[col] = line[col], line[pivot]
        unit_inverse = pow(A[pivot][pivot] >> v, -1, q)
        A[pivot] = [(x * unit_inverse) % q for x in A[pivot]]
        B[pivot] = [(x * unit_inverse) % q for x in B[pivot]]
        divisor = 1 << v
        assert A[pivot][pivot] == divisor
        # Clear the pivot column below it, applying identical row operations
        # to every RHS. Earlier pivot columns in these rows are already zero.
        for i in range(pivot + 1, m):
            assert A[i][pivot] % divisor == 0
            multiplier = A[i][pivot] // divisor
            A[i] = [(x - multiplier * y) % q for x, y in zip(A[i], A[pivot])]
            B[i] = [(x - multiplier * y) % q for x, y in zip(B[i], B[pivot])]
        # Clear the pivot row by column operations, leaving RHS unchanged.
        # The pivot column has only one nonzero entry, so no other row changes.
        assert all(A[pivot][j] % divisor == 0 for j in range(pivot + 1, d))
        for j in range(pivot + 1, d):
            A[pivot][j] = 0
        consistent &= all(x % divisor == 0 for x in B[pivot])
        r += 1
    assert all(all(x == 0 for x in row[r:]) for row in A[r:])
    consistent &= all(all(x == 0 for x in row) for row in B[r:])
    return bool(consistent), r


def binary_rank(rows):
    basis = {}
    for row in rows:
        value = sum((x & 1) << j for j, x in enumerate(row))
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = value
                break
            value ^= basis[pivot]
    return len(basis)


def brute_solver_checks():
    records = []
    for exponent, m, d in ((1, 2, 2), (2, 2, 2), (2, 3, 2), (3, 2, 1)):
        q = 1 << exponent
        matrices = cases = socle_checks = 0
        for entries in itertools.product(range(q), repeat=m*d):
            A = [entries[i*d:(i+1)*d] for i in range(m)]
            image = {tuple(sum(row[j] * coefficients[j] for j in range(d)) % q for row in A)
                     for coefficients in itertools.product(range(q), repeat=d)}
            torsion = {y for y in image if all(2*x % q == 0 for x in y)}
            feasible, r = diagonal_test(A, [[0] for _ in range(m)], exponent)
            assert feasible and len(torsion) == 2**r and r <= d
            socle_checks += 1
            for rhs in itertools.product(range(q), repeat=m):
                feasible, _ = diagonal_test(A, [[x] for x in rhs], exponent)
                assert feasible == (rhs in image)
                cases += 1
            matrices += 1
        records.append(dict(exponent=exponent, rows=m, columns=d, matrices=matrices,
                            rhs_feasibility_cases=cases, exact_socle_cardinality_checks=socle_checks))
    return records


def rows(n):
    points = list(itertools.product((0, 1), repeat=n))
    pairs = list(itertools.combinations(range(n), 2))
    triples = list(itertools.combinations(range(n), 3))
    A = [[1] + list(x) + [x[i]*x[j] for i, j in pairs] for x in points]
    B = [[x[i]*x[j]*x[k] for i, j, k in triples] for x in points]
    return points, A, B


def subset_check(n, exponent, level, exhaustive=True):
    points, A, B = rows(n)
    N, D = len(points), len(A[0])
    weight = 1 << level
    histogram = Counter()
    cases = feasible_cases = 0
    rng = random.Random(20261018 + n + exponent + level)
    if exhaustive:
        subsets = range(1 << N)
    else:
        subsets = [rng.getrandbits(N) for _ in range(600)]
        # Parity slices expose genuine nonunit behavior: rational quadratic
        # interpolation may introduce powers-of-two denominators.
        for active in range(1, n + 1):
            parity_slice = sum(1 << i for i, x in enumerate(points) if sum(x[:active]) % 2 == 0)
            subsets.append(parity_slice)
            subsets.extend(parity_slice | (1 << i) for i in range(N) if not (parity_slice >> i) & 1)
    excess_example = None
    for subset in subsets:
        indices = [i for i in range(N) if (subset >> i) & 1]
        selected_A = [A[i] for i in indices]
        selected_B = [[weight*x for x in B[i]] for i in indices]
        feasible, r = diagonal_test(selected_A, selected_B, exponent)
        cases += 1
        if feasible:
            H3 = binary_rank([A[i] + B[i] for i in indices])
            # The image's order-two subgroup has dimension r. Every degree
            # <=3 Boolean evaluation embeds in it by multiplying by q/2.
            assert H3 <= r <= D
            # Shattered d coordinates give independent degree <=3 monomials.
            vc = 0
            for coordinate_mask in range(1 << n):
                count = coordinate_mask.bit_count()
                if count <= vc:
                    continue
                seen = {sum(points[i][j] << j for j in range(n) if (coordinate_mask >> j) & 1)
                        for i in indices}
                if len(seen) == 1 << count:
                    vc = count
            if indices:
                assert sum(comb(vc, j) for j in range(min(3, vc)+1)) <= H3
            else:
                assert H3 == 0
            assert len(indices) <= sum(comb(n, j) for j in range(vc+1))
            histogram[len(indices)] += 1
            feasible_cases += 1
            if len(indices) > D and excess_example is None:
                excess_example = dict(points=[points[i] for i in indices], size=len(indices),
                                      quadratic_features=D, socle_dimension=r, cubic_binary_rank=H3,
                                      vc_dimension=vc)
    return dict(n=n, modulus=1 << exponent, level=level, weight=weight,
                quadratic_features=D, subsets_checked=cases, feasible_subsets=feasible_cases,
                largest_feasible_tested_subset=max(histogram), exhaustive=exhaustive,
                histogram=dict(histogram), exceeds_unit_weight_D_bound_example=excess_example)


def explicit_nonunit_example():
    n = 5
    points, A, B = rows(n)
    triples = list(itertools.combinations(range(n), 3))
    pairs = list(itertools.combinations(range(n), 2))
    records = []
    for exponent in (3, 4, 5):
        q = 1 << exponent
        g = q // 2
        agreeing = []
        evaluations = 0
        for x in points:
            correct = True
            for triple in triples:
                complement = tuple(i for i in range(n) if i not in triple)
                selected = list(itertools.combinations(triple, 2)) + [complement]
                # On odd Hamming weight or zero, all weighted cubics agree
                # with this explicit integer quadratic, without an oracle
                # for modular linear-system feasibility.
                quadratic = (g // 2) * (sum(x[i]*x[j] for i, j in pairs) +
                                          sum(x[i]*x[j] for i, j in selected))
                correct &= quadratic % q == g*x[triple[0]]*x[triple[1]]*x[triple[2]] % q
                evaluations += 1
            if correct:
                agreeing.append(x)
        expected = [x for x in points if sum(x) % 2 == 1 or sum(x) == 0]
        assert agreeing == expected and len(agreeing) == 17 > len(A[0])
        records.append(dict(modulus=q, weight=g, simultaneous_agreement=17,
                            quadratic_feature_count=len(A[0]), formula_evaluations=evaluations,
                            formula='(g/2)*(sum_all_pairs x_i*x_j + sum_pairs_inside_triple x_i*x_j + product_complement_pair)',
                            agreement_set='all odd Hamming weights, together with zero'))
    return records


def envelopes():
    output = []
    for n in (16, 32, 64, 128, 256, 1024, 4096):
        D = 1 + n + comb(n, 2)
        d = max(d for d in range(n+1) if sum(comb(d, j) for j in range(min(3, d)+1)) <= D)
        S = sum(comb(n, j) for j in range(d+1))
        lower = Fraction(2 * 2**n, S) - 1
        # Easier but coarser envelope: d < 3*n^(2/3)+3 gives d/n -> 0;
        # the exact binomial sum here is already explicit at every n.
        output.append(dict(n=n, quadratic_features=D, vc_dimension_upper_bound=d,
                           agreement_count_upper_bound=str(S), keys=str(2**n),
                           signed_norm_lower_bound_numerator=str(lower.numerator),
                           signed_norm_lower_bound_denominator=str(lower.denominator),
                           signed_norm_log2_floor=lower.numerator.bit_length()-lower.denominator.bit_length()-1))
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    solver = brute_solver_checks()
    records = [subset_check(3, k, ell) for k, ell in ((1, 0), (2, 1), (3, 1), (3, 2))]
    records += [subset_check(4, k, ell) for k, ell in ((2, 1), (3, 2))]
    records += [subset_check(n, k, ell, exhaustive=False)
                for n, k, ell in ((5, 3, 2), (5, 4, 3), (6, 4, 3))]
    result = dict(scope='Exact weighted noiseless cubic-message simulation, not noisy ciphertext security',
                  argument='Top-bit socle + degree-three Boolean evaluation rank + Sauer-Shelah',
                  solver_checks=solver, agreement_checks=records, explicit_nonunit_examples=explicit_nonunit_example(),
                  signed_norm_envelopes=envelopes())
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(solver_rhs_cases=sum(x['rhs_feasibility_cases'] for x in solver),
                          agreement_subset_cases=sum(x['subsets_checked'] for x in records),
                          nonunit_D_counterexamples=sum(x['exceeds_unit_weight_D_bound_example'] is not None for x in records),
                          output=str(args.output))))


if __name__ == '__main__':
    main()
