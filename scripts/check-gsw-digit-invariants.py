#!/usr/bin/env python3
"""Exact finite filters for proposed linear GSW error invariants.

These checks concern the existing unsigned binary gadget. They do not rule
out restricted reachable formats or nonlinear error correction, and are not
a Lean proof or a security experiment at cryptographic parameters.
"""
import argparse
import itertools
import json
from pathlib import Path
import random


def gadget(q, rows):
    levels = q.bit_length() - 1
    return [[(1 << (column % levels)) if column // levels == row else 0
             for column in range(rows * levels)] for row in range(rows)]


def digits(matrix, levels):
    return [[(matrix[index // levels][column] >> (index % levels)) & 1
             for column in range(len(matrix[0]))]
            for index in range(len(matrix) * levels)]


def product(first, second, q):
    return [[sum(a * b for a, b in zip(row, column)) % q
             for column in zip(*second)] for row in first]


def row_product(row, matrix, q):
    return product([row], matrix, q)[0]


def gadget_checks():
    identity_count = unit_count = cmux_count = 0
    for q, rows in itertools.product((4, 8, 16, 32), (1, 2, 3)):
        levels = q.bit_length() - 1
        size = rows * levels
        g = gadget(q, rows)
        identity = [[int(i == j) for j in range(size)] for i in range(size)]
        assert digits(g, levels) == identity
        identity_count += 1
        for i, j in itertools.product(range(size), repeat=2):
            unit = [[int(a == i and b == j) for b in range(size)]
                    for a in range(size)]
            assert digits(product(g, unit, q), levels) == unit
            unit_count += 1

        # Actual first CMux branch: p=3, body=0, weight=1, position=2.
        # The shifted indicator is G and the unshifted indicator is zero.
        # Thus every error coordinate of a native control survives this step.
        for bits in itertools.product((0, 1), repeat=rows - 1):
            secret = [1] + [-bit for bit in bits]
            for bit, error_index in itertools.product((0, 1), range(size)):
                masks = [[(3 * row + 5 * column + 1) % q
                          for column in range(size)] for row in range(rows - 1)]
                errors = [int(column == error_index) for column in range(size)]
                bodies = [(sum(s * a[column] for s, a in zip(bits, masks))
                           + bit * row_product(secret, g, q)[column]
                           + errors[column]) % q for column in range(size)]
                control = [bodies] + masks
                result = product(control, digits(g, levels), q)
                assert result == control
                phase = row_product(secret, result, q)
                expected = row_product(secret, g, q)
                assert [(x - bit * y) % q for x, y in zip(phase, expected)] == errors
                cmux_count += 1
    return {"gadget_identity_cases": identity_count,
            "matrix_unit_reconstructions": unit_count,
            "first_cmux_error_checks": cmux_count}


def invariant_checks():
    q, size = 4, 2
    zero = frozenset({(0, 0)})
    points = list(itertools.product(range(q), repeat=size))
    subgroups, pending = {zero}, [zero]
    while pending:
        subgroup = pending.pop()
        for point in points:
            if point in subgroup:
                continue
            enlarged = frozenset(tuple((h[i] + k * point[i]) % q for i in range(size))
                                 for h in subgroup for k in range(q))
            if enlarged not in subgroups:
                subgroups.add(enlarged)
                pending.append(enlarged)
    factors = [[[flat[i * size + j] for j in range(size)] for i in range(size)]
               for flat in itertools.product((0, 1), repeat=size * size)]
    invariant = [subgroup for subgroup in subgroups
                 if all(tuple(row_product(row, factor, q)) in subgroup
                        for row in subgroup for factor in factors)]
    ideals = [frozenset(itertools.product(range(0, q, step), repeat=size))
              for step in (1, 2, 4)]
    assert set(invariant) == set(ideals)
    return {"ring": "Z/4Z", "error_dimension": size,
            "additive_subgroups_enumerated": len(subgroups),
            "binary_digit_factors_enumerated": len(factors),
            "invariant_subgroup_sizes": sorted(map(len, invariant))}


def parity_disclosure_checks():
    # Full-rank public masks and even errors reveal an entire binary secret
    # by solving the noiseless public equations modulo two.
    q, count = 4, 0
    for flat in itertools.product((0, 1), repeat=4):
        a = [flat[:2], flat[2:]]
        if (a[0][0] * a[1][1] - a[0][1] * a[1][0]) % 2 == 0:
            continue
        for secret in itertools.product((0, 1), repeat=2):
            for error in itertools.product((0, 2), repeat=2):
                body = [(sum(a[i][j] * secret[j] for j in range(2)) + error[i]) % q
                        for i in range(2)]
                compatible = [candidate for candidate in itertools.product((0, 1), repeat=2)
                              if all(sum(a[i][j] * candidate[j] for j in range(2)) % 2
                                     == body[i] % 2 for i in range(2))]
                assert compatible == [secret]
                count += 1
    return count


def binary_nullspace(matrix, columns):
    rows = [list(row) for row in matrix]
    pivots = []
    for column in range(columns):
        pivot = next((i for i in range(len(pivots), len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        index = len(pivots)
        rows[index], rows[pivot] = rows[pivot], rows[index]
        for i in range(len(rows)):
            if i != index and rows[i][column]:
                rows[i] = [a ^ b for a, b in zip(rows[i], rows[index])]
        pivots.append(column)
    basis = []
    for free in range(columns):
        if free in pivots:
            continue
        vector = [int(j == free) for j in range(columns)]
        for index, pivot in enumerate(pivots):
            vector[pivot] = rows[index][free]
        basis.append(vector)
    return basis


def eigen_key_list(controls, levels):
    """Public polynomial enumeration; neither a secret nor source errors enter."""
    dimension, rows = len(controls), len(controls) + 1
    matrices = [[[entry[row * levels] % 2 for row in range(rows)] for entry in control]
                for control in controls]
    states = [((), [[int(i == j) for j in range(rows)] for i in range(rows)])]
    maximum_states = 1
    for matrix in matrices:
        next_states = []
        for label, basis in states:
            image = product(basis, matrix, 2)
            for bit in (0, 1):
                constraints = [[image[i][j] ^ (bit * basis[i][j]) for i in range(len(basis))]
                               for j in range(rows)]
                coefficients = binary_nullspace(constraints, len(basis))
                if coefficients:
                    next_states.append((label + (bit,), product(coefficients, basis, 2)))
        assert sum(len(basis) for _, basis in next_states) <= rows
        states = next_states
        maximum_states = max(maximum_states, len(states))
    candidates = [label for label, _ in states
                  if all(row_product([1, *label], matrix, 2)
                         == [bit * value for value in [1, *label]]
                         for matrix, bit in zip(matrices, label))]
    assert len(candidates) <= dimension + 1
    return candidates, maximum_states, matrices


def control_disclosure_checks():
    rng = random.Random(20261010)
    checked, largest_list, largest_states = 0, 0, 0
    for q, dimension in itertools.product((4, 8, 16, 32), range(1, 7)):
        levels = q.bit_length() - 1
        g = gadget(q, dimension + 1)
        size = (dimension + 1) * levels
        for secret in itertools.product((0, 1), repeat=dimension):
            phase_gadget = row_product([1, *[-s for s in secret]], g, q)
            for _ in range(2):
                controls = []
                for bit in secret:
                    masks = [[rng.randrange(q) for _ in range(size)] for _ in secret]
                    bodies = [(sum(s * row[j] for s, row in zip(secret, masks))
                               + bit * phase_gadget[j] + rng.choice((-2, 0, 2))) % q
                              for j in range(size)]
                    controls.append([bodies] + masks)
                candidates, states, matrices = eigen_key_list(controls, levels)
                exhaustive = [candidate for candidate in itertools.product((0, 1), repeat=dimension)
                              if all(row_product([1, *candidate], matrix, 2)
                                     == [bit * value for value in [1, *candidate]]
                                     for matrix, bit in zip(matrices, candidate))]
                assert sorted(candidates) == sorted(exhaustive)
                assert secret in candidates
                checked += 1
                largest_list = max(largest_list, len(candidates))
                largest_states = max(largest_states, states)
    return {"public_control_key_list_checks": checked,
            "largest_compatible_key_list": largest_list,
            "largest_live_eigenspace_count": largest_states,
            "secret_dimensions": [1, 2, 3, 4, 5, 6],
            "error_support": [-2, 0, 2],
            "cross_check": "Every list equals exhaustive compatible-key enumeration"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = {"scope": "Finite filters for strict annihilators and universal linear error ideals",
              "limitations": "No claim about restricted reachable states, nonlinear correction, or general impossibility",
              **gadget_checks(), "invariants": invariant_checks(),
              "even_error_key_recovery_checks": parity_disclosure_checks(),
              "even_control_error_disclosure": control_disclosure_checks()}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
