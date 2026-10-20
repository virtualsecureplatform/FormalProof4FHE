#!/usr/bin/env python3
"""Check signed low-degree simulations of the complete cubic message channel.

Includes an exact paired affine simulation, an optimal single-cubic Boolean
example, complete small-domain quadratic interpolation tests, and a negative
atom for the pointwise public recursive compiler. This is not a Lean theorem
or a complete ordinary-LWE security proof.
"""

import argparse
from collections import Counter
from fractions import Fraction
import itertools
import json
from math import comb
from pathlib import Path


def keys(n):
    return list(itertools.product((0, 1), repeat=n))


def features(key):
    return [1] + list(key) + [key[i] * key[j] for i, j in itertools.combinations(range(len(key)), 2)]


def cubics(key):
    return tuple(key[i] * key[j] * key[k] for i, j, k in itertools.combinations(range(len(key)), 3))


def mobius_coefficients(table, points, q):
    lookup = {sum(bit << i for i, bit in enumerate(point)): value
              for point, value in zip(points, table)}
    values = [lookup[i] for i in range(len(points))]
    for i in range(len(points[0])):
        for mask in range(len(points)):
            if mask & (1 << i):
                values[mask] = (values[mask] - values[mask ^ (1 << i)]) % q
    return values


def single_cubic_optimum():
    points = keys(3)
    target = [point[0] * point[1] * point[2] for point in points]
    branches = []
    for negative, changed in itertools.product((False, True), range(8)):
        table = [value ^ int(i == changed) ^ int(negative) for i, value in enumerate(target)]
        mobius = mobius_coefficients(table, points, 2)
        assert mobius[7] == 0
        coeff = [mobius[0]] + [mobius[1 << i] for i in range(3)]
        coeff += [mobius[(1 << i) | (1 << j)] for i, j in itertools.combinations(range(3), 2)]
        assert all(sum(a * b for a, b in zip(coeff, features(point))) % 2 == value
                   for point, value in zip(points, table))
        branches.append((Fraction(-1 if negative else 7, 48), coeff, table))
    checks = 0
    for i, bit in itertools.product(range(8), (0, 1)):
        mass = sum(weight for weight, _, table in branches if table[i] == bit)
        assert mass == int(bit == target[i])
        checks += 1
    norm = sum(abs(weight) for weight, _, _ in branches)
    assert sum(weight for weight, _, _ in branches) == 1
    assert norm == Fraction(4, 3)
    matches = Counter()
    for coeff in itertools.product((0, 1), repeat=7):
        table = [sum(a * b for a, b in zip(coeff, features(point))) % 2 for point in points]
        agreement = sum(x == y for x, y in zip(table, target))
        matches[agreement] += 1
        assert abs(2 * agreement - 8) <= 6
    # The target's witness value is 8, so norm >= 8/6. The construction is optimal.
    assert min(matches) == 1 and max(matches) == 7

    # Public RecursiveQuadratic compiler at a fixed zero source tape:
    # T=A-M, linear=y-a+l, body=y0+c. Here A=a=y=y0=0.
    # Distinct quadratic coefficient vectors give distinct public ciphertexts.
    atoms = {}
    for weight, coeff, _ in branches:
        matrix = [[0] * 3 for _ in range(3)]
        for value, (i, j) in zip(coeff[4:], itertools.combinations(range(3), 2)):
            matrix[i][j] = (-value) % 2
        ciphertext = tuple(value for row in matrix for value in row) + tuple(coeff[1:4]) + (coeff[0],)
        atoms[ciphertext] = atoms.get(ciphertext, Fraction(0)) + weight
        for point in points:
            phase = (coeff[0] + sum(point[i] * coeff[1 + i] for i in range(3)) -
                     sum(point[i] * matrix[i][j] * point[j] for i in range(3) for j in range(3))) % 2
            assert phase == sum(a * b for a, b in zip(coeff, features(point))) % 2
    assert len(atoms) == 16
    assert min(atoms.values()) == Fraction(-1, 48)

    # This can also affect a genuine GSWMasking IND-CPA continuation. At a
    # zero public table with q=2, base=2 and one gadget level, encryption is
    # bit*I (the subset hash is zero for every selector tape). Read a diagonal
    # entry, guessing it on positive atoms and its complement on negative
    # atoms. The signed winning value is 7/6, so it is not a probability.
    positive_atoms = {atom for atom, mass in atoms.items() if mass > 0}
    signed_winning = Fraction(0)
    game_checks = 0
    for atom, mass in atoms.items():
        wins = 0
        for bit in (0, 1):
            ciphertext = [[bit * int(i == j) for j in range(13)] for i in range(13)]
            guess = ciphertext[0][0] if atom in positive_atoms else 1-ciphertext[0][0]
            wins += guess == bit
            game_checks += 1
        signed_winning += mass * Fraction(wins, 2)
    assert signed_winning == Fraction(7, 6)

    # After averaging a complete secret-consistent zero-error source, the
    # public compiler's signed law is positive and equals the cubic phase law.
    # This contrasts with the negative atom at one fixed source input above.
    averaged_entries = source_branch_cases = 0
    packed_branches = []
    for weight, coeff, _ in branches:
        matrix_mask = sum(value << (3 * i + j) for value, (i, j) in
                          zip(coeff[4:], itertools.combinations(range(3), 2)))
        linear_mask = sum(value << i for i, value in enumerate(coeff[1:4]))
        packed_branches.append((int(weight * 48), matrix_mask, linear_mask, coeff[0]))
    for secret in range(8):
        mass = [0] * (1 << 13)
        for raw_matrix in range(1 << 9):
            raw_body = sum(((sum(((secret >> i) & 1) * ((raw_matrix >> (3 * i + j)) & 1)
                                 for i in range(3))) % 2) << j for j in range(3))
            for inner in range(8):
                inner_body = (secret & inner).bit_count() % 2
                for numerator, matrix_shift, linear_shift, constant in packed_branches:
                    output = ((raw_matrix ^ matrix_shift) |
                              ((raw_body ^ inner ^ linear_shift) << 9) |
                              ((inner_body ^ constant) << 12))
                    mass[output] += numerator
                    source_branch_cases += 1
        expected = int(secret == 7)
        for ciphertext, numerator in enumerate(mass):
            quadratic = sum(((secret >> i) & 1) * ((secret >> j) & 1) *
                            ((ciphertext >> (3 * i + j)) & 1)
                            for i in range(3) for j in range(3)) % 2
            actual = ((ciphertext >> 12) ^ (secret & (ciphertext >> 9)).bit_count() ^ quadratic) & 1
            assert numerator == (48 if actual == expected else 0)
            averaged_entries += 1
    return dict(branches=len(branches), exact_channel_entries=checks,
                signed_norm=str(norm), proved_dual_witness_lower_bound='4/3',
                all_quadratic_boolean_maps=128, agreement_histogram=dict(matches),
                fixed_zero_source_distinct_compiler_outputs=len(atoms),
                fixed_zero_source_negative_event_mass=str(min(atoms.values())),
                fixed_zero_source_signed_GSW_game_winning_value=str(signed_winning),
                fixed_zero_source_GSW_game_bit_checks=game_checks,
                averaged_compiler_ciphertext_entries=averaged_entries,
                averaged_compiler_source_branch_cases=source_branch_cases)


def paired_anchor_simulation(n, q):
    points = keys(n)
    N, width = len(points), comb(n, 3)
    outputs = list(itertools.product(range(q), repeat=width))
    target = [cubics(point) for point in points]
    # Given a public sampled anchor r, independently choose the nonconstant
    # affine coefficients for every output. Set each constant to F(r)-a*r.
    # Enumerate the actual free coefficients to check the conditional laws.
    free_count = q ** n
    counts = []
    coefficient_evaluations = 0
    for anchor in points:
        conditional = [[0] * q for _ in points]
        for coefficients in itertools.product(range(q), repeat=n):
            for i, point in enumerate(points):
                offset = sum(a * (x - r) for a, x, r in zip(coefficients, point, anchor)) % q
                conditional[i][offset] += 1
                coefficient_evaluations += 1
        for i, point in enumerate(points):
            assert sum(conditional[i]) == free_count
            if point == anchor:
                assert conditional[i][0] == free_count
            else:
                assert all(count == free_count // q for count in conditional[i])
        counts.append(conditional)
    baseline = Fraction(1, q ** width)
    checks = 0
    for i, point in enumerate(points):
        for message in outputs:
            positive = Fraction(0)
            for r in range(N):
                probability = Fraction(1)
                for j in range(width):
                    probability *= Fraction(counts[r][i][(message[j] - target[r][j]) % q], free_count)
                positive += probability / N
            signed = N * positive - (N - 1) * baseline
            assert signed == int(message == target[i])
            checks += 1
    return dict(n=n, q=q, cubic_outputs=width, anchors=N,
                affine_coefficient_evaluations=coefficient_evaluations,
                exact_joint_channel_entries=checks, positive_weight=N,
                negative_weight=1-N, signed_norm=2*N-1)


def agreement_subset_check(n):
    points = keys(n)
    N, D = len(points), 1 + n + comb(n, 2)
    rows = [(sum(value << i for i, value in enumerate(features(point))),
             sum(value << i for i, value in enumerate(cubics(point)))) for point in points]
    histogram = Counter()
    for selected in range(1 << N):
        basis = {}
        consistent = True
        for i, (feature_row, rhs) in enumerate(rows):
            if not selected & (1 << i):
                continue
            while feature_row:
                pivot = feature_row.bit_length() - 1
                if pivot not in basis:
                    basis[pivot] = (feature_row, rhs)
                    break
                feature_row ^= basis[pivot][0]
                rhs ^= basis[pivot][1]
            if feature_row == 0 and rhs:
                consistent = False
                break
        if consistent:
            histogram[selected.bit_count()] += 1
    assert max(histogram) == D
    zero_agreement = sum(all(value == 0 for value in cubics(point)) for point in points)
    assert zero_agreement == D
    return dict(n=n, keys=N, quadratic_feature_count=D, tested_key_subsets=1 << N,
                largest_simultaneously_interpolable_subset=max(histogram),
                zero_quadratic_map_agreement=zero_agreement,
                consistent_subset_histogram=dict(histogram))


def scaling_checks():
    records = []
    for n in (3, 4, 8, 10, 16, 32, 64, 128):
        N, D = 2 ** n, 1 + n + comb(n, 2)
        lower = Fraction(2 * N, D) - 1
        # This is a lower bound on one BRANCHWISE upper-bound expression,
        # not a lower bound on cryptographic advantage or exact TV distance.
        # The current sharp entropy expression has q^d-1 in its numerator;
        # q>=2 and d>=1 imply q^d-1>=1, giving the displayed floor.
        entropy_cost_squared = lower ** 2 / (4 * N)
        records.append(dict(n=n, keys=N, quadratic_feature_count=D,
                            signed_norm_lower_bound=str(lower), anchor_signed_norm=2*N-1,
                            branchwise_entropy_cost_lower_bound_squared=str(entropy_cost_squared),
                            branchwise_cost_lower_bound_at_least_half=entropy_cost_squared >= Fraction(1, 4),
                            branchwise_cost_lower_bound_at_least_one=entropy_cost_squared >= 1))
    return records


def low_level_deletion_checks():
    records = []
    for q, radius, cutoff in itertools.product((128, 256), (3, 7, 15), (1, 2, 3)):
        width = 2 * radius + 1
        shifts = [1 << level for level in range(cutoff)]
        assert q > 2 * width + max(shifts)
        original = Counter(tuple(value % q for value in values)
                           for values in itertools.product(range(-radius, radius + 1), repeat=cutoff))
        shifted = Counter(tuple((value + shift) % q for value, shift in zip(values, shifts))
                          for values in itertools.product(range(-radius, radius + 1), repeat=cutoff))
        exact_tv = sum(Fraction(abs(original[value] - shifted[value]), 2 * width ** cutoff)
                       for value in original.keys() | shifted.keys())
        overlap = Fraction(1)
        for shift in shifts:
            overlap *= max(Fraction(0), 1-Fraction(shift, width))
        assert exact_tv == 1-overlap
        union = Fraction((1 << cutoff)-1, width)
        assert exact_tv <= union
        # The actual n=3 table has six ordered distinct-index columns per level.
        ordered_conditional_tv = 1-overlap ** 6
        assert ordered_conditional_tv <= 6 * union
        records.append(dict(q=q, radius=radius, cutoff=cutoff,
                            exact_product_interval_tv=str(exact_tv),
                            exact_ordered_n3_conditional_tv=str(ordered_conditional_tv),
                            union_bound_per_unique_triple=str(union)))
    family = []
    for parameter in (16, 32, 64, 128, 256, 512, 1024):
        scale = parameter+1
        n, radius, cutoff = 2*scale**5, 1 << scale, scale//2
        columns_per_level = n*(n-1)*(n-2)
        deletion = Fraction(columns_per_level*((1 << cutoff)-1), 2*radius+1)
        # Actual finite-budget error is 2*C*t*2^(-scale^2). Use the larger
        # 2*C*t*2^(-scale) here to avoid printing enormous denominators.
        retry_envelope = Fraction(2*columns_per_level*cutoff, 1 << scale)
        total_envelope = deletion+retry_envelope
        family.append(dict(parameter=parameter, binary_key_dimension=n,
                           radius=radius, deleted_levels=cutoff,
                           ordered_cubic_columns_per_level=columns_per_level,
                           full_view_deletion_bound=str(deletion),
                           finite_budget_total_upper_envelope=str(total_envelope),
                           envelope_below_two_pow_minus_parameter_over_8=(
                               total_envelope < Fraction(1, 1 << (parameter//8)))))
    return records, family


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('docs/GSWSignedQuadraticSimulationExploration.json'))
    args = parser.parse_args()
    local = single_cubic_optimum()
    paired = [paired_anchor_simulation(n, q) for n, q in ((3, 2), (3, 4), (3, 8), (3, 16), (4, 2))]
    agreements = [agreement_subset_check(n) for n in (3, 4)]
    scaling = scaling_checks()
    low_levels, family_deletion = low_level_deletion_checks()
    summary = dict(single_cubic_optimal_norm=local['signed_norm'],
                   fixed_source_negative_event_mass=local['fixed_zero_source_negative_event_mass'],
                   fixed_source_signed_GSW_game_winning_value=local['fixed_zero_source_signed_GSW_game_winning_value'],
                   averaged_compiler_ciphertext_entries=local['averaged_compiler_ciphertext_entries'],
                   averaged_compiler_source_branch_cases=local['averaged_compiler_source_branch_cases'],
                   paired_channel_instances=len(paired),
                   paired_exact_joint_channel_entries=sum(r['exact_joint_channel_entries'] for r in paired),
                   paired_affine_coefficient_evaluations=sum(r['affine_coefficient_evaluations'] for r in paired),
                   exhaustive_key_subsets=sum(r['tested_key_subsets'] for r in agreements),
                   agreement_bounds_sharp_in_tested_dimensions=True,
                   scaling_dimensions=len(scaling),
                   exact_product_interval_tv_checks=len(low_levels),
                   concrete_family_low_level_bounds=len(family_deletion))
    args.output.write_text(json.dumps(dict(
        scope='Exact signed simulation of complete cubic message channels by key-independent '
              'quadratic maps, before fresh encryption. Includes an actual public recursive '
              'compiler example at a fixed zero source input.',
        limitations='Not a Lean theorem, complete security proof, or impossibility theorem '
                    'for ciphertext/game-specific reductions. The signed-norm bound assumes '
                    'exact conditional message-channel representation, including all unit-weight '
                    'cubic coordinates, and fixed quadratic branch maps independent of the key. '
                    'It does not cover noisy-ciphertext-only approximation, source-dependent '
                    'nonlinear coefficients, or cancellation proved for the actual observer. '
                    'The entropy-cost calculation concerns composition of existing branchwise '
                    'upper bounds, not actual advantage or an unavoidable loss in every proof.',
        summary=summary, single_cubic=local, paired_simulations=paired,
        quadratic_agreement_checks=agreements, branchwise_scaling=scaling,
        low_level_interval_checks=low_levels, concrete_family_deletion_bounds=family_deletion), indent=2) + '\n')
    print(json.dumps(summary))
    print(f'Wrote {args.output}')


if __name__ == '__main__':
    main()
