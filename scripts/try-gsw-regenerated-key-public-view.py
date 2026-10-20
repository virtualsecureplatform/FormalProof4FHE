#!/usr/bin/env python3
"""Check public-key compatibility of the error-absorbing latent-key candidate.

Uses actual recursive fresh-zero columns and the constant-feature, top-level
column of public GSW encryption. This is a finite construction diagnostic,
not a bootstrap experiment, security proof, or efficient key-recovery attack.
"""

import argparse
from fractions import Fraction
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    'error_absorbing', Path(__file__).with_name('try-gsw-error-absorbing-key.py'))
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)


def centered_abs(value, q):
    value %= q
    return min(value, q - value)


def decode_nearest(phase, q):
    # TFHE.BootstrappingCorrectness.decodeNearest breaks ties toward zero.
    return int(centered_abs(phase - q // 2, q) < centered_abs(phase, q))


def fresh_table(key, count, q, radius, rng):
    n = len(key)
    zero = ([[0] * n for _ in range(n)], [0] * n, 0)
    columns = []
    for _ in range(count):
        column, phase_error = candidate.add_fresh_zero(key, zero, q, radius, rng)
        assert candidate.decrypt(key, column, q) == phase_error % q
        columns.append(column)
    return columns


def uniform_table(n, count, q, rng):
    return [([[rng.randrange(q) for _ in range(n)] for _ in range(n)],
             [rng.randrange(q) for _ in range(n)], rng.randrange(q))
            for _ in range(count)]


def compatible_keys(columns, n, q, bound):
    # Exhaustive enumeration is deliberately restricted to the diagnostic.
    return [key for key in itertools.product((0, 1), repeat=n)
            if all(centered_abs(candidate.decrypt(key, column, q), q) <= bound
                   for column in columns)]


def selected_encryption_column(columns, selectors, bit, q):
    """Flattened subset hash + gadget at the constant-feature top column."""
    n = len(columns[0][1])
    selected = [column for column, take in zip(columns, selectors) if take]
    matrix = [[sum(column[0][i][j] for column in selected) % q
               for j in range(n)] for i in range(n)]
    linear = [sum(column[1][i] for column in selected) % q for i in range(n)]
    body = (sum(column[2] for column in selected) + bit * (q // 2)) % q
    return matrix, linear, body


def check_wrong_key_uniform_orbits():
    """Exhaust the selected inner-mask coordinate in small exact examples."""
    rng = random.Random(2026101701)
    orbits = checks = 0
    for n, q in itertools.product((2, 3), (2, 4, 8, 16)):
        for original in itertools.product((0, 1), repeat=n):
            for wrong in itertools.product((0, 1), repeat=n):
                if original == wrong:
                    continue
                selected = next(i for i in range(n) if original[i] != wrong[i])
                for _ in range(2):
                    matrix = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
                    inner = [rng.randrange(q) for _ in range(n)]
                    errors = [rng.randrange(q) for _ in range(n)]
                    body_error = rng.randrange(q)
                    phases = []
                    for value in range(q):
                        inner[selected] = value
                        linear = [(sum(original[i] * matrix[i][j] for i in range(n)) -
                                   inner[j] + errors[j]) % q for j in range(n)]
                        body = (sum(x * y for x, y in zip(original, inner)) + body_error) % q
                        phase = candidate.decrypt(wrong, (matrix, linear, body), q)
                        expected = (body_error + sum(wrong[i] * errors[i] for i in range(n)) +
                                    sum((original[i] - wrong[i]) * inner[i] for i in range(n)) +
                                    sum((original[i] - wrong[i]) * matrix[i][j] * wrong[j]
                                        for i in range(n) for j in range(n))) % q
                        assert phase == expected
                        phases.append(phase)
                        checks += 1
                    assert sorted(phases) == list(range(q))
                    orbits += 1
    return dict(exact_wrong_key_uniform_orbits=orbits,
                exact_wrong_key_phase_identity_checks=checks)


def trial(n, levels, radius, count, seed):
    rng = random.Random(seed)
    q, m = 1 << levels, n - 2
    bound = (n + 1) * radius
    assert count * bound < q // 4
    while True:
        a = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
        rows = candidate.source_rows(a)
        inverse = candidate.inverse_binary([row[2:] for row in rows])
        if inverse is not None:
            break
    errors = [rng.randint(-radius, radius) for _ in range(m)]
    errors[0] = 1  # Exercise the odd-error case that forces an actual key change.
    delta = [0, 0] + candidate.multiply_binary(inverse, [e % 2 for e in errors])
    assert any(delta)
    result = dict(n=n, levels=levels, q=q, radius=radius, columns=count, seed=seed,
                  single_column_phase_bound=bound, source_key_draws=0,
                  original_key_phase_checks=0, changed_key_phase_checks=0,
                  changed_key_columns_outside_bound=0,
                  changed_key_compatible_retained_tables=0,
                  regenerated_key_phase_checks=0,
                  original_key_selected_column_checks=0,
                  changed_key_selected_column_checks=0,
                  changed_key_selected_column_strict_interval_failures=0,
                  changed_key_selected_column_decode_failures=0,
                  regenerated_key_selected_column_checks=0)
    for source_key in itertools.product((0, 1), repeat=n):
        result['source_key_draws'] += 1
        outputs = [(sum(source_key[i] * a[i][j] for i in range(n)) + errors[j]) % q
                   for j in range(m)]
        key = tuple(x ^ y for x, y in zip(source_key, delta))
        assert key != source_key
        assert list(key) in candidate.candidate_keys(a, outputs, inverse)
        retained = fresh_table(source_key, count, q, radius, rng)
        regenerated = fresh_table(key, count, q, radius, rng)
        wrong_phases = []
        for old, new in zip(retained, regenerated):
            assert centered_abs(candidate.decrypt(source_key, old, q), q) <= bound
            assert centered_abs(candidate.decrypt(key, new, q), q) <= bound
            wrong = centered_abs(candidate.decrypt(key, old, q), q)
            wrong_phases.append(wrong)
            result['changed_key_columns_outside_bound'] += wrong > bound
            result['original_key_phase_checks'] += 1
            result['changed_key_phase_checks'] += 1
            result['regenerated_key_phase_checks'] += 1
        result['changed_key_compatible_retained_tables'] += all(x <= bound for x in wrong_phases)
        for bit, _ in itertools.product((0, 1), range(2)):
            selectors = [rng.randrange(2) for _ in range(count)]
            ciphertext = selected_encryption_column(retained, selectors, bit, q)
            fresh = selected_encryption_column(regenerated, selectors, bit, q)
            message = bit * (q // 2)
            assert centered_abs(candidate.decrypt(source_key, ciphertext, q) - message, q) < q // 4
            assert centered_abs(candidate.decrypt(key, fresh, q) - message, q) < q // 4
            assert decode_nearest(candidate.decrypt(source_key, ciphertext, q), q) == bit
            assert decode_nearest(candidate.decrypt(key, fresh, q), q) == bit
            wrong_phase = candidate.decrypt(key, ciphertext, q)
            result['changed_key_selected_column_strict_interval_failures'] += (
                centered_abs(wrong_phase - message, q) >= q // 4)
            result['changed_key_selected_column_decode_failures'] += decode_nearest(wrong_phase, q) != bit
            result['original_key_selected_column_checks'] += 1
            result['changed_key_selected_column_checks'] += 1
            result['regenerated_key_selected_column_checks'] += 1
        if result['source_key_draws'] == 1:
            keys = compatible_keys(retained, n, q, bound)
            result['first_retained_table_compatible_key_count'] = len(keys)
            assert source_key in keys
            result['first_retained_table_unique_original_key'] = keys == [source_key]
            result['first_regenerated_table_compatible_key_count'] = len(
                compatible_keys(regenerated, n, q, bound))
    result['uniform_table_compatible_key_count'] = len(
        compatible_keys(uniform_table(n, count, q, rng), n, q, bound))
    pi = Fraction(2 * bound + 1, q)
    result['fixed_wrong_key_compatibility_probability_exact'] = str(pi ** count)
    result['any_wrong_key_compatibility_union_bound'] = str((2 ** n - 1) * pi ** count)
    result['uniform_table_any_key_compatibility_union_bound'] = str(2 ** n * pi ** count)
    result['uniform_table_any_key_bound_below_2_pow_minus_40'] = (
        2 ** n * pi ** count < Fraction(1, 2 ** 40))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('docs/GSWRegeneratedPublicViewExploration.json'))
    args = parser.parse_args()
    exact_checks = check_wrong_key_uniform_orbits()
    records = [trial(n, levels, radius, count,
                     20261017 + 10000 * n + 100 * levels + 10 * radius + count + seed)
               for n, levels, radius, count, seed in itertools.product(
                   (3, 4, 6, 8), (14, 20), (1, 3), (8, 24), range(2))]
    counters = ('source_key_draws', 'original_key_phase_checks', 'changed_key_phase_checks',
                'changed_key_columns_outside_bound', 'changed_key_compatible_retained_tables',
                'regenerated_key_phase_checks', 'original_key_selected_column_checks',
                'changed_key_selected_column_checks',
                'changed_key_selected_column_strict_interval_failures',
                'changed_key_selected_column_decode_failures',
                'regenerated_key_selected_column_checks')
    summary = dict(families=len(records), **exact_checks,
                   **{key: sum(r[key] for r in records) for key in counters})
    summary.update(
        first_retained_tables_with_unique_original_key=sum(
            r['first_retained_table_unique_original_key'] for r in records),
        uniform_tables_with_any_compatible_binary_key=sum(
            r['uniform_table_compatible_key_count'] != 0 for r in records),
        all_uniform_table_compatibility_bounds_below_2_pow_minus_40=all(
            r['uniform_table_any_key_bound_below_2_pow_minus_40'] for r in records))
    args.output.write_text(json.dumps(dict(
        scope='Retaining versus regenerating full recursive public-key zero columns after '
              'the earlier error-absorbing binary-key transport.',
        limitations='Finite diagnostic, not a Lean theorem, full bootstrap trial, or security '
                    'attack. Diagnostic bounded errors are not an asymptotic LWE hardness '
                    'instantiation. Selected encryption columns use independent binary subset '
                    'selectors and the constant-feature top gadget column; the nearest-codeword '
                    'decoder breaks ties toward zero as in the Lean definition. Exhaustive key '
                    'enumeration is unbounded. The support bounds do not exclude changing the '
                    'public table by another joint nonlinear simulator, or a game-specific '
                    'uniform endpoint that has no valid decryption key.',
        mathematical_bounds=dict(
            retained_wrong_key='For independent fresh columns under s, any fixed binary v != s '
                               'has independent uniform phases: coefficient of one inner mask '
                               'is s_i-v_i = +/-1. With H < q/2, compatibility is ((2H+1)/q)^p.',
            retained_adaptive_key='A union bound over all wrong binary keys bounds existence '
                                  'by (2^n-1)((2H+1)/q)^p, also covering adaptive key selection.',
            uniform_full_table='For each binary v, the independently uniform body makes every '
                                 'column phase uniform. Existence of any compatible binary key '
                                 'has probability at most 2^n((2H+1)/q)^p.',
            regeneration_endpoint='A sampler always producing a compatible binary key and '
                                  'narrow-noise zero table is separated in TV from a uniform '
                                  'full table by at least 1-2^n((2H+1)/q)^p. This separating '
                                  'event may be computationally infeasible to test.'),
        summary=summary, records=records), indent=2) + '\n')
    print(json.dumps(summary))
    print(f'Wrote {args.output}')


if __name__ == '__main__':
    main()
