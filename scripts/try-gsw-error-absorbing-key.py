#!/usr/bin/env python3
"""Test a mask/error-dependent latent key for a star of cubic controls.

This is not a full refresh sampler. It repairs top-weight cubic phases,
measures key disclosure, and checks what happens to the intended simulation
when the source outputs are uniform. All phase checks use the actual
recursive ciphertext decryption formula.
"""

import argparse
import itertools
import json
from pathlib import Path
import random


def parity_dot(row, vector):
    return sum(x * y for x, y in zip(row, vector)) % 2


def inverse_binary(matrix):
    n = len(matrix)
    rows = [sum((x % 2) << j for j, x in enumerate(row)) | (1 << (n + i))
            for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next((i for i in range(column, n) if (rows[i] >> column) & 1), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for i in range(n):
            if i != column and (rows[i] >> column) & 1:
                rows[i] ^= rows[column]
    return [[(rows[i] >> (n + j)) & 1 for j in range(n)] for i in range(n)]


def multiply_binary(matrix, vector):
    return [parity_dot(row, vector) for row in matrix]


def source_rows(a):
    return [[a[i][j] % 2 for i in range(len(a))] for j in range(len(a[0]))]


def candidate_keys(a, outputs, inverse):
    rows = source_rows(a)
    candidates = []
    for first, second in itertools.product((0, 1), repeat=2):
        rhs = [(outputs[j] - row[0] * first - row[1] * second) % 2
               for j, row in enumerate(rows)]
        key = [first, second] + multiply_binary(inverse, rhs)
        assert all(parity_dot(row, key) == outputs[j] % 2 for j, row in enumerate(rows))
        candidates.append(key)
    return candidates


def public_controls(a, outputs, inverse, q):
    w = q // 2
    rhs = [(a[0][j] + a[1][j] - outputs[j]) % 2 for j in range(len(outputs))]
    coefficients = multiply_binary(inverse, rhs)
    n = len(a)
    controls = []
    for coefficient in coefficients:
        matrix = [[0] * n for _ in range(n)]
        matrix[0][1] = w * coefficient
        controls.append((matrix, [0] * n, 0))
    return controls, coefficients


def decrypt(key, ciphertext, q):
    matrix, linear, body = ciphertext
    return (body + sum(x * y for x, y in zip(key, linear)) -
            sum(key[i] * matrix[i][j] * key[j]
                for i in range(len(key)) for j in range(len(key)))) % q


def add_fresh_zero(key, ciphertext, q, radius, rng):
    n = len(key)
    matrix = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
    inner = [rng.randrange(q) for _ in range(n)]
    errors = [rng.randint(-radius, radius) for _ in range(n)]
    body_error = rng.randint(-radius, radius)
    linear = [(sum(key[i] * matrix[i][j] for i in range(n)) - inner[j] + errors[j]) % q
              for j in range(n)]
    body = (sum(x * y for x, y in zip(key, inner)) + body_error) % q
    zero = (matrix, linear, body)
    phase_error = body_error + sum(x * y for x, y in zip(key, errors))
    assert decrypt(key, zero, q) == phase_error % q
    added = ([[(matrix[i][j] + ciphertext[0][i][j]) % q for j in range(n)]
              for i in range(n)],
             [(linear[i] + ciphertext[1][i]) % q for i in range(n)],
             (body + ciphertext[2]) % q)
    return added, phase_error


def trial(n, levels, radius, seed):
    rng = random.Random(seed)
    q, m = 1 << levels, n - 2
    attempts = 0
    while True:
        attempts += 1
        a = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
        rows = source_rows(a)
        inverse = inverse_binary([row[2:] for row in rows])
        if inverse is not None:
            break
    for i in range(m):
        for j in range(m):
            assert sum(inverse[i][k] * rows[k][j + 2] for k in range(m)) % 2 == int(i == j)
    # Force one odd error so the test cannot silently specialize to even errors.
    errors = [rng.randint(-radius, radius) for _ in range(m)]
    errors[0] = 1
    delta = [0, 0] + multiply_binary(inverse, [e % 2 for e in errors])
    seen, guessed = set(), 0
    phase_checks = randomized_checks = 0
    for source_key in itertools.product((0, 1), repeat=n):
        outputs = [(sum(source_key[i] * a[i][j] for i in range(n)) + errors[j]) % q
                   for j in range(m)]
        key = [x ^ y for x, y in zip(source_key, delta)]
        seen.add(tuple(key))
        candidates = candidate_keys(a, outputs, inverse)
        assert len({tuple(x) for x in candidates}) == 4
        assert key in candidates
        controls, coefficients = public_controls(a, outputs, inverse, q)
        # This extractor sees only the bare controls, not the raw source.
        public_guess = [1, 1] + coefficients
        guessed += public_guess == key
        assert (public_guess == key) == bool(key[0] and key[1])
        for k, control in enumerate(controls, 2):
            target = (q // 2) * key[0] * key[1] * key[k]
            assert decrypt(key, control, q) == target
            phase_checks += 1
            randomized, phase_error = add_fresh_zero(key, control, q, radius, rng)
            assert decrypt(key, randomized, q) == (target + phase_error) % q
            assert abs(phase_error) <= (n + 1) * radius
            distance = lambda x, y: min((x - y) % q, (y - x) % q)
            assert distance(decrypt(key, randomized, q), target) < q // 4
            randomized_checks += 1
    assert len(seen) == 2 ** n
    assert guessed == 2 ** (n - 2)

    # Enumerate every source-output parity and every guessed prefix. For
    # uniform source outputs this produces every binary output key exactly once.
    uniform_seen = set()
    uniform_checks = uniform_zero_added_checks = uniform_nonzero_messages = 0
    for syndrome in itertools.product((0, 1), repeat=m):
        controls, _ = public_controls(a, syndrome, inverse, q)
        for key in candidate_keys(a, syndrome, inverse):
            uniform_seen.add(tuple(key))
            for k, control in enumerate(controls, 2):
                target = (q // 2) * key[0] * key[1] * key[k]
                assert decrypt(key, control, q) == target
                uniform_checks += 1
                uniform_nonzero_messages += target != 0
                randomized, phase_error = add_fresh_zero(key, control, q, radius, rng)
                assert decrypt(key, randomized, q) == (target + phase_error) % q
                uniform_zero_added_checks += 1
    assert len(uniform_seen) == 2 ** n
    assert uniform_nonzero_messages * 8 == uniform_checks
    return dict(n=n, source_samples=m, q=q, radius=radius, seed=seed,
                accepted_mask_after_draws=attempts, source_errors=errors,
                tail_flip=delta[2:], key_bijection_size=len(seen),
                bare_control_key_guesses_correct=guessed, key_count=2 ** n,
                published_raw_source_candidate_count=4,
                real_cubic_phase_checks=phase_checks,
                fresh_zero_added_phase_checks=randomized_checks,
                uniform_source_cubic_phase_checks=uniform_checks,
                uniform_source_fresh_zero_phase_checks=uniform_zero_added_checks,
                uniform_source_nonzero_cubic_messages=uniform_nonzero_messages,
                fresh_zero_phase_bound=(n + 1) * radius,
                scope='Only top-weight cubic controls sharing the first two key bits; '
                      'no complete bootstrapping key or public-key sampler.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path('docs/GSWErrorAbsorbingKeyExploration.json'))
    args = parser.parse_args()
    records = [trial(n, levels, radius, 20261017 + 1000 * n + 100 * levels + 10 * radius + seed)
               for n, levels, radius, seed in itertools.product((3, 4, 6, 8), (10, 14), (1, 3), range(2))]
    summary = dict(families=len(records),
                   source_key_draws=sum(x['key_count'] for x in records),
                   real_phase_checks=sum(x['real_cubic_phase_checks'] for x in records),
                   fresh_zero_phase_checks=sum(x['fresh_zero_added_phase_checks'] for x in records),
                   uniform_source_phase_checks=sum(x['uniform_source_cubic_phase_checks'] for x in records),
                   uniform_source_fresh_zero_phase_checks=sum(x['uniform_source_fresh_zero_phase_checks']
                                                              for x in records),
                   uniform_source_nonzero_cubic_messages=sum(x['uniform_source_nonzero_cubic_messages']
                                                            for x in records),
                   bare_control_key_recovery_probability='1/4',
                   raw_source_public_key_list_size=4,
                   uniform_mode_also_has_correct_cubic_controls=True)
    args.output.write_text(json.dumps(dict(
        scope='An actual mask/error-dependent latent-key coupling, tested with odd errors.',
        limitations='Not a complete FHE construction or Lean theorem. Bare controls expose the '
                    'key on one quarter of keys; raw-source publication leaves four candidate keys. '
                    'Fresh-zero addition uses the latent key; a public-only simulator can compute '
                    'one by selecting a prefix. It produces real cubic controls in the uniform '
                    'source mode too, so it does not supply the missing ordinary-LWE security hop.',
        summary=summary, records=records), indent=2) + '\n')
    print(json.dumps(summary))
    print(f'Wrote {args.output}')


if __name__ == '__main__':
    main()
