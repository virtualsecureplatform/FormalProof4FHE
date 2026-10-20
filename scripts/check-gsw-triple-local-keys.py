#!/usr/bin/env python3
"""Check the triple-local key-list filter and the q/4 torsion guard.

Synthetic local constraints test the public list algorithm. They are NOT
ordinary-LWE-generated views or a security reduction. Confined-source fixtures
separately check the actual character formula and its scaled error bound.
No dense-compiler attack, lattice search, or secure family is asserted.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import random


def centered(value, q):
    residue = value % q
    return residue if 2 * residue <= q else residue - q


def evaluate(coefficients, bits, q):
    return sum(value for monomial, value in enumerate(coefficients) if bits & monomial == monomial) % q


def seven_corner_polynomial(excluded, weight, shift, q):
    delta = {0: 1}
    for row in range(3):
        if excluded & (1 << row):
            delta = {mask | (1 << row): value for mask, value in delta.items()}
        else:
            expanded = {}
            for mask, value in delta.items():
                expanded[mask] = expanded.get(mask, 0) + value
                expanded[mask | (1 << row)] = expanded.get(mask | (1 << row), 0) - value
            delta = expanded
    coefficients = [0] * 8
    coefficients[7] = weight
    for mask, value in delta.items():
        coefficients[mask] -= weight * delta[7] * value
    coefficients[0] += shift
    assert coefficients[7] == 0
    return [value % q for value in coefficients]


def constraints_for(n, key, rng, weight, bound, q, saturation):
    constraints = []
    for triple in itertools.combinations(range(n), 3):
        actual = sum(((key >> row) & 1) << place for place, row in enumerate(triple))
        excluded = 7 if saturation else rng.choice([value for value in range(8) if value != actual])
        shift = 0 if saturation else rng.randint(-bound, bound)
        coefficients = seven_corner_polynomial(excluded, weight, shift, q)
        accepted = [abs(centered((weight if bits == 7 else 0) - evaluate(coefficients, bits, q), q)) <= bound
                    for bits in range(8)]
        assert accepted == [bits != excluded for bits in range(8)]
        assert accepted[actual]
        constraints.append((triple, coefficients, accepted))
    return constraints


def enumerate_public_candidates(n, constraints):
    """Only public constraints are inputs. Check newly complete triples per step."""
    by_last = [[] for _ in range(n)]
    for triple, _, accepted in constraints:
        by_last[triple[2]].append((triple, accepted))
    candidates, prefix_counts, tests = [0], [1], 0
    for last in range(n):
        retained = []
        for prefix in candidates:
            for bit in range(2):
                candidate = prefix | (bit << last)
                for triple, accepted in by_last[last]:
                    pattern = sum(((candidate >> row) & 1) << place for place, row in enumerate(triple))
                    tests += 1
                    if not accepted[pattern]:
                        break
                else:
                    retained.append(candidate)
        candidates = retained
        assert len(candidates) == len(set(candidates))
        size = last + 1
        assert len(candidates) <= 1 + size + size * (size - 1) // 2
        prefix_counts.append(len(candidates))
    # At most two extensions per previous prefix and choose(last,2) new tests.
    cap = 2 * n * (1 + n + n * (n - 1) // 2) * (n * (n - 1) // 2)
    assert tests <= cap
    return candidates, prefix_counts, tests


def exhaustive_candidates(n, constraints):
    return [key for key in range(1 << n) if all(
        accepted[sum(((key >> row) & 1) << place for place, row in enumerate(triple))]
        for triple, _, accepted in constraints)]


def check_key_lists():
    cases = []
    for saturation, sizes in ((True, (0, 1, 2, 3, 8, 16, 24, 32)),
                              (False, (3, 6, 9, 12, 24, 48, 64))):
        for n in sizes:
            seed = 20261020 + n + 1000 * saturation
            rng = random.Random(seed)
            q, bound = 65536, 0 if saturation else 12
            weight = q // 4
            key = 0 if saturation else rng.randrange(1 << n)
            assert 8 * bound < weight
            constraints = constraints_for(n, key, rng, weight, bound, q, saturation)
            candidates, prefixes, tests = enumerate_public_candidates(n, constraints)
            assert key in candidates
            cap = 1 + n + n * (n - 1) // 2
            if saturation:
                expected = {0} | {1 << row for row in range(n)} | {
                    (1 << i) | (1 << j) for i, j in itertools.combinations(range(n), 2)}
                assert set(candidates) == expected
                assert len(candidates) == cap
            if n <= 12:
                assert set(candidates) == set(exhaustive_candidates(n, constraints))
            # Independent source samples only VALIDATE the synthetic list.
            # They are not used to construct the constraints or by enumeration.
            validation = []
            for _ in range(4):
                mask = [rng.randrange(q) for _ in range(n)]
                error = rng.randint(-3, 3)
                body = (sum(value for row, value in enumerate(mask) if key & (1 << row)) + error) % q
                validation.append((mask, body))
            validated = [candidate for candidate in candidates if all(abs(centered(
                body - sum(value for row, value in enumerate(mask) if candidate & (1 << row)), q)) <= 3
                for mask, body in validation)]
            assert validated == [key]
            public_digest = hashlib.sha256(json.dumps(constraints, separators=(",", ":")).encode()).hexdigest()
            cases.append(dict(kind="saturating" if saturation else "planted", n=n, seed=seed,
                              modulus=q, weight=weight, residual_bound=bound, public_digest=public_digest,
                              constraints=len(constraints), prefix_counts=prefixes, candidate_count=len(candidates),
                              candidate_cap=cap, public_constraint_tests=tests, validation_samples=4,
                              validated_candidates=len(validated), exhaustive_oracle_checked=n <= 12))
    return cases


def raw_character_value(head, u, bodies, secret, q):
    """Direct pairPolynomial - lowerPolynomial formula, independent of VC tests."""
    total = 0
    for pair, coefficients in zip(((0, 1), (0, 2), (1, 2)), u):
        i, j = pair
        z = sum(x * y for x, y in zip(coefficients, bodies))
        projected = [sum(x * y for x, y in zip(row, coefficients)) for row in head]
        linear = sum(x * y for x, y in zip(projected, secret))
        lower = linear - 2 * secret[i] * linear - 2 * secret[j] * linear + 4 * (
            projected[i] + projected[j]) * secret[i] * secret[j]
        total += (2 * secret[i] - 1) * (2 * secret[j] - 1) * z - lower
    return total % q


def raw_local_value(head, u, bodies, bits, q):
    return raw_character_value(head, u, bodies, [(bits >> i) & 1 for i in range(3)], q)


def check_confined_sources():
    q, weight, E = 1024, 64, 1
    a = [[0, 0, 0], [0, 0, 0], [16, 0, 0], [256, 512, 768]]
    u = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    scaled = [[4 * x for x in row] for row in u]
    assert any(sum(x * y for x, y in zip(a[3], row)) % q for row in u)
    assert all(4 * sum(x * y for x, y in zip(a[3], row)) % q == 0 for row in u)
    assert abs(centered(raw_local_value(a[:3], u, a[3], 0, q), q)) == 512
    assert 4 * weight % q == q // 4 and 4 * (q // 2) % q == 0
    assert 8 * 12 < q // 4
    checks, failed_unscaled = 0, 0
    for bits, tail, errors in itertools.product(range(8), (0, 1, 2, 3, 17, q - 1),
                                               itertools.product(range(-E, E + 1), repeat=3)):
        secret = [(bits >> i) & 1 for i in range(3)] + [tail]
        bodies = [(sum(a[row][column] * secret[row] for row in range(4)) + errors[column]) % q
                  for column in range(3)]
        target = weight if bits == 7 else 0
        full_error = abs(centered(target - raw_character_value(a, u, bodies, secret, q), q))
        unscaled_error = abs(centered(target - raw_local_value(a[:3], u, bodies, bits, q), q))
        actual_error = abs(centered(4 * target - raw_local_value(a[:3], scaled, bodies, bits, q), q))
        assert full_error <= 3
        assert actual_error <= 12
        failed_unscaled += unscaled_error > 3
        checks += 1
    return dict(source_phase_checks=checks, unscaled_bound_failures=failed_unscaled,
                full_ambient_phase_checks=checks, full_ambient_supported_error_bound=3,
                scaled_supported_error_bound=12, scaled_target=256, modulus=q,
                nonzero_outside_projection=True, top_weight_annihilated=True)


def report():
    cases = check_key_lists()
    return dict(version=1, scope="Triple-local shortcut filter; no dense attack or full LWE reduction.",
                list_cases=cases, confined_source=check_confined_sources(),
                summary=dict(list_cases=len(cases), max_n=max(c["n"] for c in cases),
                             exhaustive_list_cases=sum(c["exhaustive_oracle_checked"] for c in cases),
                             public_constraint_tests=sum(c["public_constraint_tests"] for c in cases),
                             max_candidates=max(c["candidate_count"] for c in cases)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-existing", type=Path)
    args = parser.parse_args()
    result = report()
    if args.verify_existing:
        assert json.loads(args.verify_existing.read_text()) == result
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(summary=result["summary"], confined_source=result["confined_source"]), sort_keys=True))


if __name__ == "__main__":
    main()
