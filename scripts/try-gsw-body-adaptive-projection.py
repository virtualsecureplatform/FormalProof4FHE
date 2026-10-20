#!/usr/bin/env python3
"""Try public factors GP=C, CP=C and right-acting native CMux.

The builder sees only G,C and uses public LLL/Babai preimages. Its failure is
recorded without resampling; that control uses signed canonical digits as a
fallback. Finite correctness results do not supply a secure parameter family.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import random

import numpy as np
from fpylll import GSO, IntegerMatrix

spec = importlib.util.spec_from_file_location(
    "projection_redundant", Path(__file__).with_name("try-gsw-redundant-digits.py"))
redundant = importlib.util.module_from_spec(spec)
spec.loader.exec_module(redundant)
t = redundant.midpoint.transcript


def public_short_preimages(stacked, targets, q):
    """Checked public modular preimages with exact lattice combinations."""
    solve = t.remaining.lattice_solver(stacked.tolist(), q)
    # Reconstruct the nearby lattice vector from integer basis coefficients.
    # Direct CVP.babai returned a non-kernel vector on a structured q=65536
    # instance; exact certificates caught it. This path checks the reduced
    # basis and forms every nearby vector by an exact integer combination.
    basis = solve.kernel_basis()
    assert all(all(sum(int(a) * int(b) for a, b in zip(row, v)) % q == 0
                   for row in stacked) for v in basis)
    reduced = stacked.tolist()
    rows, width = stacked.shape
    transform = [[int(i == j) for j in range(rows)] for i in range(rows)]
    pivots = []
    for column in range(width):
        rank = len(pivots)
        pivot = next((i for i in range(rank, rows) if reduced[i][column] % 2), None)
        if pivot is None:
            continue
        for matrix in (reduced, transform):
            matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(reduced[rank][column] % q, -1, q)
        reduced[rank] = [x * inverse % q for x in reduced[rank]]
        transform[rank] = [x * inverse % q for x in transform[rank]]
        for i in range(rows):
            if i == rank:
                continue
            coefficient = reduced[i][column]
            reduced[i] = [(x - coefficient * y) % q for x, y in zip(reduced[i], reduced[rank])]
            transform[i] = [(x - coefficient * y) % q for x, y in zip(transform[i], transform[rank])]
        pivots.append(column)
        if len(pivots) == rows:
            break
    assert len(pivots) == rows
    lattice = IntegerMatrix.from_matrix(basis)
    orthogonalized = GSO.Mat(lattice, update=True)
    columns = []
    for column in range(targets.shape[1]):
        target = targets[:, column].tolist()
        particular = [0] * width
        for i, pivot in enumerate(pivots):
            particular[pivot] = t.centered(sum(a * b for a, b in zip(transform[i], target)), q)
        assert all(sum(int(a) * b for a, b in zip(row, particular)) % q == expected
                   for row, expected in zip(stacked, target))
        coefficients = orthogonalized.babai(particular)
        nearby = [sum(int(coefficients[i]) * basis[i][j] for i in range(width)) for j in range(width)]
        columns.append([x - y for x, y in zip(particular, nearby)])
    factor = np.array(columns, dtype=np.int64).T
    assert np.array_equal(stacked @ factor % q, targets % q)
    return factor


def public_factor(g, control, q, levels):
    """No key, source errors, plaintext or diagnostic target is an argument."""
    targets = np.vstack((control, control))
    try:
        factor = public_short_preimages(np.vstack((g, control)), targets, q)
    except ValueError as error:
        factor = redundant.signed_quarter_digits(control, levels)
        return factor, {"failure": str(error), "fallback": "signed canonical digits"}
    assert np.array_equal(g @ factor % q, control)
    assert np.array_equal(control @ factor % q, control)
    return factor, {"preimage_columns": int(control.shape[1]),
                    "certified_scalar_equations": int(targets.size),
                    "max_digit": int(np.max(np.abs(factor))),
                    "max_column_l1": int(np.max(np.sum(np.abs(factor), axis=0))),
                    "globally_idempotent": bool(np.array_equal(factor @ factor % q, factor % q))}


def draw(n, levels, radius, seed, variant):
    rng, q = random.Random(seed), 1 << levels
    secret = np.array([rng.randrange(2) for _ in range(n)], dtype=np.int64)
    m, g = (n + 1) * levels + 80, t.gadget(n, levels)
    a = np.array([[rng.randrange(q) for _ in range(m)] for _ in range(n)], dtype=np.int64)
    source_error = np.array([rng.randint(-radius, radius) for _ in range(m)], dtype=np.int64)
    source = np.vstack(((secret @ a + source_error) % q, a))
    width, controls = g.shape[1], []
    for i in range(n):
        raw = np.array([[rng.randrange(q) for _ in range(width)] for _ in range(n)], dtype=np.int64)
        fresh = np.array([rng.randint(-radius, radius) for _ in range(width)], dtype=np.int64)
        h, c = np.zeros_like(raw), np.zeros(width, dtype=np.int64)
        for row in range(n + 1):
            for level in range(levels):
                column, w = row * levels + level, 1 << level
                if row == 0:
                    h[i, column] = w
                elif row - 1 == i and variant == "exact_diagonal":
                    h[i, column] = -w
                else:
                    c[column] = w // 4
                    h[i, column] -= w // 2
                    h[row - 1, column] -= w // 2
        control = np.vstack(((secret @ raw + fresh + c) % q, (raw - h) % q))
        predicted = (fresh + c + secret @ h - int(secret[i]) * t.phase(g, secret, q)) % q
        assert np.array_equal((t.phase(control, secret, q) - int(secret[i]) * t.phase(g, secret, q)) % q, predicted)
        controls.append(control)
    initial = [(source @ np.array([[rng.randrange(2) for _ in range(width)] for _ in range(m)], dtype=np.int64)
                + bit * g) % q for bit in (0, 1)]
    return secret, controls, initial


def refresh(ciphertext, controls, factors, levels, q, lookup, policy):
    g, n = t.gadget(len(controls), levels), len(controls)
    switched = [(int(x) // (q // lookup)) % lookup for x in ciphertext[:, levels - 1]]
    state = np.zeros((lookup, *g.shape), dtype=np.int64)
    state[switched[0]] = g
    for i in reversed(range(n)):
        old = state
        if policy == "left_signed":
            state = np.array([(old[pos] + controls[i] @ redundant.signed_quarter_digits(
                (old[(pos + switched[i + 1]) % lookup] - old[pos]) % q, levels)) % q
                for pos in range(lookup)], dtype=np.int64)
        else:
            state = np.array([(old[pos] + (old[(pos + switched[i + 1]) % lookup] - old[pos]) @ factors[i]) % q
                              for pos in range(lookup)], dtype=np.int64)
    selected = [pos for pos in range(lookup) if abs(t.centered(pos - lookup // 2, lookup)) < abs(t.centered(pos, lookup))]
    return np.sum(state[selected], axis=0) % q


def single_control_check(g, control, factor, q):
    # A publicly checkable algebraic test with 17 uses of the same control.
    lookup, body, weight, steps = 16, 3, 5, 17
    state = np.zeros((lookup, *g.shape), dtype=np.int64)
    state[body] = g
    for _ in range(steps):
        old = state
        state = np.array([(old[pos] + (old[(pos + weight) % lookup] - old[pos]) @ factor) % q
                          for pos in range(lookup)], dtype=np.int64)
    expected = np.zeros_like(state)
    expected[body] = (g - control) % q
    expected[(body - steps * weight) % lookup] = (expected[(body - steps * weight) % lookup] + control) % q
    assert np.array_equal(state, expected)
    return lookup * int(g.size)


def experiment(n, levels, radius, seed, variant):
    q, lookup = 1 << levels, 1 << (4 * (n + 1)).bit_length()
    secret, controls, initial = draw(n, levels, radius, seed, variant)
    g = t.gadget(n, levels)
    canonical = [redundant.signed_quarter_digits(control, levels) for control in controls]
    repaired, builders, repeat_checks = [], [], 0
    for control in controls:
        factor, record = public_factor(g, control, q, levels)
        assert np.array_equal(g @ factor % q, control)
        if "failure" not in record:
            repeat_checks += single_control_check(g, control, factor, q)
        repaired.append(factor)
        builders.append(record)
    phase_g = t.phase(g, secret, q)
    errors = [(t.phase(control, secret, q) - int(bit) * phase_g) % q
              for control, bit in zip(controls, secret)]
    eigen_checks = cross_checks = cross_correct = cross_count = 0
    cross_maxima, commutators = [], []
    for i in range(n):
        if "failure" not in builders[i]:
            assert np.array_equal(errors[i] @ repaired[i] % q, (1 - int(secret[i])) * errors[i] % q)
            eigen_checks += int(g.shape[1])
        for j in range(n):
            if i == j:
                continue
            product = controls[i] @ repaired[j] % q
            error = (t.phase(product, secret, q) - int(secret[i] * secret[j]) * phase_g) % q
            assert np.array_equal(error, (errors[i] @ repaired[j] + int(secret[i]) * errors[j]) % q)
            cross_checks += int(g.shape[1])
            cross_maxima.append(max(abs(t.centered(int(value), q)) for value in error))
            phase = int(t.phase(product, secret, q)[levels - 1])
            decoded = int(abs(t.centered(phase - q // 2, q)) < abs(t.centered(phase, q)))
            cross_correct += decoded == int(secret[i] * secret[j])
            cross_count += 1
            commutator = (controls[i] @ repaired[j] - controls[j] @ repaired[i]) % q
            commutators.append(bool(np.any(commutator)))
    policies = []
    for policy, factors in (("left_signed", canonical), ("right_canonical", canonical), ("right_self_stable", repaired)):
        current, trials = [c.copy() for c in initial], []
        for cycle in range(3):
            output = []
            for branch in (0, 1):
                before = current[branch] if cycle == 0 else (
                    g - current[branch] @ redundant.signed_quarter_digits(initial[0], levels)) % q
                expected = branch if cycle == 0 else 1
                after = refresh(before, controls, factors, levels, q, lookup, policy)
                phase = int(t.phase(after, secret, q)[levels - 1])
                decoded = int(abs(t.centered(phase - q // 2, q)) < abs(t.centered(phase, q)))
                bound = max(map(abs, t.noise(after, expected, secret, g, q)))
                trials.append({"cycle": cycle, "branch": branch, "correct": decoded == expected,
                               "output_noise": bound, "output_decoding_margin": 4 * bound < q,
                               "next_signed_nand_rounding_margin": 2 * ((g.shape[1] + 1) * bound
                                   + (n + 1) * (q // lookup - 1)) < q // 2})
                output.append(after)
            current = output
        policies.append({"policy": policy, "refresh_trials": trials})
    result = {"n": n, "levels": levels, "fresh_error_bound": radius, "seed": seed, "variant": variant,
              "uniform_binary_key_draw": True, "source_resampled": False,
              "secret_for_diagnostic": secret.tolist(), "control_phase_checks": n * int(g.shape[1]),
              "builders": builders, "single_control_repeated_scalar_checks": repeat_checks,
              "self_error_eigen_checks": eigen_checks, "cross_error_checks": cross_checks,
              "cross_products": cross_count, "cross_products_selected_correct": cross_correct,
              "cross_product_max_column_errors": cross_maxima,
              "nonzero_public_commutators": sum(commutators),
              "policies": policies}
    print(json.dumps({"n": n, "levels": levels, "seed": seed, "variant": variant,
                      "builder_failures": sum("failure" in b for b in builders),
                      "correct": [sum(t["correct"] for t in p["refresh_trials"]) for p in policies]}), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    params = [(2, 8, 1), (2, 16, 1), (3, 8, 1), (3, 16, 1), (4, 16, 1)]
    cases = [experiment(*param, 15000 + 10 * index + repeat, variant)
             for index, param in enumerate(params) for repeat in range(2)
             for variant in ("exact_diagonal", "full_signed_outer_product")]
    summaries = []
    for policy in ("left_signed", "right_canonical", "right_self_stable"):
        trials = [trial for case in cases for p in case["policies"] if p["policy"] == policy for trial in p["refresh_trials"]]
        summaries.append({"policy": policy, "refresh_calls": len(trials), "selected_correct": sum(t["correct"] for t in trials),
                          "output_margins": sum(t["output_decoding_margin"] for t in trials),
                          "next_nand_margins": sum(t["next_signed_nand_rounding_margin"] for t in trials)})
    result = {"scope": "Public body-adaptive self-stable factors and complete small native refresh cycles",
              "limitations": "Finite diagnostics, explicit builder failures/fallbacks; no shortness/failure asymptotic or complete security theorem",
              "cases": cases, "summaries": summaries,
              "control_phase_checks": sum(c["control_phase_checks"] for c in cases),
              "successful_builders": sum("failure" not in b for c in cases for b in c["builders"]),
              "failed_builders": sum("failure" in b for c in cases for b in c["builders"]),
              "single_control_repeated_scalar_checks": sum(c["single_control_repeated_scalar_checks"] for c in cases),
              "self_error_eigen_checks": sum(c["self_error_eigen_checks"] for c in cases),
              "cross_error_checks": sum(c["cross_error_checks"] for c in cases),
              "cross_products": sum(c["cross_products"] for c in cases),
              "cross_products_selected_correct": sum(c["cross_products_selected_correct"] for c in cases),
              "nonzero_public_commutators": sum(c["nonzero_public_commutators"] for c in cases)}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("summaries", "control_phase_checks", "successful_builders", "failed_builders",
                                            "single_control_repeated_scalar_checks", "self_error_eigen_checks",
                                            "cross_error_checks", "cross_products", "cross_products_selected_correct",
                                            "nonzero_public_commutators")}, sort_keys=True))


if __name__ == "__main__":
    main()
