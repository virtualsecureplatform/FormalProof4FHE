#!/usr/bin/env python3
"""Public three-corner correction and polynomial candidate-key extraction.

Sources and keys are drawn once, without correctness-conditioned resampling.
Large dimensions test source/candidate logic only; small dimensions also run
three refresh cycles under the same secret. These are finite diagnostics.
"""
import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import random

import numpy as np

spec = importlib.util.spec_from_file_location(
    "rotated", Path(__file__).with_name("try-gsw-rotated-trapdoor-source.py"))
rotated = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rotated)
transcript = rotated.transcript


def satisfiable(n, forbidden, prefix):
    """2SAT feasibility by two DFS passes on the implication graph."""
    graph, reverse = [[] for _ in range(2 * n)], [[] for _ in range(2 * n)]

    def edge(a, b):
        graph[a].append(b)
        reverse[b].append(a)

    for i, j, a, b in forbidden:
        edge(2 * i + a, 2 * j + 1 - b)
        edge(2 * j + b, 2 * i + 1 - a)
    for i, a in enumerate(prefix):
        edge(2 * i + 1 - a, 2 * i + a)
    seen, order = set(), []

    def visit(v):
        if v not in seen:
            seen.add(v)
            for u in graph[v]:
                visit(u)
            order.append(v)

    for v in range(2 * n):
        visit(v)
    components = [-1] * (2 * n)

    def assign(v, label):
        if components[v] == -1:
            components[v] = label
            for u in reverse[v]:
                assign(u, label)

    for label, v in enumerate(reversed(order)):
        assign(v, label)
    return all(components[2 * i] != components[2 * i + 1] for i in range(n))


def candidates(n, forbidden):
    prefixes, calls = [()], 0
    for _ in range(n):
        extended = []
        for prefix in prefixes:
            for bit in (0, 1):
                calls += 1
                child = (*prefix, bit)
                if satisfiable(n, forbidden, child):
                    extended.append(child)
        prefixes = extended
        # Each live prefix extends some complete solution, so this bound also
        # holds at intermediate levels for complete pair constraints.
        assert len(prefixes) <= n + 1
    assert calls <= 2 * n * (n + 1)
    return prefixes, calls


def coefficients(a, b, w):
    # The tuple is the excluded assignment, not an estimate supplied privately.
    return {(0, 0): (w, -w, -w), (0, 1): (0, 0, -w),
            (1, 0): (0, -w, 0), (1, 1): (0, 0, 0)}[a, b]


def check_solver():
    checked = 0
    rng = random.Random(13000)
    for n in (0, 1, 2, 3, 4):
        pairs = list(itertools.combinations(range(n), 2))
        assignments = (itertools.product(range(4), repeat=len(pairs)) if n <= 3
                       else ([rng.randrange(4) for _ in pairs] for _ in range(128)))
        for values in assignments:
            forbidden = [(i, j, value // 2, value % 2)
                         for (i, j), value in zip(pairs, values)]
            expected = [key for key in itertools.product((0, 1), repeat=n)
                        if all((key[i], key[j]) != (a, b) for i, j, a, b in forbidden)]
            actual, _ = candidates(n, forbidden)
            assert actual == expected
            checked += 1
    for excluded in itertools.product((0, 1), repeat=2):
        for w in (1, 2, 32768):
            c, x, y = coefficients(*excluded, w)
            for a, b in itertools.product((0, 1), repeat=2):
                delta = c + x * a + y * b + w * a * b
                assert (delta != 0) == ((a, b) == excluded)
                assert abs(delta) == (w if (a, b) == excluded else 0)
    return checked


def experiment(n, levels, radius, seed, refresh):
    rng, q = random.Random(seed), 1 << levels
    m0, pool = (n + 1) * levels + 80, 64
    secret = np.array([rng.randrange(2) for _ in range(n)], dtype=np.int64)
    base = np.array([[rng.randrange(q) for _ in range(m0)] for _ in range(n)], dtype=np.int64)
    blocks = [np.array([[rng.randrange(q) for _ in range(n)] for _ in range(n)], dtype=np.int64)
              for _ in range(pool)]
    inverses = [rotated.inverse_mod(block, q) for block in blocks]
    selected = next((i for i, inv in enumerate(inverses) if inv is not None), None)
    masks = np.hstack([base, *blocks])
    errors = np.array([rng.randint(-radius, radius) for _ in range(masks.shape[1])], dtype=np.int64)
    bodies = (secret @ masks + errors) % q
    result = {"n": n, "levels": levels, "source_radius": radius, "seed": seed,
              "uniform_binary_key_draw": True, "source_resampled": False,
              "selected_rotation": selected, "refresh_enabled": refresh, "refresh_trials": []}
    if selected is None:
        result["failure"] = "No invertible block in the fixed public pool"
        return result
    begin = m0 + selected * n
    inverse = inverses[selected]
    # Everything below used by the compiler depends only on public bodies/masks.
    proxy = inverse.T @ bodies[begin:begin + n] % q
    excluded = [1 - int(z % 2) for z in proxy]
    forbidden = [(i, j, excluded[i], excluded[j])
                 for i, j in itertools.combinations(range(n), 2)]
    possible, calls = candidates(n, forbidden)
    # Independent verification sample is not passed to the compiler.
    verify_mask = [rng.randrange(q) for _ in range(n)]
    verify_error = rng.randint(-radius, radius)
    verify_body = (sum(int(s) * a for s, a in zip(secret, verify_mask)) + verify_error) % q
    verified = [key for key in possible if abs(transcript.centered(
        verify_body - sum(s * a for s, a in zip(key, verify_mask)), q)) <= radius]
    eta = inverse.T @ errors[begin:begin + n] % q
    assert np.array_equal(proxy, (secret + eta) % q)
    odd_weight = sum(int(z % 2) for z in eta)
    actual_included = tuple(int(s) for s in secret) in possible
    assert actual_included == (odd_weight <= 1)
    result.update(candidate_count=len(possible), solver_feasibility_calls=calls,
                  candidate_contains_actual_key=actual_included,
                  verification_candidates=len(verified),
                  verification_recovers_actual_key=(verified == [tuple(int(s) for s in secret)]),
                  selected_source_error_nonzero=bool(np.any(errors[begin:begin + n])),
                  inverse_error_odd_weight=odd_weight,
                  ideal_verification_union_bound=(n + 1) * (2 * radius + 1) / q)
    if not refresh:
        return result
    g = transcript.gadget(n, levels)
    width = g.shape[1]
    controls, residual_max = [], 0
    for i in range(n):
        raw = np.array([[rng.randrange(q) for _ in range(width)] for _ in range(n)], dtype=np.int64)
        fresh = np.array([rng.randint(-radius, radius) for _ in range(width)], dtype=np.int64)
        shift, constant = np.zeros((n, width), dtype=np.int64), np.zeros(width, dtype=np.int64)
        residual = np.zeros(width, dtype=np.int64)
        for row in range(n + 1):
            for level in range(levels):
                column, w = row * levels + level, 1 << level
                if row == 0:
                    shift[i, column] = w
                elif row - 1 == i:
                    shift[i, column] = -w
                else:
                    j = row - 1
                    c, x, y = coefficients(excluded[i], excluded[j], w)
                    constant[column], shift[i, column], shift[j, column] = c, x, y
                    residual[column] = (c + x * secret[i] + y * secret[j] + w * secret[i] * secret[j]) % q
        control = np.vstack(((secret @ raw + fresh + constant) % q, (raw - shift) % q))
        # Native phase is body - secret dot mask; raw-shift adds the affine phase.
        assert transcript.noise(control, secret[i], secret, g, q) == [
            transcript.centered(int(v), q) for v in (fresh + residual) % q]
        residual_max = max(residual_max, max(abs(transcript.centered(int(v), q)) for v in residual))
        controls.append(control)
    assert (residual_max == 0) == actual_included
    result.update(max_compiler_residual=residual_max,
                  phase_checks=n * width,
                  max_control_noise=max(abs(v) for i, c in enumerate(controls)
                                        for v in transcript.noise(c, secret[i], secret, g, q)))
    public_key = np.vstack((bodies, masks))
    initial = [(public_key @ np.array([[rng.randrange(2) for _ in range(width)]
                                      for _ in range(masks.shape[1])], dtype=np.int64) + bit * g) % q
               for bit in (0, 1)]
    lookup = 1 << (4 * (n + 1)).bit_length()
    current = [c.copy() for c in initial]
    for cycle in range(3):
        output = []
        for branch in (0, 1):
            before = current[branch] if cycle == 0 else (
                g - current[branch] @ transcript.digits(initial[0], levels)) % q
            expected = branch if cycle == 0 else 1
            after = transcript.refresh(before, controls, levels, q, lookup)
            input_bound = max(map(abs, transcript.noise(before, expected, secret, g, q)))
            output_bound = max(map(abs, transcript.noise(after, expected, secret, g, q)))
            selected_phase = int(transcript.phase(after, secret, q)[levels - 1])
            decoded = int(abs(transcript.centered(selected_phase - q // 2, q)) <
                          abs(transcript.centered(selected_phase, q)))
            result["refresh_trials"].append({"cycle": cycle, "branch": branch,
                "correct": decoded == expected, "input_noise": input_bound, "output_noise": output_bound,
                "input_rounding_margin": 2 * (input_bound + (n + 1) * (q // lookup - 1)) < q // 2,
                "output_decoding_margin": 4 * output_bound < q,
                "next_nand_rounding_margin": 2 * ((width + 1) * output_bound +
                                                  (n + 1) * (q // lookup - 1)) < q // 2})
            output.append(after)
        current = output
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    solver_checks = check_solver()
    settings = [(n, 16 if n == 2 else 24, radius, True)
                for n in (2, 3, 4) for radius in (1, 64)]
    settings += [(n, 16, radius, False) for n in (16, 32) for radius in (1, 64)]
    cases = [experiment(n, levels, radius, 13100 + 10 * index + repeat, refresh)
             for index, (n, levels, radius, refresh) in enumerate(settings)
             for repeat in range(4 if refresh else 2)]
    trials = [t for c in cases for t in c["refresh_trials"]]
    totals = {"attempts": len(cases), "solver_cross_checks": solver_checks,
              "compiler_success_cases": sum(c.get("candidate_contains_actual_key", False) for c in cases),
              "public_key_recovery_cases": sum(c.get("verification_recovers_actual_key", False) for c in cases),
              "phase_checks": sum(c.get("phase_checks", 0) for c in cases),
              "refresh_calls": len(trials), "selected_correct": sum(t["correct"] for t in trials),
              "output_margins": sum(t["output_decoding_margin"] for t in trials),
              "next_nand_margins": sum(t["next_nand_rounding_margin"] for t in trials)}
    args.output.write_text(json.dumps({"scope": "Public pair-local correction diagnostics, not a secure FHE construction",
                                       "totals": totals, "cases": cases}, indent=2) + "\n")
    print(json.dumps(totals, sort_keys=True))


if __name__ == "__main__":
    main()
