#!/usr/bin/env python3
"""Public transcript-dependent builders and three companion architecture tests.

All construction functions receive public data only. Hidden keys/errors are
used exclusively by diagnostics. Finite examples are not asymptotic security,
negligible-failure, or efficient useful-builder guarantees. Requires numpy,
fpylll 0.6.4 and cysignals; no matrix resampling or hidden trapdoor.
"""

import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import random

import numpy as np

spec = importlib.util.spec_from_file_location(
    "remaining", Path(__file__).with_name("try-gsw-remaining-routes.py"))
remaining = importlib.util.module_from_spec(spec)
spec.loader.exec_module(remaining)
centered = remaining.centered


def digits(ciphertext, levels):
    return np.vstack([(row >> level) & 1
                      for row in ciphertext for level in range(levels)])


def gadget(n, levels):
    result = np.zeros((n + 1, (n + 1) * levels), dtype=np.int64)
    for row in range(n + 1):
        for level in range(levels):
            result[row, row * levels + level] = 1 << level
    return result


def phase(ciphertext, secret, q):
    return (np.array([1, *[-s for s in secret]], dtype=np.int64) @ ciphertext) % q


def noise(ciphertext, bit, secret, g, q):
    return [centered(int(x), q) for x in (phase(ciphertext, secret, q) - bit * phase(g, secret, q)) % q]


def bootstrap(controls, weights, body, levels, q, lookup):
    """Actual vector accumulator, with native gadget digits at every CMux."""
    n = len(controls)
    g = gadget(n, levels)
    state = np.zeros((lookup, *g.shape), dtype=np.int64)
    state[body] = g
    # Lean runStored processes the tail first.
    for index in reversed(range(n)):
        old = state
        state = np.array([(old[pos] + controls[index] @ digits(
            (old[(pos + weights[index]) % lookup] - old[pos]) % q, levels)) % q
            for pos in range(lookup)], dtype=np.int64)
    selected = [pos for pos in range(lookup)
                if abs(centered(pos - lookup // 2, lookup)) < abs(centered(pos, lookup))]
    return np.sum(state[selected], axis=0) % q


def refresh(ciphertext, controls, levels, q, lookup):
    factor = q // lookup
    # Match GSWModulusSwitch.down: unsigned floor division.
    switched = [(int(x) // factor) % lookup
                for x in ciphertext[:, levels - 1]]
    return bootstrap(controls, switched[1:], switched[0], levels, q, lookup)


def dense_pool(a, body, q):
    n, m = len(a), len(a[0])
    pairs, system = remaining.quadratic_system(a)
    solve = remaining.lattice_solver(system, q)
    kernel = sorted(solve.kernel_basis(), key=lambda v: sum(abs(x) for x in v))[:12]

    def build(first, second, weight, mode):
        target = [weight * int((i, j) == tuple(sorted((first, second)))) for i, j in pairs]
        original = solve(target)
        candidates = [original] + [[x + sign * y for x, y in zip(original, v)]
                                    for v in kernel for sign in (-1, 1)]

        def correction(v):
            return [centered(sum(v[r * m + c] * body[c] for c in range(m)), q)
                    for r in range(n)]

        if mode == "l1":
            chosen = min(candidates, key=lambda v: sum(map(abs, v)))
        else:
            chosen = min(candidates, key=lambda v: (sum(map(abs, correction(v))), sum(map(abs, v))))
        assert all(sum(x * y for x, y in zip(row, chosen)) % q == t % q
                   for row, t in zip(system, target))
        return np.array(chosen, dtype=np.int64).reshape(n, m)

    return build, solve


def experiment(n, m, q, radius, seed):
    rng = random.Random(seed)
    levels = q.bit_length() - 1
    a = [[rng.randrange(q) for _ in range(m)] for _ in range(n)]
    secret = [rng.randrange(2) for _ in range(n)]
    error = [rng.randint(-radius, radius) for _ in range(m)]
    body = [(sum(a[r][c] * secret[r] for r in range(n)) + error[c]) % q for c in range(m)]
    try:
        build, _ = dense_pool(a, body, q)
    except ValueError as exc:
        return {"n": n, "m": m, "q": q, "radius": radius, "seed": seed,
                "failure": str(exc), "source_resampled": False}
    try:
        linear = remaining.lattice_solver(a, q)
        recovery = []
        for i in range(n):
            v = linear([q // 2 * int(i == r) for r in range(n)])
            value = sum(x * y for x, y in zip(v, body)) % q
            guess = int(abs(centered(value - q // 2, q)) < abs(centered(value, q)))
            recovery.append({"coordinate": i, "l1": sum(map(abs, v)),
                             "worst_case_decode_margin": 2 * radius * sum(map(abs, v)) < q // 2,
                             "sample_guess_correct": guess == secret[i]})
    except ValueError as exc:
        recovery = [{"failure": str(exc)}]
    g = gadget(n, levels)
    width = (n + 1) * levels
    raw_masks = np.array([[[rng.randrange(q) for _ in range(width)] for _ in range(n)]
                         for _ in range(n)], dtype=np.int64)
    fresh_errors = np.array([[rng.randint(-radius, radius) for _ in range(width)]
                            for _ in range(n)], dtype=np.int64)
    source = np.array([body, *a], dtype=np.int64)
    initial = [(source @ np.array([[rng.randrange(2) for _ in range(width)] for _ in range(m)],
                                  dtype=np.int64) + bit * g) % q for bit in (0, 1)]
    result = {"n": n, "m": m, "q": q, "radius": radius, "seed": seed,
              "diagnostic_secret_hamming_weight": sum(secret), "diagnostic_error_l1": sum(map(abs, error)),
              "source_resampled": False, "linear_recovery_filter": recovery, "modes": []}
    for mode in ("l1", "public_body"):
        controls, records = [], []
        # The builder sees A,y, target, and mode, never secret or errors.
        cache = {}
        for index in range(n):
            h = np.zeros((n, width), dtype=np.int64)
            residual_prediction = np.zeros(width, dtype=np.int64)
            for row in range(n + 1):
                for level in range(levels):
                    column, weight = row * levels + level, 1 << level
                    if row == 0:
                        h[index, column] = weight
                    elif row - 1 == index:
                        h[index, column] = -weight
                    else:
                        other = row - 1
                        key = (tuple(sorted((index, other))), level)
                        if key not in cache:
                            cache[key] = build(index, other, -weight, mode)
                        b = cache[key]
                        h[:, column] = b @ np.array(body, dtype=np.int64) % q
                        # Observer only: actual shared residual, independent of construction choices.
                        residual_prediction[column] = int(np.array(secret) @ b @ np.array(error))
                        records.append({"control": index, "row": other, "level": level,
                                        "l1": sum(abs(int(x)) for x in b.flat),
                                        "correction_l1": sum(abs(centered(int(x), q)) for x in h[:, column]),
                                        "actual_shared_residual": centered(int(residual_prediction[column]), q)})
            masks = (raw_masks[index] - h) % q
            bodies = (np.array(secret, dtype=np.int64) @ raw_masks[index] + fresh_errors[index]) % q
            control = np.vstack((bodies, masks))
            assert noise(control, secret[index], secret, g, q) == [centered(int(x), q)
                    for x in (fresh_errors[index] + residual_prediction) % q]
            controls.append(control)
        ctrl_bound = max(abs(x) for i, c in enumerate(controls)
                         for x in noise(c, secret[i], secret, g, q))
        lookup = 1 << (4 * (n + 1)).bit_length()
        lookup = min(lookup, q)
        trials = []
        current = [x.copy() for x in initial]
        for cycle in range(3):
            next_ciphertexts = []
            for bit in (0, 1):
                # Repeat NAND + refresh without changing controls or secret.
                if cycle:
                    other = initial[0]
                    before = (g - current[bit] @ digits(other, levels)) % q
                    message = 1
                else:
                    before, message = current[bit], bit
                after = refresh(before, controls, levels, q, lookup)
                input_bound = max(map(abs, noise(before, message, secret, g, q)))
                input_phase = int(phase(before, secret, q)[levels - 1])
                input_decoded = int(abs(centered(input_phase - q // 2, q)) < abs(centered(input_phase, q)))
                out_phase = int(phase(after, secret, q)[levels - 1])
                decoded = int(abs(centered(out_phase - q // 2, q)) < abs(centered(out_phase, q)))
                trials.append({"cycle": cycle, "input_branch": bit, "expected": message,
                               "decoded": decoded, "correct": decoded == message,
                               "input_noise": input_bound, "input_decoded": input_decoded,
                               "input_decodes_as_expected": input_decoded == message,
                               "rounding_margin_verified": 2 * (input_bound + (n + 1) * (q // lookup - 1)) < q // 2,
                               "output_noise": max(map(abs, noise(after, message, secret, g, q)))})
                next_ciphertexts.append(after)
            current = next_ciphertexts
        for trial in trials:
            trial["output_decoding_margin_verified"] = 4 * trial["output_noise"] < q
            trial["nand_then_rounding_margin_from_actual_output"] = (
                2 * ((width + 1) * trial["output_noise"] +
                     (n + 1) * (q // lookup - 1)) < q // 2)
        result["modes"].append({"mode": mode, "certificates_checked": len(records),
                                "max_l1": max(r["l1"] for r in records),
                                "max_control_noise": ctrl_bound, "lookup": lookup,
                                "triangle_output_bound": lookup * n * width * ctrl_bound,
                                "refresh_trials": trials, "records": records})
    return result


def correlated_error_attempt():
    q, n, levels, lookup = 256, 2, 8, 16
    g = gadget(n, levels)
    records = []
    for secret in itertools.product((0, 1), repeat=n):
        errors = np.zeros(g.shape[1], dtype=np.int64)
        errors[levels - 1] = 3 * q // 8
        controls = []
        for i, sign in enumerate((1, -1)):
            c = secret[i] * g.copy()
            c[0] = (c[0] + sign * errors) % q
            controls.append(c)
        assert np.all(np.array(noise(controls[0], secret[0], secret, g, q)) +
                      np.array(noise(controls[1], secret[1], secret, g, q)) == 0)
        out = bootstrap(controls, [lookup // 2, 0], lookup // 2 * secret[0], levels, q, lookup)
        vector = noise(out, 0, secret, g, q)
        value = int(phase(out, secret, q)[levels - 1])
        decoded = int(abs(centered(value - q // 2, q)) < abs(centered(value, q)))
        assert decoded == 1
        records.append({"key": list(secret), "zero_sum_control_errors": True,
                        "output_error_nonzero": any(vector), "max_output_error": max(map(abs, vector)),
                        "expected": 0, "decoded": decoded})
    assert any(r["output_error_nonzero"] for r in records)
    return {"scope": "Functional cancellation counterexample; no claimed secure key law",
            "records": records}


def shifted_source_attempt():
    q, n, levels, radius = 256, 3, 8, 1
    rng = random.Random(731)
    # Two WWW-style gadget-shifted matrix labels differing in one block.
    g = gadget(n - 1, levels)
    base = np.array([[rng.randrange(q) for _ in range(n * levels)] for _ in range(n)], dtype=np.int64)
    first, second = base, (base - g) % q
    checked = 0
    for secret in itertools.product((0, 1), repeat=n):
        for e1 in itertools.product((-1, 0, 1), repeat=n):
            for e2 in itertools.product((-1, 0, 1), repeat=n):
                y1 = np.array(secret) @ first % q
                y2 = np.array(secret) @ second % q
                for i in range(n):
                    col = i * levels + levels - 1
                    difference = int(y1[col] - y2[col] + e1[i] - e2[i]) % q
                    guess = int(abs(centered(difference - q // 2, q)) < abs(centered(difference, q)))
                    assert guess == secret[i]
                checked += 1
    return {"q": q, "n": n, "error_radius": radius, "joint_cases": checked,
            "recovered": "all bits in every enumerated case",
            "scope": "Two honest zero batches under one key at publicly gadget-shifted matrices; not an attack on WWW25"}


def direct_game_attempt():
    """A positive-rank lossy endpoint with a surviving invisible coordinate."""
    q, n, weight = 256, 3, 128
    checked = 0
    # Rank two, not the previously tested rank-zero replacement.
    lossy_factor = [[1, 0], [0, 1], [0, 0]]
    coefficients = [37, 91]
    mask = [sum(x * y for x, y in zip(row, coefficients)) for row in lossy_factor]
    for secret in itertools.product((0, 1), repeat=n):
        for error in (-1, 0, 1):
            control_body = (sum(s * a for s, a in zip(secret, mask)) + weight * secret[2] + error) % q
            # Condition on leaked projection s0,s1, as a lossy entropy proof may do.
            projected = (control_body - sum(secret[i] * mask[i] for i in (0, 1))) % q
            guessed = int(abs(centered(projected - weight, q)) < abs(centered(projected, q)))
            assert guessed == secret[2]
            checked += 1
    return {"lossy_rank": 2, "lossy_factor": lossy_factor, "key_dimension": n, "q": q, "cases": checked,
            "remaining_coordinate_recovered_given_lossy_projection": True,
            "scope": "This coordinate-aligned statistical lossy endpoint fails; not every direct-game reduction"}


def convert_with_auxiliary(ciphertext, auxiliary, q):
    """Public conversion. The generator of auxiliary is a separate obligation."""
    matrix, linear, body = ciphertext
    levels = q.bit_length() - 1
    mask = [-x for x in linear]
    for i in range(len(linear)):
        for j in range(len(linear)):
            for level in range(levels):
                if (matrix[i][j] >> level) & 1:
                    a, b = auxiliary[i, j, level]
                    mask = [x - y for x, y in zip(mask, a)]
                    body -= b
    return [x % q for x in mask], body % q


def auxiliary_conversion_attempt():
    q, n, levels = 4096, 3, 12
    rng = random.Random(751)
    checked, max_error = 0, 0
    for secret in itertools.product((0, 1), repeat=n):
        auxiliary, auxiliary_errors = {}, {}
        # This honest quadratic-hint generator uses the private key, as a
        # candidate key generator may; its joint LWE security is unproved.
        for i, j, level in itertools.product(range(n), range(n), range(levels)):
            a = [rng.randrange(q) for _ in range(n)]
            e = rng.choice((-1, 0, 1))
            b = (sum(x * y for x, y in zip(secret, a)) + (1 << level) * secret[i] * secret[j] + e) % q
            auxiliary[i, j, level] = a, b
            auxiliary_errors[i, j, level] = e
        for sample in range(100):
            matrix = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
            a = [rng.randrange(q) for _ in range(n)]
            error = [rng.choice((-1, 0, 1)) for _ in range(n)]
            fresh_error = rng.choice((-1, 0, 1))
            message = sample % 2 * (q // 2)
            linear = [(sum(secret[i] * matrix[i][j] for i in range(n)) - a[j] + error[j]) % q
                      for j in range(n)]
            body = (sum(x * y for x, y in zip(secret, a)) + message + fresh_error) % q
            out_mask, out_body = convert_with_auxiliary((matrix, linear, body), auxiliary, q)
            source_noise = fresh_error + sum(x * y for x, y in zip(secret, error))
            aux_noise = sum(auxiliary_errors[i, j, level]
                            for i, j, level in itertools.product(range(n), range(n), range(levels))
                            if (matrix[i][j] >> level) & 1)
            actual = (out_body - sum(x * y for x, y in zip(secret, out_mask)) - message) % q
            assert actual == (source_noise - aux_noise) % q
            assert abs(centered(actual, q)) <= n + 1 + n * n * levels
            max_error = max(max_error, abs(centered(actual, q)))
            checked += 1
    return {"q": q, "n": n, "ciphertexts_checked": checked, "max_actual_noise": max_error,
            "worst_case_noise_bound": n + 1 + n * n * levels,
            "same_underlying_key": True, "auxiliary_columns": n * n * levels,
            "scope": "Conversion correctness only; joint ordinary-LWE security of the native quadratic auxiliary law is unproved"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    results = {"scope": "Construction and operation diagnostics only", "builder": "LLL/Babai dense pool; public-body or l1 selection",
               "direct_game": direct_game_attempt(), "correlated_errors": correlated_error_attempt(),
               "shifted_source": shifted_source_attempt(), "auxiliary_conversion": auxiliary_conversion_attempt(),
               "compiler_cases": []}
    for seed, (n, m, q, radius) in enumerate([(4, 8, 256, 1), (4, 8, 65536, 1),
                                             (4, 16, 65536, 1), (4, 8, 65536, 64),
                                             (8, 8, 65536, 1), (8, 16, 65536, 1),
                                             (4, 16, 65536, 1), (4, 16, 65536, 1)], start=741):
        record = experiment(n, m, q, radius, seed)
        results["compiler_cases"].append(record)
        print({"case": [n, m, q, radius], "failure": record.get("failure"),
               "modes": [{"mode": r["mode"], "noise": r["max_control_noise"],
                          "refresh_selected_bit_correct": sum(x["correct"] for x in r["refresh_trials"])}
                         for r in record.get("modes", [])]}, flush=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
