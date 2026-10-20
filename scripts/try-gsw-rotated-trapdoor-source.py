#!/usr/bin/env python3
"""An ordinary-source simulation attempt; tests correctness, not security.

All source masks/errors are sampled once. A fixed pool supplies the first
invertible rotation; no source or error failure is resampled. The correction
algorithm receives only source transcripts and independently sampled R.
"""

import argparse
import importlib.util
import json
from pathlib import Path
import random

import numpy as np

spec = importlib.util.spec_from_file_location(
    "transcript", Path(__file__).with_name("try-gsw-transcript-routes.py"))
transcript = importlib.util.module_from_spec(spec)
spec.loader.exec_module(transcript)
centered = transcript.centered


def inverse_mod(matrix, q):
    n = len(matrix)
    rows = [[int(x) % q for x in row] + [int(i == j) for j in range(n)]
            for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next((i for i in range(column, n) if rows[i][column] % 2), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        reciprocal = pow(rows[column][column], -1, q)
        rows[column] = [value * reciprocal % q for value in rows[column]]
        for i in range(n):
            if i != column:
                scale = rows[i][column]
                rows[i] = [(x - scale * y) % q for x, y in zip(rows[i], rows[column])]
    inverse = np.array([row[n:] for row in rows], dtype=np.int64)
    assert np.array_equal(np.array(matrix, dtype=np.int64) @ inverse % q, np.eye(n, dtype=np.int64))
    return inverse


def experiment(n, levels, radius, seed, key_mode):
    rng, q = random.Random(seed), 1 << levels
    m0, pool_size = (n + 1) * levels + 80, 64
    a0 = np.array([[rng.randrange(q) for _ in range(m0)] for _ in range(n)], dtype=np.int64)
    rotations = [np.array([[rng.randrange(q) for _ in range(n)] for _ in range(n)], dtype=np.int64)
                 for _ in range(pool_size)]
    inverses = [inverse_mod(h, q) for h in rotations]
    selected = next((i for i, inv in enumerate(inverses) if inv is not None), None)
    # Fixed nonzero diagnostic keys; these are not a cryptographic key sampler.
    secret = np.ones(n, dtype=np.int64) if key_mode == "all_ones" else np.array([1] + [0] * (n - 1))
    all_masks = np.hstack([a0, *rotations])
    errors = np.array([rng.randint(-radius, radius) for _ in range(all_masks.shape[1])], dtype=np.int64)
    all_bodies = (secret @ all_masks + errors) % q
    result = {"n": n, "levels": levels, "q": q, "source_radius": radius,
              "seed": seed, "key_mode": key_mode, "fixed_diagnostic_key": True,
              "source_resampled": False, "rotation_pool": pool_size,
              "selected_rotation": selected, "public_source_width": all_masks.shape[1],
              "certificates_checked": 0, "phase_checks": 0, "half_turn_witnesses": [],
              "refresh_trials": []}
    if selected is None:
        result["failure"] = "No invertible rotation in the fixed pool"
        return result
    h, inverse = rotations[selected], inverses[selected]
    begin = m0 + selected * n
    y0, y_h = all_bodies[:m0], all_bodies[begin:begin + n]
    e0, e_h = errors[:m0], errors[begin:begin + n]
    r = np.array([[rng.randrange(2) for _ in range(n * levels)] for _ in range(m0)], dtype=np.int64)
    t = np.vstack((r, np.eye(n * levels, dtype=np.int64)))
    gadget = transcript.gadget(n, levels)
    small_g = gadget[1:, levels:]
    derived_a = np.hstack((a0, (h @ small_g - a0 @ r) % q))
    derived_y = np.concatenate((y0, (y_h @ small_g - y0 @ r) % q))
    derived_error = np.concatenate((e0, e_h @ small_g - e0 @ r))
    assert np.array_equal(derived_a @ t % q, h @ small_g % q)
    assert np.array_equal((derived_y - secret @ derived_a) % q, derived_error % q)
    assert np.array_equal(t.T @ derived_y % q, small_g.T @ y_h % q)
    eta, proxy = inverse.T @ e_h % q, inverse.T @ y_h % q
    assert np.array_equal(proxy, (secret + eta) % q)
    width = gadget.shape[1]
    raw_masks = np.array([[[rng.randrange(q) for _ in range(width)] for _ in range(n)]
                          for _ in range(n)], dtype=np.int64)
    fresh_errors = np.array([[rng.randint(-radius, radius) for _ in range(width)]
                             for _ in range(n)], dtype=np.int64)
    controls, max_norm = [], 0
    for i in range(n):
        correction = np.zeros((n, width), dtype=np.int64)
        residual = np.zeros(width, dtype=np.int64)
        for row in range(n + 1):
            for level in range(levels):
                column, weight = row * levels + level, 1 << level
                if row == 0:
                    correction[i, column] = weight
                elif row - 1 == i:
                    correction[i, column] = -weight
                else:
                    j = row - 1
                    target = np.zeros((n, n), dtype=np.int64)
                    target[i, j] = -weight
                    effective = target @ inverse.T % q
                    decomposition = np.hstack([((effective >> ell) & 1)[:, j:j + 1]
                                               for j in range(n) for ell in range(levels)])
                    assert np.array_equal(decomposition @ small_g.T % q, effective)
                    b = decomposition @ t.T
                    assert np.array_equal(b @ derived_a.T % q, target % q)
                    correction[:, column] = b @ derived_y % q
                    assert np.array_equal(correction[:, column], target @ proxy % q)
                    residual[column] = int(secret @ b @ derived_error) % q
                    assert residual[column] == int(secret @ (target @ eta % q)) % q
                    norm = int(np.abs(b).sum())
                    assert norm <= n * levels * (m0 + 1)
                    max_norm = max(max_norm, norm)
                    result["certificates_checked"] += 1
                    if eta[j] and (weight * int(eta[j])) % q == q // 2:
                        result["half_turn_witnesses"].append({"control": i, "coordinate": j,
                                                             "level": level,
                                                             "active_secret_bit": bool(secret[i])})
        control = np.vstack(((secret @ raw_masks[i] + fresh_errors[i]) % q,
                             (raw_masks[i] - correction) % q))
        assert transcript.noise(control, secret[i], secret, gadget, q) == [
            centered(int(value), q) for value in (fresh_errors[i] + residual) % q]
        result["phase_checks"] += width
        controls.append(control)
    for i in range(n):
        for j in range(n):
            if i != j and eta[j]:
                assert any(w["control"] == i and w["coordinate"] == j
                           for w in result["half_turn_witnesses"])
    result.update(max_private_preimage_l1=max_norm,
                  structural_l1_bound=n * levels * (m0 + 1),
                  selected_rotation_error=[int(x) for x in e_h],
                  inverse_error=[centered(int(x), q) for x in eta],
                  max_derived_source_error=int(np.abs(derived_error).max()),
                  max_control_noise=max(abs(x) for i, c in enumerate(controls)
                                        for x in transcript.noise(c, secret[i], secret, gadget, q)))
    active = sum(w["active_secret_bit"] for w in result["half_turn_witnesses"])
    result["active_half_turns"] = active
    result["control_obstruction_lower_bound"] = max(0, q // 2 - radius) if active else 0
    assert result["max_control_noise"] >= result["control_obstruction_lower_bound"]
    public_key = np.vstack((all_bodies, all_masks))
    initial = [(public_key @ np.array([[rng.randrange(2) for _ in range(width)]
                                      for _ in range(all_masks.shape[1])], dtype=np.int64) + bit * gadget) % q
               for bit in (0, 1)]
    lookup = 1 << (4 * (n + 1)).bit_length()
    current = [c.copy() for c in initial]
    for cycle in range(3):
        output = []
        for branch in (0, 1):
            before = current[branch] if cycle == 0 else (
                gadget - current[branch] @ transcript.digits(initial[0], levels)) % q
            expected = branch if cycle == 0 else 1
            after = transcript.refresh(before, controls, levels, q, lookup)
            input_bound = max(map(abs, transcript.noise(before, expected, secret, gadget, q)))
            output_bound = max(map(abs, transcript.noise(after, expected, secret, gadget, q)))
            selected_phase = int(transcript.phase(after, secret, q)[levels - 1])
            decoded = int(abs(centered(selected_phase - q // 2, q)) < abs(centered(selected_phase, q)))
            result["refresh_trials"].append({"cycle": cycle, "branch": branch,
                "expected": expected, "decoded": decoded, "correct": decoded == expected,
                "input_noise": input_bound, "output_noise": output_bound,
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
    params = [(2, 16, 0), (2, 16, 1), (2, 16, 64), (3, 24, 0),
              (3, 24, 1), (3, 24, 64), (4, 24, 1), (4, 24, 64)]
    cases = [experiment(*p, 12001 + i, mode) for i, p in enumerate(params)
             for mode in ("all_ones", "single_one")]
    trials = [trial for case in cases for trial in case["refresh_trials"]]
    result = {"scope": "Rotated ordinary-source simulation/correctness trial; no secure correct FHE claim",
              "zero_error_boundary": "Zero rotation noise restores native controls but does not meet the required LWE source-hardness premise",
              "cases": cases, "totals": {"attempts": len(cases),
                "certificates": sum(c["certificates_checked"] for c in cases),
                "phase_checks": sum(c["phase_checks"] for c in cases),
                "refresh_calls": len(trials),
                "selected_correct": sum(t["correct"] for t in trials),
                "output_margins": sum(t["output_decoding_margin"] for t in trials),
                "next_nand_margins": sum(t["next_nand_rounding_margin"] for t in trials)}}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["totals"], sort_keys=True))


if __name__ == "__main__":
    main()
