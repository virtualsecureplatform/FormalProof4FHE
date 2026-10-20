#!/usr/bin/env python3
"""Private gadget-trapdoor correctness trials, with no security claim.

Uses MP12 Algorithm 1's statistical trapdoor distribution (0 with probability
1/2, +/-1 each with probability 1/4). The matrix marginal estimate does not
bound the complete public view. B, its signed gadget decomposition, and the
trapdoor stay private. Kernel randomization here is bounded ternary noise,
not MP12's basis-independent Gaussian preimage sampler.
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


def trial(n, levels, radius, seed):
    rng = random.Random(seed)
    q, m0 = 1 << levels, n * levels + 80
    width = (n + 1) * levels
    g = transcript.gadget(n, levels)
    small_g = g[1:, levels:]
    a0 = np.array([[rng.randrange(q) for _ in range(m0)] for _ in range(n)], dtype=np.int64)
    r = np.array([[rng.choice((0, 0, -1, 1)) for _ in range(n * levels)]
                  for _ in range(m0)], dtype=np.int64)
    t = np.vstack((r, np.eye(n * levels, dtype=np.int64)))
    a = np.hstack((a0, (small_g - a0 @ r) % q))
    assert np.array_equal(a @ t % q, small_g)
    m = a.shape[1]
    secret = np.array([rng.randrange(2) for _ in range(n)], dtype=np.int64)
    errors = np.array([rng.randint(-radius, radius) for _ in range(m)], dtype=np.int64)
    y = (secret @ a + errors) % q
    raw_masks = np.array([[[rng.randrange(q) for _ in range(width)] for _ in range(n)]
                          for _ in range(n)], dtype=np.int64)
    fresh_errors = np.array([[rng.randint(-radius, radius) for _ in range(width)]
                             for _ in range(n)], dtype=np.int64)
    public_key = np.vstack((y, a))
    initial = [(public_key @ np.array([[rng.randrange(2) for _ in range(width)]
                                      for _ in range(m)], dtype=np.int64) + bit * g) % q
               for bit in (0, 1)]
    # A small PUBLIC gadget kernel, lifted using PRIVATE T.
    kernel = np.zeros((n * levels, n * (levels - 1)), dtype=np.int64)
    for row in range(n):
        for level in range(levels - 1):
            col = row * (levels - 1) + level
            kernel[row * levels + level, col] = 2
            kernel[row * levels + level + 1, col] = -1
    assert not np.any(small_g @ kernel)
    lifted_kernel = t @ kernel
    assert not np.any(a @ lifted_kernel % q)
    # The same alternating freedom is used in both modes.
    witnesses = {}
    for i in range(n):
        for j in range(n):
            if i != j:
                for level in range(levels):
                    witnesses[i, j, level] = np.array(
                        [[rng.choice((-1, 0, 1)) for _ in range(n)] for _ in range(n)],
                        dtype=np.int64)
    modes = []
    for randomized in (False, True):
        controls, checks, max_l1, max_residual = [], 0, 0, 0
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
                        unit_target = np.zeros((n, n), dtype=np.int64)
                        unit_target[i, j] = -1
                        u = witnesses[i, j, level]
                        coefficient = unit_target + u - u.T
                        decomposition = np.zeros((n, n * levels), dtype=np.int64)
                        decomposition[:, level::levels] = coefficient
                        b = decomposition @ t.T
                        if randomized:
                            z = np.array([[rng.choice((-1, 0, 1)) for _ in range(kernel.shape[1])]
                                          for _ in range(n)], dtype=np.int64)
                            b += z @ lifted_kernel.T
                        assert np.array_equal(b @ a.T % q, coefficient * weight % q)
                        assert int(secret @ b @ a.T @ secret) % q == -weight * secret[i] * secret[j] % q
                        correction[:, column] = b @ y % q
                        residual[column] = int(secret @ b @ errors) % q
                        max_l1 = max(max_l1, int(np.abs(b).sum()))
                        max_residual = max(max_residual, abs(transcript.centered(int(residual[column]), q)))
                        checks += 1
            masks = (raw_masks[i] - correction) % q
            bodies = (secret @ raw_masks[i] + fresh_errors[i]) % q
            control = np.vstack((bodies, masks))
            assert transcript.noise(control, secret[i], secret, g, q) == [
                transcript.centered(int(x), q) for x in (fresh_errors[i] + residual) % q]
            controls.append(control)
        control_bound = max(abs(x) for i, c in enumerate(controls)
                            for x in transcript.noise(c, secret[i], secret, g, q))
        # Triangle bound: every selected T column has l1 <= m0+1;
        # |Q+U-U^T| <= 3 per entry. Each lifted kernel column is
        # 2*T_col - T_next, with l1 <= 3*(m0+1).
        structural_l1_bound = 3 * n * n * (m0 + 1) * (levels if randomized else 1)
        assert max_l1 <= structural_l1_bound
        lookup = 1 << (4 * (n + 1)).bit_length()
        current = [c.copy() for c in initial]
        records = []
        for cycle in range(3):
            next_ciphertexts = []
            for bit in (0, 1):
                if cycle:
                    before = (g - current[bit] @ transcript.digits(initial[0], levels)) % q
                    message = 1
                else:
                    before, message = current[bit], bit
                after = transcript.refresh(before, controls, levels, q, lookup)
                input_bound = max(map(abs, transcript.noise(before, message, secret, g, q)))
                output_bound = max(map(abs, transcript.noise(after, message, secret, g, q)))
                phase = int(transcript.phase(after, secret, q)[levels - 1])
                decoded = int(abs(transcript.centered(phase - q // 2, q)) <
                              abs(transcript.centered(phase, q)))
                records.append({"cycle": cycle, "input_branch": bit, "expected": message,
                                "decoded": decoded, "correct": decoded == message,
                                "input_noise": input_bound, "output_noise": output_bound,
                                "input_rounding_margin": 2 * (input_bound + (n + 1) * (q // lookup - 1)) < q // 2,
                                "output_decoding_margin": 4 * output_bound < q,
                                "next_nand_rounding_margin": 2 * ((width + 1) * output_bound +
                                    (n + 1) * (q // lookup - 1)) < q // 2})
                next_ciphertexts.append(after)
            current = next_ciphertexts
        # Diagnostic for the DISCLOSED-trapdoor variant only. The real public
        # view in this trial does not contain T, B, or their decompositions.
        top = t[:, levels - 1::levels]
        projection = top.T @ y % q
        recovered = np.array([int(abs(transcript.centered(int(x) - q // 2, q)) <
                                  abs(transcript.centered(int(x), q))) for x in projection])
        modes.append({"kernel_randomization": randomized, "certificates_checked": checks,
                      "full_control_phase_checks": n * width,
                      "max_preimage_total_l1": max_l1, "structural_l1_bound": structural_l1_bound,
                      "max_shared_residual": max_residual,
                      "max_control_noise": control_bound, "refresh_trials": records,
                      "disclosed_trapdoor_only": {
                          "key_recovered": bool(np.array_equal(recovered, secret)),
                          "all_coordinate_worst_case_margins": bool(
                              np.all(4 * radius * np.abs(top).sum(axis=0) < q))}})
    return {"n": n, "levels": levels, "q": q, "source_width": m, "radius": radius,
            "seed": seed, "diagnostic_secret_hamming_weight": int(secret.sum()),
            "source_resampled": False,
            "matrix_marginal_MP12_statistical_distance_upper_bound": n * levels / 2 * 2 ** -40,
            "modes": modes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    results = {"scope": "Finite private-trapdoor correctness diagnostics; full joint security unproved",
               "public_view": "A,y,native masked controls; excludes trapdoor, preimages and decompositions",
               "ordinary_LWE_reduction_gap": "No public simulator for the hidden preimage corrections at the unknown-secret challenge matrix",
               "cases": []}
    for n, levels, radius, seed in [(2, 20, 1, 811), (3, 24, 1, 812),
                                   (3, 24, 8, 813), (4, 24, 8, 814)]:
        result = trial(n, levels, radius, seed)
        results["cases"].append(result)
        print({"case": [n, levels, radius, seed], "key_weight": result["diagnostic_secret_hamming_weight"],
               "modes": [{"randomized": m["kernel_randomization"], "control_noise": m["max_control_noise"],
                          "correct": sum(r["correct"] for r in m["refresh_trials"]),
                          "reusable_margin": sum(r["next_nand_rounding_margin"] for r in m["refresh_trials"])}
                         for m in result["modes"]]}, flush=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
