#!/usr/bin/env python3
"""Try public simultaneous self-stability and pairwise gadget commutation.

All constraints use the stored control matrices, including bodies. Pairwise
commutation on G does not assert global operator commutation or small errors.
Builder failures are retained; no source/key/control draw is resampled.
"""
import argparse
import importlib.util
import json
from pathlib import Path

import numpy as np

spec = importlib.util.spec_from_file_location(
    "joint_projection_body", Path(__file__).with_name("try-gsw-body-adaptive-projection.py"))
body = importlib.util.module_from_spec(spec)
spec.loader.exec_module(body)
t = body.t


def joint_factors(g, controls, q):
    n, rows, width = len(controls), *g.shape
    constraints, targets = [], []
    for i, control in enumerate(controls):
        for source in (g, control):
            equation = np.zeros((rows, n * width), dtype=np.int64)
            equation[:, i * width:(i + 1) * width] = source
            constraints.append(equation)
            targets.append(control)
    for i in range(n):
        for j in range(i + 1, n):
            equation = np.zeros((rows, n * width), dtype=np.int64)
            equation[:, j * width:(j + 1) * width] = controls[i]
            equation[:, i * width:(i + 1) * width] = -controls[j]
            constraints.append(equation)
            targets.append(np.zeros_like(g))
    system, target = np.vstack(constraints), np.vstack(targets)
    solution = body.public_short_preimages(system, target, q)
    factors = [solution[i * width:(i + 1) * width] for i in range(n)]
    for i in range(n):
        assert np.array_equal(g @ factors[i] % q, controls[i])
        assert np.array_equal(controls[i] @ factors[i] % q, controls[i])
        for j in range(n):
            assert np.array_equal(controls[i] @ factors[j] % q, controls[j] @ factors[i] % q)
    return factors, {"constraint_rows": int(system.shape[0]), "lattice_dimension": int(system.shape[1]),
                     "preimage_columns": width, "certified_scalar_equations": int(target.size),
                     "max_digit": int(np.max(np.abs(solution))),
                     "max_column_l1_per_factor": [int(np.max(np.sum(np.abs(p), axis=0))) for p in factors]}


def experiment(n, levels, seed, variant):
    q, radius = 1 << levels, 1
    lookup = 1 << (4 * (n + 1)).bit_length()
    secret, controls, initial = body.draw(n, levels, radius, seed, variant)
    g = t.gadget(n, levels)
    result = {"n": n, "levels": levels, "fresh_error_bound": radius, "seed": seed,
              "variant": variant, "source_resampled": False, "secret_for_diagnostic": secret.tolist()}
    try:
        factors, builder = joint_factors(g, controls, q)
    except ValueError as error:
        result["builder_failure"] = str(error)
        print(json.dumps(result), flush=True)
        return result
    result["builder"] = builder
    result["single_control_scalar_checks"] = sum(body.single_control_check(g, c, p, q) for c, p in zip(controls, factors))
    phase_g = t.phase(g, secret, q)
    errors = [(t.phase(c, secret, q) - int(bit) * phase_g) % q for c, bit in zip(controls, secret)]
    cross = []
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            product = controls[i] @ factors[j] % q
            error = (t.phase(product, secret, q) - int(secret[i] * secret[j]) * phase_g) % q
            assert np.array_equal(error, (errors[i] @ factors[j] + int(secret[i]) * errors[j]) % q)
            assert np.array_equal(error, (errors[j] @ factors[i] + int(secret[j]) * errors[i]) % q)
            phase = int(t.phase(product, secret, q)[levels - 1])
            decoded = int(abs(t.centered(phase - q // 2, q)) < abs(t.centered(phase, q)))
            cross.append({"i": i, "j": j, "selected_correct": decoded == int(secret[i] * secret[j]),
                          "max_column_error": max(abs(t.centered(int(x), q)) for x in error)})
    result["cross_products"] = cross
    current, trials = [c.copy() for c in initial], []
    for cycle in range(3):
        output = []
        for branch in (0, 1):
            before = current[branch] if cycle == 0 else (
                g - current[branch] @ body.redundant.signed_quarter_digits(initial[0], levels)) % q
            expected = branch if cycle == 0 else 1
            after = body.refresh(before, controls, factors, levels, q, lookup, "right_joint_stable")
            phase = int(t.phase(after, secret, q)[levels - 1])
            decoded = int(abs(t.centered(phase - q // 2, q)) < abs(t.centered(phase, q)))
            bound = max(map(abs, t.noise(after, expected, secret, g, q)))
            trials.append({"cycle": cycle, "branch": branch, "correct": decoded == expected,
                           "output_noise": bound, "output_decoding_margin": 4 * bound < q,
                           "next_nand_rounding_margin": 2 * ((g.shape[1] + 1) * bound +
                                (n + 1) * (q // lookup - 1)) < q // 2})
            output.append(after)
        current = output
    result["refresh_trials"] = trials
    print(json.dumps({"n": n, "levels": levels, "seed": seed, "variant": variant,
                      "max_digit": builder["max_digit"], "correct": sum(t["correct"] for t in trials)}), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    cases = [experiment(n, levels, seed, variant) for n, levels, seed in
             ((2, 8, 15000), (2, 16, 15010), (3, 8, 15020), (3, 16, 15030))
             for variant in ("exact_diagonal", "full_signed_outer_product")]
    completed = [c for c in cases if "builder" in c]
    trials = [t for c in completed for t in c["refresh_trials"]]
    cross = [p for c in completed for p in c["cross_products"]]
    result = {"scope": "Joint public body-adaptive factors; pairwise gadget commutation and full small refresh cycles",
              "limitations": "No global commuting-operator claim, secure parameters, negligible builder failure, or closed mixed-error invariant",
              "cases": cases, "totals": {"cases": len(cases), "builder_failures": len(cases) - len(completed),
                  "preimage_columns": sum(c["builder"]["preimage_columns"] for c in completed),
                  "certified_scalar_equations": sum(c["builder"]["certified_scalar_equations"] for c in completed),
                  "single_control_scalar_checks": sum(c["single_control_scalar_checks"] for c in completed),
                  "cross_products": len(cross), "cross_selected_correct": sum(p["selected_correct"] for p in cross),
                  "refresh_calls": len(trials), "selected_correct": sum(t["correct"] for t in trials),
                  "output_margins": sum(t["output_decoding_margin"] for t in trials),
                  "next_nand_margins": sum(t["next_nand_rounding_margin"] for t in trials),
                  "all_six_selected_correct_cases": sum(all(t["correct"] for t in c["refresh_trials"]) for c in completed)}}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["totals"], sort_keys=True))


if __name__ == "__main__":
    main()
