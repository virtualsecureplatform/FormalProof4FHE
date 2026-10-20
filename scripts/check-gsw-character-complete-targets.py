#!/usr/bin/env python3
"""Replay saved character coefficients in the complete original-control layout.

No search, lattice package, key resampling or hardness inference. Each cubic
slot uses a saved exact preimage or the zero correction, whichever has the
smaller public bound. All other targets use the verified quadratic correction.
The report is a supported coefficient certificate, not sampled key generation.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "docs/GSWLinearCharacterCompilerExploration.json"
SOURCE_HASH = "85d6412016a68b711e79662252d6273e98dc4d58693da1fb0902ff9d68184b45"


def report():
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_HASH
    saved = json.loads(SOURCE.read_text())
    cases = []
    for case in saved["cases"]:
        n, m, bits, radius = (case[key] for key in ("n", "m", "bits", "radius"))
        q = 1 << bits
        a = [sum((block[row] for block in case["blocks"]), []) for row in range(n)]
        width = len(a[0])
        assert width == 3 * m and all(len(row) == width for row in a)
        pairs = list(itertools.combinations(range(n), 2))
        triples = list(itertools.combinations(range(n), 3))
        preimages = {}
        for witness in case["attempt"].get("vectors", []):
            if "coefficients" not in witness:
                continue
            target, level, u = tuple(witness["indices"]), witness["level"], witness["coefficients"]
            assert target in triples and 2 <= level < bits
            assert len(u) == len(pairs) * width and all(2 * abs(x) <= q for x in u)
            assert (target, level) not in preimages
            # Coefficients of the ACTUAL sparse cubic polynomial, without
            # dividing a residue by four or using secret values as a verifier.
            for triple in triples:
                coefficient = 0
                for pair_index, pair in enumerate(pairs):
                    if set(pair) <= set(triple):
                        remaining = next(row for row in triple if row not in pair)
                        coefficient += sum(a[remaining][j] * u[pair_index * width + j]
                                           for j in range(width))
                assert (4 * coefficient) % q == ((1 << level) if triple == target else 0)
            preimages[target, level] = radius * sum(map(abs, u))

        features = [()] + [(i,) for i in range(n)] + list(itertools.product(range(n), repeat=2))
        rows = n * n + n + 1
        assert len(features) == rows
        bounds, noncubic, exact, omitted = [], 0, 0, 0
        for index in range(n):
            for feature in features:
                genuine = len(feature) == 2 and len({index, *feature}) == 3
                for level in range(bits):
                    if not genuine:
                        # All lower/repeated-index targets are exact quadratic
                        # messages. Character coefficients and discrepancy are zero.
                        bounds.append(0)
                        noncubic += 1
                        continue
                    triple = tuple(sorted((index, *feature)))
                    zero_bound = 1 << level  # One cubic monomial's centered coefficient.
                    projected_bound = preimages.get((triple, level), zero_bound)
                    if projected_bound < zero_bound:
                        bounds.append(projected_bound)
                        exact += 1
                    else:
                        bounds.append(zero_bound)
                        omitted += 1
        control_count = n * rows * bits
        assert len(bounds) == control_count
        assert exact + omitted == 6 * len(triples) * bits
        max_discrepancy_and_source_error = max(bounds, default=0)
        control_bound = (n + 1) * radius + max_discrepancy_and_source_error
        lookup = 1
        while lookup < 8 * rows:
            lookup *= 2
        growth = rows * bits
        factor = lookup * lookup * rows * growth * (growth + 1) * (growth + 1)
        assert lookup == case["budget"]["lookup"] and factor == int(case["budget"]["refresh_factor"])
        assert (q - 1) // (4 * factor) - (n + 1) * radius == int(case["budget"]["J_cap"])
        public_samples = growth + 2 * bits + 17
        fresh_bound = public_samples * (n + 1) * radius
        assert fresh_bound == int(case["budget"]["fresh_encryption_bound"])
        output_bound = lookup * rows * growth * (growth + 1) * control_bound
        assert q % lookup == 0
        down_factor = q // lookup
        round_margin = 2 * ((growth + 1) * output_bound + (rows + 1) * (down_factor - 1)) < q // 2
        decode_margin = 2 * output_bound < q // 2

        recovery = case["attempt"]["source_recovery"]
        recovered_indices = set()
        for witness in recovery["vectors"]:
            index, vector = witness["coordinate"], witness["coefficients"]
            assert len(vector) == width and 0 <= index < n and index not in recovered_indices
            assert all(sum(x * y for x, y in zip(row, vector)) % q == (q // 2 if r == index else 0)
                       for r, row in enumerate(a))
            assert sum(map(abs, vector)) == int(witness["l1"])
            if 4 * radius * sum(map(abs, vector)) < q:
                recovered_indices.add(index)
        source_recoverable = len(recovered_indices) == n
        assert source_recoverable == recovery["guaranteed_matching_radius_recovery"]
        passes = 4 * factor * control_bound < q and fresh_bound <= output_bound
        assert not passes or (round_margin and decode_margin)
        cases.append(dict(n=n, block_width=m, bits=bits, error_radius=radius,
                          verified_preimages=len(preimages), control_slots=control_count,
                          exact_quadratic_slots=noncubic, exact_cubic_slots=exact,
                          omitted_cubic_slots=omitted, compiler_bound=str(max_discrepancy_and_source_error),
                          control_bound=str(control_bound), compiler_cap=case["budget"]["J_cap"],
                          conservative_budget_passes=passes, lookup=lookup,
                          fresh_encryption_bound=str(fresh_bound), refresh_output_bound=str(output_bound),
                          actual_rounding_margin=round_margin, actual_decoding_margin=decode_margin,
                          public_table_columns=public_samples, retained_source_columns=width,
                          total_ordinary_source_columns=width + (public_samples + control_count) * (n + 1),
                          matching_radius_source_recovery=source_recoverable))
    return dict(version=1, input_sha256=SOURCE_HASH,
                scope="Complete target/coefficient replay; no joint sampler experiment or hardness claim.",
                cases=cases,
                summary=dict(verified_preimages=sum(c["verified_preimages"] for c in cases),
                             control_slots=sum(c["control_slots"] for c in cases),
                             budget_passes=sum(c["conservative_budget_passes"] for c in cases),
                             passes_without_source_recovery=sum(c["conservative_budget_passes"] and
                                                               not c["matching_radius_source_recovery"] for c in cases)))


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
    print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
