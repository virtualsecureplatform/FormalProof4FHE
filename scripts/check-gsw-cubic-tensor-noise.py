#!/usr/bin/env python3
"""Audit a probabilistic error bound for the public three-block compiler.

For mask-dependent D and independent centered errors in [-E,E], three
conditional Hoeffding steps give |D[e1,e2,e3]| <= (2t)^(3/2) E^3 ||D||_F
except with probability <= 2(m^2+m+1) exp(-t). Union over K controls
requires no independence between their errors. This script checks exact
finite budget substitutions, not the missing coefficient-family theorem.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path


def ceil_sqrt(value):
    root = math.isqrt(value)
    return root+int(root*root != value)


def error_bound(m, count, security_bits, radius, frobenius_squared):
    union_factor = 2*count*(m*m+m+1)
    t = security_bits+(union_factor-1).bit_length()
    failure_bound = Fraction(union_factor, 1 << t)
    assert failure_bound <= Fraction(1, 1 << security_bits)
    return (ceil_sqrt((2*t)**3*radius**6*frobenius_squared), t, failure_bound)


def budget(n, bits, radius, bound):
    rows = n*n+n+1
    growth = rows*bits
    lookup = 1 << (8*rows-1).bit_length()
    return lookup**2*rows*growth*(growth+1)**2*max(bound, (n+1)*radius)


def exact_tail_fixtures():
    """Exact integer tails, using binomial multiplicities instead of sampling."""
    records = []
    nonvacuous_positive_tails = 0
    for m in (2, 8, 16, 32, 64):
        sums = [(2*i-m, math.comb(m, i)) for i in range(m+1)]
        distribution = Counter()
        for (a, wa), (b, wb), (c, wc) in itertools.product(sums, repeat=3):
            distribution[abs(a*b*c)] += wa*wb*wc
        assert sum(distribution.values()) == 1 << (3*m)
        # All-one tensor: residual is the product of three Rademacher sums.
        for t in (1, 2, 4, 8, 16, 32):
            threshold = ceil_sqrt((2*t)**3*m**3)
            tail_count = sum(multiplicity for value, multiplicity in distribution.items()
                             if value > threshold)
            exact_tail = Fraction(tail_count, 1 << (3*m))
            upper = min(Fraction(1), Fraction(2*(m*m+m+1), 1 << t))
            assert exact_tail <= upper
            nonvacuous_positive_tails += int(0 < exact_tail and upper < 1)
            records.append(dict(m=m, t=t, threshold=str(threshold),
                                exact_integer_tail=str(exact_tail), upper_bound=str(upper)))
    assert nonvacuous_positive_tails > 0
    return dict(records=records, nonvacuous_positive_tails=nonvacuous_positive_tails,
                represented_error_tapes=str(sum(1 << (3*m) for m in (2, 8, 16, 32, 64))))


def audit(source):
    raw = source.read_bytes()
    data = json.loads(raw)
    assert data["version"] == 2 and not data["asymptotic_shortness_theorem"]
    records = []
    for case in data["cases"]:
        n, m, bits = case["n"], case["m"], case["bits"]
        # Conservative count of all scalar original-bit control columns,
        # matching RecursiveFeatureSecurityView.scalarColumns minus the PK.
        joint_count = n*(n*n+n+1)*bits
        for control in case.get("controls", []):
            l1, f2 = int(control["l1"]), int(control["frobenius_squared"])
            assert f2 == sum(x*x for x in control["coefficients"])
            assert l1 == sum(map(abs, control["coefficients"]))
            assert f2 <= l1*l1 <= m**3*f2
            for security_bits in (8, 32, 64, 128):
                for radius in (1, 3):
                    high_probability, t, failure = error_bound(m, joint_count, security_bits, radius, f2)
                    supported = radius**3*l1
                    if 2*t >= m:
                        assert high_probability >= supported
                    chosen = min(supported, high_probability)
                    new_budget = budget(n, bits, radius, chosen)
                    old_budget = int(control["bootstrap_budgets"][0 if radius == 1 else 1]["budget"])
                    assert old_budget == budget(n, bits, radius, supported)
                    linear = case["linear_source_filter"]
                    recovery = linear["status"] == "ok" and len(linear["vectors"]) == n and all(
                        4*radius*int(v["l1"]) < 1 << bits for v in linear["vectors"])
                    records.append(dict(n=n, m=m, bits=bits, indices=control["indices"],
                                        level=control["level"], radius=radius, security_bits=security_bits,
                                        joint_count=joint_count, t=t, joint_failure_bound=str(failure),
                                        supported_bound=str(supported), probabilistic_bound=str(high_probability),
                                        chosen_bound=str(chosen), improved=chosen < supported,
                                        dimension_forces_no_improvement=2*t >= m,
                                        previous_strict_budget=old_budget < 1 << bits,
                                        strict_budget=new_budget < 1 << bits,
                                        ordinary_input_recovery=recovery))
    return dict(version=1, scope="Noise-bound audit only; no asymptotic compiler or security theorem",
                input_path=str(source), input_sha256=hashlib.sha256(raw).hexdigest(),
                exact_tail_fixtures=exact_tail_fixtures(), records=records,
                summary=dict(control_certificates=data["summary"]["control_certificates"],
                             noise_budget_substitutions=len(records),
                             improved_bounds=sum(r["improved"] for r in records),
                             dimension_forces_no_improvement=sum(r["dimension_forces_no_improvement"] for r in records),
                             additional_budget_passes=sum(r["strict_budget"] and not r["previous_strict_budget"]
                                                          for r in records),
                             passing_budgets_without_source_recovery=sum(r["strict_budget"] and not
                                                                         r["ordinary_input_recovery"] for r in records)),
                new_Lean_theorem=False, coefficient_family_bound=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path("docs/GSWCubicTensorCompilerExploration.json"))
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    args = parser.parse_args()
    result = audit(args.source)
    if args.verify_existing:
        assert result == json.loads(args.verify_existing.read_text())
    else:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result["summary"]), flush=True)


if __name__ == "__main__":
    main()
