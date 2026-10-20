#!/usr/bin/env python3
"""Exact all-target basis bounds for the approximate cubic compiler.

This extracts bases only from small lattice calls already known to finish.
It checks finite certificates, not random-mask profile concentration.
Generation uses fpylll; replay and exact nearest-plane use standard Python.
"""
import argparse
from fractions import Fraction as F
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import time


ROOT = Path(__file__).resolve().parent.parent
COMPILER = ROOT / "scripts/search-gsw-approximate-tensor-compiler.py"
SOURCE = ROOT / "docs/GSWApproximateTensorCompilerExploration.json"
spec = importlib.util.spec_from_file_location("approximate_compiler", COMPILER)
approx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(approx)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def encode(value):
    value = F(value)
    return dict(numerator_hex=hex(value.numerator), denominator_hex=hex(value.denominator))


def decode(value):
    return F(int(value["numerator_hex"], 16), int(value["denominator_hex"], 16))


def ceil_fraction(value):
    return -(-value.numerator//value.denominator)


def ceil_sqrt(value):
    root = math.isqrt(value.numerator//value.denominator)
    return root+int(root*root*value.denominator < value.numerator)


def gram_schmidt(basis):
    orthogonal, norms = [], []
    for row in basis:
        current = list(map(F, row))
        for earlier, norm in zip(orthogonal, norms):
            multiple = sum(a*b for a, b in zip(current, earlier))/norm
            current = [a-multiple*b for a, b in zip(current, earlier)]
        norm = sum(x*x for x in current)
        assert norm > 0
        orthogonal.append(current)
        norms.append(norm)
    return orthogonal, norms


def independent_ldl(basis):
    """Reconstruct GSO via a rational LDL factorization of the integer Gram matrix."""
    size = len(basis)
    gram = [[sum(a*b for a, b in zip(row, other)) for other in basis] for row in basis]
    mu = [[F(int(i == j)) for j in range(size)] for i in range(size)]
    norms = []
    for i in range(size):
        norm = F(gram[i][i])-sum(mu[i][k]**2*norms[k] for k in range(i))
        assert norm > 0
        norms.append(norm)
        for j in range(i+1, size):
            mu[j][i] = (F(gram[j][i])-sum(mu[j][k]*mu[i][k]*norms[k] for k in range(i)))/norm
    orthogonal = []
    for i, row in enumerate(basis):
        orthogonal.append([F(row[j])-sum(mu[i][k]*orthogonal[k][j] for k in range(i))
                           for j in range(size)])
    assert all(sum(x*x for x in row) == norm for row, norm in zip(orthogonal, norms))
    assert all(sum(a*b for a, b in zip(orthogonal[i], orthogonal[j])) == 0
               for i in range(size) for j in range(i))
    return orthogonal, norms


def profile(basis, orthogonal, norms, alpha, q, width, height):
    dimension = len(basis)
    determinant_squared = alpha**(2*width)*q**(2*height)
    assert math.prod(norms) == determinant_squared
    norm_sum = sum(norms)
    l1_sum = sum(abs(x) for row in orthogonal for x in row)
    h_l1 = ceil_fraction(l1_sum/16+F(9*height, 2))
    h_l2 = ceil_fraction(F(ceil_sqrt(dimension*norm_sum), 16)+F(9*height, 2))
    ratio = norm_sum**dimension/(dimension**dimension*determinant_squared)
    assert ratio >= 1
    low, high = 0, 1
    while high**dimension*ratio.denominator < ratio.numerator:
        high *= 2
    while high-low > 1:
        middle = (high+low)//2
        if middle**dimension*ratio.denominator >= ratio.numerator:
            high = middle
        else:
            low = middle
    assert high**dimension*ratio.denominator >= ratio.numerator
    assert (high-1)**dimension*ratio.denominator < ratio.numerator
    return dict(gso_norms=[encode(x) for x in norms], norm_sum=encode(norm_sum),
                orthogonal_l1_sum=encode(l1_sum), H_l1=str(h_l1), H_l2=str(h_l2),
                H=str(min(h_l1, h_l2)), mean_flatness_integer=str(high),
                determinant_squared_bits=determinant_squared.bit_length())


def exact_nearest_plane(basis, orthogonal, norms, target):
    residual = list(target)
    combination = [0]*len(basis)
    for i in reversed(range(len(basis))):
        quotient = sum(a*b for a, b in zip(residual, orthogonal[i]))/norms[i]
        rounded = (2*quotient.numerator+quotient.denominator)//(2*quotient.denominator)
        combination[i] = rounded
        residual = [a-rounded*b for a, b in zip(residual, basis[i])]
    # Later updates in the reverse loop are orthogonal to already fixed rows.
    projections = [sum(a*b for a, b in zip(residual, row))/norm for row, norm in zip(orthogonal, norms)]
    assert all(-F(1, 2) <= x <= F(1, 2) for x in projections)
    assert sum(x*x for x in residual) == sum(x*x*norm for x, norm in zip(projections, norms))
    assert 4*sum(x*x for x in residual) <= sum(norms)
    return combination, [a-b for a, b in zip(target, residual)]


def membership(basis, matrix, alpha, q, width):
    assert len(basis) == width+len(matrix)
    assert all(len(row) == len(basis) for row in basis)
    for row in basis:
        assert all(x % alpha == 0 for x in row[:width])
        vector = [x//alpha for x in row[:width]]
        assert all((sum(a*b for a, b in zip(crow, vector))-row[width+i]) % q == 0
                   for i, crow in enumerate(matrix))


def bound_checks():
    rounding = 0
    for r in range(-65536, 65537):
        d = (r+4)//8
        epsilon = r-8*d
        assert -4 <= epsilon <= 3
        assert 8*(abs(d)+abs(epsilon)) <= abs(r)+36
        rounding += 1
    basis = [[3, 1], [1, 4]]
    orthogonal, norms = gram_schmidt(basis)
    assert (orthogonal, norms) == independent_ldl(basis)
    targets = 0
    for target in itertools.product(range(-8, 9), repeat=2):
        combination, near = exact_nearest_plane(basis, orthogonal, norms, target)
        assert near == [sum(c*row[j] for c, row in zip(combination, basis)) for j in range(2)]
        targets += 1
    for n in range(3, 4097):
        m = (3*n+3)//4
        assert m**3 >= 2*math.comb(n, 3)
    return dict(rounding_bound_checks=rounding, exact_plane_toy_targets=targets,
                dimension_checks=4094)


def generate(source):
    from fpylll import IntegerMatrix, LLL
    records = []
    for case in source["cases"]:
        if case["n"] not in (3, 4):
            continue
        n, m, bits = case["n"], case["m"], case["bits"]
        q = 1 << bits
        triples, matrix = approx.cubic_matrix(case["blocks"], q)
        width, height = m**3, len(triples)
        for run in case["radii"]:
            old = next(a for a in run["attempts"] if a["scale"] == 8)
            assert old["status"] == "complete"
            radius = run["radius"]
            alpha = 8*radius**3
            raw = [[alpha*int(i == j) for j in range(width)]+[matrix[k][i] for k in range(height)]
                   for i in range(width)]
            raw += [[0]*width+[q*int(i == j) for j in range(height)] for i in range(height)]
            lattice = IntegerMatrix.from_matrix(raw)
            LLL.reduction(lattice, delta=0.75)
            basis = [[int(lattice[i, j]) for j in range(width+height)] for i in range(width+height)]
            membership(basis, matrix, alpha, q, width)
            orthogonal, norms = gram_schmidt(basis)
            cert = profile(basis, orthogonal, norms, alpha, q, width, height)
            bound = int(cert["H"])
            witnesses = []
            float_matches = 0
            worst = 0
            entries = {(tuple(e["indices"]), e["level"]): e for e in run["entries"]}
            for indices in triples:
                for level in range(bits):
                    target = [0]*width+[(1 << level)*int(t == indices) for t in triples]
                    combination, near = exact_nearest_plane(basis, orthogonal, norms, target)
                    assert all(x % alpha == 0 for x in near[:width])
                    vector = [x//alpha for x in near[:width]]
                    phase = approx.certificate(matrix, triples, vector, indices, level, radius, q)
                    assert int(phase["J"]) <= bound
                    worst = max(worst, int(phase["J"]))
                    float_vector = next(c["coefficients"] for c in entries[indices, level]["candidates"] if c["method"] == "scale8")
                    float_matches += vector == float_vector
                    witnesses.append(dict(indices=list(indices), level=level, combination=combination, J=phase["J"]))
            records.append(dict(n=n, m=m, bits=bits, radius=radius, basis=basis, profile=cert,
                                exact_target_witnesses=witnesses, exact_worst_J=str(worst),
                                floating_tensor_matches=float_matches,
                                universal_budget=approx.budget_info(n, bits, radius, bound),
                                source_key_recovery=run["guaranteed_source_key_recovery"]))
            print(json.dumps(dict(event="basis_certificate", n=n, bits=bits, radius=radius,
                                  H=cert["H"], P=cert["mean_flatness_integer"], targets=len(witnesses),
                                  budget=records[-1]["universal_budget"]["strict_budget"])), flush=True)
    return records


def summary(records):
    return dict(bases=len(records), exact_target_witnesses=sum(len(r["exact_target_witnesses"]) for r in records),
                floating_tensor_matches=sum(r["floating_tensor_matches"] for r in records),
                all_target_budget_passes=sum(r["universal_budget"]["strict_budget"] for r in records),
                budget_passes_without_source_recovery=sum(r["universal_budget"]["strict_budget"] and not
                                                        r["source_key_recovery"] for r in records),
                minimum_mean_flatness=min(int(r["profile"]["mean_flatness_integer"]) for r in records),
                maximum_mean_flatness=max(int(r["profile"]["mean_flatness_integer"]) for r in records))


def verify(path, source):
    result = json.loads(path.read_text())
    assert result["version"] == 1
    assert result["provenance"] == dict(compiler_sha256=digest(COMPILER), source_sha256=digest(SOURCE))
    assert result["checks"] == bound_checks()
    expected = {(c["n"], c["m"], c["bits"], r["radius"]) for c in source["cases"] if c["n"] in (3, 4) for r in c["radii"]}
    assert {(r["n"], r["m"], r["bits"], r["radius"]) for r in result["records"]} == expected
    assert len(result["records"]) == len(expected) == 24
    count = 0
    for record in result["records"]:
        n, m, bits, radius = (record[k] for k in ("n", "m", "bits", "radius"))
        case = next(c for c in source["cases"] if (c["n"], c["m"], c["bits"]) == (n, m, bits))
        run = next(r for r in case["radii"] if r["radius"] == radius)
        q, alpha, width = 1 << bits, 8*radius**3, m**3
        triples, matrix = approx.independent_cubic_matrix(case["blocks"], q)
        basis = record["basis"]
        membership(basis, matrix, alpha, q, width)
        orthogonal, norms = independent_ldl(basis)
        actual_profile = profile(basis, orthogonal, norms, alpha, q, width, len(triples))
        assert actual_profile == record["profile"]
        assert [decode(x) for x in record["profile"]["gso_norms"]] == norms
        bound = int(record["profile"]["H"])
        assert record["universal_budget"] == approx.budget_info(n, bits, radius, bound)
        approx.independent_budget_check(record["universal_budget"], n, bits, radius, bound)
        linear = case["linear_source_filter"]
        if linear["status"] == "ok":
            assert len(linear["vectors"]) == n
            assert {v["coordinate"] for v in linear["vectors"]} == set(range(n))
            masks = [sum((case["blocks"][r][i] for r in range(3)), []) for i in range(n)]
            for v in linear["vectors"]:
                assert len(v["coefficients"]) == 3*m
                assert v["l1"] == str(sum(abs(x) for x in v["coefficients"]))
                assert all(sum(a*b for a, b in zip(row, v["coefficients"])) % q == q//2*int(i == v["coordinate"])
                           for i, row in enumerate(masks))
        recovery = linear["status"] == "ok" and len(linear["vectors"]) == n and all(
            4*radius*int(v["l1"]) < q for v in linear["vectors"])
        assert record["source_key_recovery"] == run["guaranteed_source_key_recovery"] == recovery
        expected_targets = {(t, level) for t in triples for level in range(bits)}
        assert {(tuple(w["indices"]), w["level"]) for w in record["exact_target_witnesses"]} == expected_targets
        assert len(record["exact_target_witnesses"]) == len(expected_targets)
        entries = {(tuple(e["indices"]), e["level"]): e for e in run["entries"]}
        worst = matches = 0
        for witness in record["exact_target_witnesses"]:
            indices, level = tuple(witness["indices"]), witness["level"]
            target = [0]*width+[(1 << level)*int(t == indices) for t in triples]
            combination = witness["combination"]
            assert len(combination) == len(basis)
            near = [sum(c*row[j] for c, row in zip(combination, basis)) for j in range(len(basis))]
            residual = [a-b for a, b in zip(target, near)]
            coordinates = [sum(a*b for a, b in zip(residual, row))/norm for row, norm in zip(orthogonal, norms)]
            assert all(-F(1, 2) <= value <= F(1, 2) for value in coordinates)
            assert sum(x*x for x in residual) == sum(x*x*norm for x, norm in zip(coordinates, norms))
            assert 4*sum(x*x for x in residual) <= sum(norms)
            assert all(x % alpha == 0 for x in near[:width])
            vector = [x//alpha for x in near[:width]]
            phase = approx.certificate(matrix, triples, vector, indices, level, radius, q)
            approx.independent_certificate_check(matrix, triples, vector, phase, indices, level, radius, q)
            assert phase["J"] == witness["J"] and int(phase["J"]) <= bound
            worst = max(worst, int(phase["J"]))
            old_vector = next(c["coefficients"] for c in entries[indices, level]["candidates"] if c["method"] == "scale8")
            matches += vector == old_vector
            count += 1
        assert str(worst) == record["exact_worst_J"] and matches == record["floating_tensor_matches"]
        print(json.dumps(dict(event="replayed_basis", n=n, bits=bits, radius=radius, witnesses=count)), flush=True)
    assert result["summary"] == summary(result["records"])
    assert not result["proved_family_profile_bound"] and not result["production_Lean_changed"]
    print(json.dumps(dict(replayed_bases=24, exact_target_witnesses=count, summary=result["summary"])), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    args = parser.parse_args()
    source = json.loads(SOURCE.read_text())
    if args.verify_existing:
        verify(args.verify_existing, source)
        return
    started = time.monotonic()
    checks = bound_checks()
    records = generate(source)
    result = dict(version=1, scope="Exact universal target bound; no random-mask family theorem",
                  provenance=dict(compiler_sha256=digest(COMPILER), source_sha256=digest(SOURCE)),
                  checks=checks, records=records, summary=summary(records),
                  proved_family_profile_bound=False, production_Lean_changed=False,
                  elapsed_seconds=round(time.monotonic()-started, 3))
    args.output.write_text(json.dumps(result, separators=(",", ":"))+"\n")
    print(json.dumps(result["summary"]), flush=True)


if __name__ == "__main__":
    main()
