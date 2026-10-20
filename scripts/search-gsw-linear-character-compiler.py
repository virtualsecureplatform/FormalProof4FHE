#!/usr/bin/env python3
"""Construct linear-body cubic compilers with quadratic Boolean characters.

The builder is mask-only. Exact modular preimages replace SMT; source noise
is linear, not cubic. Finite certificates do not prove a secure family.
Generation uses existing fpylll; replay needs only Python's standard library.
"""
import argparse
from collections import defaultdict
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent.parent
BOUNDED = ROOT / "scripts/search-gsw-bounded-error-compiler.py"
LATTICE = ROOT / "scripts/search-gsw-cubic-tensor-compiler.py"
VERSION = 1


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


assert digest(BOUNDED) == "d31a5107a24ab52add6603f96cf8ada752c24988ead33848f335252d0571e637"
b = module("bounded_error", BOUNDED)
lattice = module("cubic_lattice", LATTICE)


def coefficient_matrix(matrix, modulus):
    n, width = len(matrix), len(matrix[0])
    triples = list(itertools.combinations(range(n), 3))
    coordinates = [(i, k, j) for i, k in itertools.combinations(range(n), 2) for j in range(width)]
    rows = [[matrix[next(iter(set(triple)-{i, k}))][j] % modulus if i in triple and k in triple else 0
             for i, k, j in coordinates] for triple in triples]
    return triples, coordinates, rows


def verify_coefficient_matrix(matrix, modulus, rows):
    """Integer Boolean finite differences of chi_i*chi_k*(A_j.s).

    Differences are divisible by FOUR over integers before reduction; no
    modular division by a nonunit is used.
    """
    n, width = len(matrix), len(matrix[0])
    independently = []
    for triple in itertools.combinations(range(n), 3):
        row = []
        for i, k in itertools.combinations(range(n), 2):
            for j in range(width):
                total = 0
                for bits in itertools.product((0, 1), repeat=3):
                    secret = [0]*n
                    for r, value in zip(triple, bits):
                        secret[r] = value
                    value = (2*secret[i]-1)*(2*secret[k]-1)*sum(matrix[r][j]*secret[r] for r in range(n))
                    total += (-1)**(3-sum(bits))*value
                assert total % 4 == 0
                row.append(total//4 % modulus)
        independently.append(row)
    assert rows == independently


def compiler_program(matrix, coefficients, indices, level, bits):
    """Sum u_ikj*chi_i(s)*chi_k(s)*y_j, cancel computed lower terms."""
    n, width, q = len(matrix), len(matrix[0]), 1 << bits
    triples, coordinates, rows = coefficient_matrix(matrix, q//4)
    assert len(coefficients) == len(coordinates) and level >= 2
    target = [(1 << (level-2))*int(triple == tuple(indices)) for triple in triples]
    assert all(sum(a*x for a, x in zip(row, coefficients)) % (q//4) == t % (q//4)
               for row, t in zip(rows, target))
    values = defaultdict(int)
    for (i, k, j), value in zip(coordinates, coefficients):
        nu = tuple(int(t == j) for t in range(width))
        for mask, factor in ((0, 1), (1 << i, -2), (1 << k, -2), ((1 << i) | (1 << k), 4)):
            values[(mask, nu)] += factor*value
    initial = b.base.serialize_program(values, n, width, 3, q)
    residual = b.base.normal_form(matrix, 3, initial, indices, level, q)
    assert all(mask.bit_count() <= 2 for (mask, beta), _ in residual.items() if not any(beta))
    for (mask, beta), value in residual.items():
        if not any(beta):
            values[(mask, beta)] -= value
    return b.base.serialize_program(values, n, width, 3, q)


def verify_nonmembership(witness, matrix, target, modulus):
    combination, divisor = witness["combination"], witness["divisor"]
    assert len(combination) == len(matrix) and divisor > 0 and modulus % divisor == 0
    assert all(sum(combination[i]*matrix[i][j] for i in range(len(matrix))) % divisor == 0
               for j in range(len(matrix[0])))
    residue = sum(a*t for a, t in zip(combination, target)) % modulus
    assert residue == witness["target_residue"] and residue % divisor != 0


def verify_recovery(record, blocks, bits, radius):
    matrix, q = b.base.joined(blocks), 1 << bits
    for item in record["vectors"]:
        vector, index = item["coefficients"], item["coordinate"]
        assert len(vector) == len(matrix[0])
        assert item["l1"] == str(sum(map(abs, vector)))
        assert all(sum(a*x for a, x in zip(row, vector)) % q == (q//2 if i == index else 0)
                   for i, row in enumerate(matrix))
    complete = record["status"] == "ok" and len(record["vectors"]) == len(matrix)
    guaranteed = complete and all(4*radius*int(item["l1"]) < q for item in record["vectors"])
    assert record["guaranteed_matching_radius_recovery"] == guaranteed
    if record["status"] == "incomplete_key_recovery":
        target = [q//2*int(i == record["coordinate"]) for i in range(len(matrix))]
        verify_nonmembership(record["witness"], matrix, target, q)


def worker(connection, blocks, bits, radius):
    started = time.monotonic()
    try:
        from fpylll import __version__ as version
        matrix, q = b.base.joined(blocks), 1 << bits
        triples, _, rows = coefficient_matrix(matrix, q//4)
        solve = lattice.public_solver(rows, q//4, bits-2)
        vectors = []
        for indices in triples:
            for level in reversed(range(2, bits)):
                target = [(1 << (level-2))*int(triple == indices) for triple in triples]
                record = dict(indices=list(indices), level=level)
                try:
                    record["coefficients"] = solve(target)
                except lattice.UnsolvableTarget as error:
                    record["nonmembership"] = error.witness
                vectors.append(record)
        recovery = lattice.linear_recovery(blocks, q, bits)
        recovery["guaranteed_matching_radius_recovery"] = recovery["status"] == "ok" and all(
            4*radius*int(v["l1"]) < q for v in recovery["vectors"])
        connection.send(dict(status="complete", vectors=vectors, source_recovery=recovery,
                             fpylll_version=version, elapsed_seconds=round(time.monotonic()-started, 3)))
    except Exception as error:
        connection.send(dict(status="worker_error", error=type(error).__name__+": "+str(error)))
    finally:
        connection.close()


def baseline(matrix, indices, level, bits, radius):
    n, width = len(matrix), len(matrix[0])
    return b.make_certificate(matrix, 3, b.base.zero_baseline(n, width, 3, indices, level, 1 << bits),
                              indices, level, bits, radius)


def summary(result):
    slots = [slot for case in result["cases"] for slot in case["slots"]]
    complete = [case for case in result["cases"] if case["attempt"]["status"] == "complete"]
    passes = [case for case in complete if case["budget"]["strict_budget"]]
    return dict(cases=len(result["cases"]), completed_lattice_cases=len(complete),
                returned_preimages=sum("candidate" in s for s in slots),
                certified_nonmemberships=sum("nonmembership" in s for s in slots),
                selected_improvements=sum(s["improved"] for s in slots),
                required_slots=len(slots), verified_source_fixtures=sum(len(s["fixtures"]) for s in slots),
                complete_table_passes=len(passes),
                passes_without_matching_radius_recovery=sum(not c["attempt"]["source_recovery"]["guaranteed_matching_radius_recovery"] for c in passes))


def generate(args):
    started = time.monotonic()
    result = dict(version=VERSION, scope="Linear-source-error compiler; finite research, not a security theorem",
                  provenance=dict(script_sha256=digest(Path(__file__)), bounded_sha256=digest(BOUNDED), lattice_sha256=digest(LATTICE)),
                  config=dict(case_seconds=args.case_seconds, global_seconds=args.global_seconds, quick=args.quick),
                  cases=[], proved_family_success=False, proved_ppt_reduction=False,
                  status="running")
    configurations = b.CONFIGURATIONS[:1] if args.quick else b.CONFIGURATIONS
    for n, m, bits in configurations:
        seed, blocks = b.base.case_masks(n, m, bits)
        matrix, radius = b.base.joined(blocks), b.base.family_radius(bits)
        triples, _, rows = coefficient_matrix(matrix, 1 << (bits-2))
        verify_coefficient_matrix(matrix, 1 << (bits-2), rows)
        remaining = args.global_seconds-(time.monotonic()-started)
        attempt = (b.base.bounded_call(worker, (blocks, bits, radius), min(remaining, args.case_seconds)) if remaining > 0
                   else dict(status="global_deadline_unstarted"))
        case = dict(n=n, m=m, bits=bits, seed=seed, blocks=blocks, radius=radius, attempt=attempt, slots=[])
        result["cases"].append(case)
        indexed = {(tuple(v["indices"]), v["level"]): v for v in attempt.get("vectors", [])}
        for indices in triples:
            for level in range(bits):
                old = baseline(matrix, indices, level, bits, radius)
                selected = old
                slot = dict(indices=list(indices), level=level, baseline_J=old["bound"]["J"], improved=False)
                vector = indexed.get((indices, level))
                if vector and "coefficients" in vector:
                    coefficients = vector["coefficients"]
                    program = compiler_program(matrix, coefficients, indices, level, bits)
                    certificate = b.make_certificate(matrix, 3, program, indices, level, bits, radius)
                    b.independent_verify(certificate, matrix, bits)
                    b.reconstruct_program(certificate, matrix, bits)
                    slot.update(coefficients=coefficients, candidate=certificate,
                                character_l1=str(sum(map(abs, coefficients))))
                    # No coefficient-wrap issue is hidden inside the analytic bound.
                    assert int(certificate["bound"]["J"]) == radius*sum(map(abs, coefficients))
                    if int(certificate["bound"]["J"]) < int(old["bound"]["J"]):
                        selected, slot["improved"] = certificate, True
                elif vector and "nonmembership" in vector:
                    target = [(1 << (level-2))*int(triple == indices) for triple in triples]
                    verify_nonmembership(vector["nonmembership"], rows, target, 1 << (bits-2))
                    slot["nonmembership"] = vector["nonmembership"]
                b.independent_verify(selected, matrix, bits)
                value = b.base.fixture(matrix, selected, bits, seed+60000000+10000*level+sum(1 << i for i in indices))
                b.base.verify_fixture(value, selected, matrix, bits)
                slot.update(selected=selected, fixtures=[value])
                case["slots"].append(slot)
        case["expected_slots"] = len(triples)*bits
        case["all_slots_certified"] = len(case["slots"]) == case["expected_slots"]
        maximum = max(int(s["selected"]["bound"]["J"]) for s in case["slots"])
        case["budget"] = b.budget(n, bits, radius, maximum)
        if attempt["status"] == "complete":
            verify_recovery(attempt["source_recovery"], blocks, bits, radius)
            assert len(indexed) == len(triples)*(bits-2)
        result["summary"] = summary(result)
        b.base.atomic_write(args.output, result)
        print(json.dumps(dict(event="case", n=n, m=m, bits=bits, status=attempt["status"],
                              max_J=str(maximum), budget_pass=case["budget"]["strict_budget"])), flush=True)
    result["status"] = "complete"
    result["elapsed_seconds"] = round(time.monotonic()-started, 3)
    result["summary"] = summary(result)
    b.base.atomic_write(args.output, result)
    print(json.dumps(result["summary"]), flush=True)


def replay(path):
    result = json.loads(path.read_text())
    assert result["version"] == VERSION and result["status"] == "complete"
    assert result["provenance"] == dict(script_sha256=digest(Path(__file__)), bounded_sha256=digest(BOUNDED), lattice_sha256=digest(LATTICE))
    assert not result["proved_family_success"] and not result["proved_ppt_reduction"]
    configurations = b.CONFIGURATIONS[:1] if result["config"]["quick"] else b.CONFIGURATIONS
    assert [(c["n"], c["m"], c["bits"]) for c in result["cases"]] == list(configurations)
    checked = 0
    for case in result["cases"]:
        n, m, bits, radius = case["n"], case["m"], case["bits"], case["radius"]
        seed, blocks = b.base.case_masks(n, m, bits)
        assert case["seed"] == seed and case["blocks"] == blocks and radius == b.base.family_radius(bits)
        matrix = b.base.joined(blocks)
        triples, coordinates, rows = coefficient_matrix(matrix, 1 << (bits-2))
        verify_coefficient_matrix(matrix, 1 << (bits-2), rows)
        expected = [(list(indices), level) for indices in triples for level in range(bits)]
        assert [(s["indices"], s["level"]) for s in case["slots"]] == expected
        assert case["all_slots_certified"] and case["expected_slots"] == len(expected)
        indexed = {(tuple(v["indices"]), v["level"]): v for v in case["attempt"].get("vectors", [])}
        if case["attempt"]["status"] == "complete":
            assert len(indexed) == len(triples)*(bits-2) == len(case["attempt"]["vectors"])
            assert set(indexed) == {(indices, level) for indices in triples for level in range(2, bits)}
            verify_recovery(case["attempt"]["source_recovery"], blocks, bits, radius)
        for slot in case["slots"]:
            indices, level = tuple(slot["indices"]), slot["level"]
            old = baseline(matrix, indices, level, bits, radius)
            assert slot["baseline_J"] == old["bound"]["J"]
            selected = old
            vector = indexed.get((indices, level))
            assert ("candidate" in slot) == bool(vector and "coefficients" in vector)
            assert ("nonmembership" in slot) == bool(vector and "nonmembership" in vector)
            if "candidate" in slot:
                coefficients, cert = slot["coefficients"], slot["candidate"]
                assert coefficients == vector["coefficients"] and len(coefficients) == len(coordinates)
                assert cert["program"] == compiler_program(matrix, coefficients, indices, level, bits)
                assert cert["degree"] == 3 and cert["indices"] == list(indices) and cert["level"] == level and cert["radius"] == radius
                b.independent_verify(cert, matrix, bits)
                b.reconstruct_program(cert, matrix, bits)
                assert slot["character_l1"] == str(sum(map(abs, coefficients)))
                assert int(cert["bound"]["J"]) == radius*int(slot["character_l1"])
                if int(cert["bound"]["J"]) < int(old["bound"]["J"]):
                    selected = cert
                checked += 1
            elif "nonmembership" in slot:
                assert slot["nonmembership"] == vector["nonmembership"]
                target = [(1 << (level-2))*int(triple == indices) for triple in triples]
                verify_nonmembership(slot["nonmembership"], rows, target, 1 << (bits-2))
            assert slot["selected"] == selected
            assert slot["improved"] == (int(selected["bound"]["J"]) < int(old["bound"]["J"]))
            b.independent_verify(selected, matrix, bits)
            assert len(slot["fixtures"]) == 1
            for value in slot["fixtures"]:
                assert value == b.base.fixture(matrix, selected, bits, seed+60000000+10000*level+sum(1 << i for i in indices))
                b.base.verify_fixture(value, selected, matrix, bits)
            checked += 1
        maximum = max(int(s["selected"]["bound"]["J"]) for s in case["slots"])
        b.verify_budget(case["budget"], n, bits, radius, maximum)
    assert result["summary"] == summary(result)
    print(json.dumps(dict(verified_certificates=checked, summary=result["summary"])), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--case-seconds", type=float, default=30)
    parser.add_argument("--global-seconds", type=float, default=1200)
    args = parser.parse_args()
    assert args.case_seconds > 0 and args.global_seconds > 0
    if args.verify_existing:
        replay(args.verify_existing)
    else:
        generate(args)


if __name__ == "__main__":
    main()
