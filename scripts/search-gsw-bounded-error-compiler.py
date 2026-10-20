#!/usr/bin/env python3
"""Bounded lower-order noise in public Boolean polynomial compilers.

Finite exact certificates, not an ordinary-LWE-only FHE security proof.
Generation uses optional Z3; artifact replay uses only the standard library.
The old compiler and artifact are immutable, hashed regression inputs.
"""
import argparse
from collections import defaultdict
import copy
from fractions import Fraction
import hashlib
import importlib.util
import itertools
import json
import math
import multiprocessing
from pathlib import Path
import random
import tempfile
import time
from types import SimpleNamespace


ROOT = Path(__file__).resolve().parent.parent
OLD_SCRIPT = ROOT / "scripts/search-gsw-boolean-polynomial-compiler.py"
OLD_ARTIFACT = ROOT / "docs/GSWBooleanPolynomialCompilerExploration.json"
OLD_SCRIPT_SHA = "c17cfb628261202cd542234f334cf8101570b83eddda9d2123582e741a5c83b6"
OLD_ARTIFACT_SHA = "0d31ce540c3d6224528fa31c59c24c5d9e025a89c5e395a714f2561f0398a094"
VERSION = 1
CONFIGURATIONS = ((3, 1, 64), (4, 1, 68), (6, 1, 80), (3, 2, 64))
DEGREES = (3, 4)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert sha256(OLD_SCRIPT) == OLD_SCRIPT_SHA, "old implementation changed"
spec = importlib.util.spec_from_file_location("gsw_boolean_polynomial_frozen", OLD_SCRIPT)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def residual_grammar(n, width, degree):
    """Residual secret degree can exceed TWO, unlike the output grammar."""
    return [(mask, beta) for beta in base.exponents(width, degree)
            for mask in base.supports(n, degree-sum(beta))]


def bound_from_residual(residual, n, degree, radius):
    """Walsh transform in s for EACH error monomial, with exact lifts."""
    scale, transformed, layers = 1 << degree, [], defaultdict(int)
    grouped = defaultdict(dict)
    for (mask, beta), value in residual.items():
        assert mask.bit_count()+sum(beta) <= degree
        grouped[beta][mask] = value
    width = len(next(iter(residual))[1]) if residual else 0
    for beta in base.exponents(width, degree) if residual else ():
        if beta not in grouped:
            continue
        for mask in base.supports(n, degree-sum(beta)):
            value = sum((1 << (degree-source.bit_count()))*coefficient
                        for source, coefficient in grouped[beta].items() if source & mask == mask)
            if value:
                transformed.append([mask, list(beta), value])
                layers[sum(beta)] += radius**sum(beta)*abs(value)
    numerator = sum(layers.values())
    return dict(scale=scale, walsh_scaled=transformed,
                weighted_numerator_by_order=[[order, str(value)] for order, value in sorted(layers.items())],
                numerator=str(numerator), J=str((numerator+scale-1)//scale))


def make_certificate(matrix, degree, program, indices, level, bits, radius):
    residual = base.normal_form(matrix, degree, program, indices, level, 1 << bits)
    return dict(degree=degree, indices=list(indices), level=level, radius=radius, program=program,
                residual=[[mask, list(beta), value] for (mask, beta), value in sorted(residual.items())],
                bound=bound_from_residual(residual, len(matrix), degree, radius))


def lower_order_nonzero(certificate):
    return any(sum(beta) in (1, 2) and coefficient for _, beta, coefficient in certificate["residual"])


def class_lower_bound(radius, level):
    """For this certificate: nonzero integer Boolean polynomial has norm >=1.

    A nonzero error layer costs at least E. If all error layers vanish,
    translation e=y-A^T*s makes P independent of y; a quadratic's cubic
    discrepancy has Walsh coefficient -w/8. This is not a security bound.
    """
    return min(radius, ((1 << level)+7)//8)


def budget(n, bits, radius, J):
    """Documented conservative 4*F gate, not the old toy F-only flag."""
    rows, q = n*n+n+1, 1 << bits
    growth = rows*bits
    lookup = 1 << (8*rows-1).bit_length()
    factor = lookup**2*rows*growth*(growth+1)**2
    cap = (q-1)//(4*factor)
    complete = J+(n+1)*radius
    samples = growth+2*bits+17
    fresh = samples*(n+1)*radius
    output = lookup*rows*growth*(growth+1)*complete
    return dict(lookup=lookup, refresh_factor=str(factor), control_cap=str(cap),
                J_cap=str(cap-(n+1)*radius), control_bound=str(complete),
                conservative_refresh_bound=str(4*factor*complete),
                fresh_encryption_bound=str(fresh), fresh_output_bound=str(output),
                fresh_bound_fits=fresh <= output,
                strict_budget=4*factor*complete < q and fresh <= output)


def verify_budget(record, n, bits, radius, J):
    """Independent arithmetic, including floor/strict-inequality equivalence."""
    rows = n*n+n+1
    lookup = 1
    while lookup < 8*rows:
        lookup *= 2
    g, q = rows*bits, 2**bits
    f = lookup*lookup*rows*g*(g+1)*(g+1)
    cap = (q-1)//(4*f)
    complete = J+(n+1)*radius
    fresh = (g+2*bits+17)*(n+1)*radius
    output = lookup*rows*g*(g+1)*complete
    assert (complete <= cap) == (4*f*complete < q)
    assert record == dict(lookup=lookup, refresh_factor=str(f), control_cap=str(cap),
                          J_cap=str(cap-(n+1)*radius), control_bound=str(complete),
                          conservative_refresh_bound=str(4*f*complete),
                          fresh_encryption_bound=str(fresh), fresh_output_bound=str(output),
                          fresh_bound_fits=fresh <= output,
                          strict_budget=complete <= cap and fresh <= output)


def maximum_error_order(radius, limit, degree):
    # A nonzero integer Boolean coefficient polynomial has Walsh L1 >= 1.
    return max((order for order in range(degree+1) if radius**order <= limit), default=-1)


def effective_degree(degree, radius, limit):
    """If residual error degree <=k, inverse translation gives y-degree <=k.

    The output has s-degree <=2, hence total degree <=k+2. For k=1,
    degree FOUR and degree THREE queries have exactly the same feasible set.
    Reuse of an unknown result remains unknown, never an exclusion proof.
    """
    return min(degree, maximum_error_order(radius, limit, degree)+2)


def build_inverse_rows(matrix, degree, q, radius=None, limit=None):
    n, width = len(matrix), len(matrix[0])
    keys = residual_grammar(n, width, degree)
    active = [key for key in keys if not any(key[1]) or limit is None or radius**sum(key[1]) <= limit]
    inverse_columns = {beta: column for (mask, beta), column in zip(
        base.grammar(n, width, degree), base.expansion_columns(
            [[-value for value in row] for row in matrix], degree, q)) if mask == 0}
    rows = defaultdict(dict)
    for source in active:
        mask, beta = source
        combined = defaultdict(int)
        for (inner, nu), value in inverse_columns[beta].items():
            combined[(mask | inner, nu)] += value
        for output, value in combined.items():
            if value % q:
                rows[output][source] = base.centered(value, q)
    return active, rows, len(keys)-len(active)


def reconstruct_program(certificate, matrix, bits):
    """Inverse substitution allows all residual secret supports."""
    degree, q = certificate["degree"], 1 << bits
    n, width = len(matrix), len(matrix[0])
    _, rows, _ = build_inverse_rows(matrix, degree, q)
    residual = {(mask, tuple(beta)): value for mask, beta, value in certificate["residual"]}
    target = (sum(1 << i for i in certificate["indices"]), (0,)*width)
    rows.setdefault(target, {})
    output = {key: ((1 << certificate["level"]) if key == target else 0)+
                   sum(value*residual.get(source, 0) for source, value in coefficients.items())
              for key, coefficients in rows.items()}
    assert all(value % q == 0 for (mask, _), value in output.items() if mask.bit_count() > 2)
    assert base.serialize_program({key: value for key, value in output.items() if key[0].bit_count() <= 2},
                                  n, width, degree, q) == certificate["program"]


def independent_verify(certificate, matrix, bits):
    """Truth-table polynomial convolution, Mobius inversion, Walsh averaging.

    Shares neither forward/inverse symbolic substitution nor the bound
    routine with generation. Integer lifts are taken BEFORE Walsh averaging.
    """
    n, width = len(matrix), len(matrix[0])
    degree, radius, q = certificate["degree"], certificate["radius"], 1 << bits
    assert 3 <= degree <= 5 and radius >= 1
    assert all(len(row) == width and all(type(a) is int and 0 <= a < q for a in row) for row in matrix)
    base.program_terms(certificate["program"], n, width, degree, q)
    indices, level = certificate["indices"], certificate["level"]
    assert len(indices) == len(set(indices)) == 3 and all(0 <= i < n for i in indices)
    assert 0 <= level < bits
    evaluations = {}
    for key in range(1 << n):
        secret = [(key >> i) & 1 for i in range(n)]
        noiseless = [sum(secret[i]*matrix[i][j] for i in range(n)) % q for j in range(width)]
        values = defaultdict(int)
        for mask, powers, coefficient in certificate["program"]:
            if mask & key != mask:
                continue
            factors = []
            for value, power in zip(noiseless, powers):
                polynomial = [1]
                for _ in range(power):
                    multiplied = [0]*(len(polynomial)+1)
                    for j, entry in enumerate(polynomial):
                        multiplied[j] += entry*value
                        multiplied[j+1] += entry
                    polynomial = [entry % q for entry in multiplied]
                factors.append(polynomial)
            for beta in itertools.product(*(range(len(poly)) for poly in factors)):
                value = coefficient
                for poly, exponent in zip(factors, beta):
                    value *= poly[exponent]
                values[beta] += value
        values[(0,)*width] -= (1 << level)*math.prod(secret[i] for i in indices)
        evaluations[key] = {beta: value % q for beta, value in values.items() if value % q}
    residual = {}
    betas = list(base.exponents(width, degree))
    for beta in betas:
        values = [evaluations[key].get(beta, 0) for key in range(1 << n)]
        for i in range(n):
            for key in range(1 << n):
                if key & (1 << i):
                    values[key] = (values[key]-values[key ^ (1 << i)]) % q
        for mask, value in enumerate(values):
            if value:
                assert mask.bit_count()+sum(beta) <= degree
                residual[(mask, beta)] = (value+q//2) % q-q//2
    recorded = {(mask, tuple(beta)): coefficient for mask, beta, coefficient in certificate["residual"]}
    assert len(recorded) == len(certificate["residual"]) and recorded == residual
    scale, walsh, layers = 2**degree, [], defaultdict(int)
    mask_order = sorted(range(1 << n), key=lambda mask: (mask.bit_count(), tuple(i for i in range(n) if mask & (1 << i))))
    for beta in betas:
        values = [sum(value for (mask, powers), value in residual.items()
                      if powers == beta and mask & key == mask) for key in range(1 << n)]
        for mask in mask_order:
            value = Fraction(sum(v*(-1)**((mask & ~key).bit_count()) for key, v in enumerate(values)), 1 << n)
            if value:
                assert mask.bit_count()+sum(beta) <= degree
                assert (scale*value).denominator == 1
                scaled = int(scale*value)
                walsh.append([mask, list(beta), scaled])
                layers[sum(beta)] += radius**sum(beta)*abs(scaled)
    numerator = sum(layers.values())
    expected = dict(scale=scale, walsh_scaled=walsh,
                    weighted_numerator_by_order=[[k, str(v)] for k, v in sorted(layers.items())],
                    numerator=str(numerator), J=str(base.ceil_fraction(Fraction(numerator, scale))))
    assert certificate["bound"] == expected
    assert int(expected["J"]) >= class_lower_bound(radius, level)
    return residual


def solve_worker(connection, matrix, bits, radius, degree, indices, level, limit, warm, seconds):
    started = time.monotonic()
    try:
        import z3
        q, n, width = 1 << bits, len(matrix), len(matrix[0])
        keys, rows, pruned = build_inverse_rows(matrix, degree, q, radius, limit)
        target = (sum(1 << i for i in indices), (0,)*width)
        rows.setdefault(target, {})
        optimizer = z3.Optimize()
        variables = {key: z3.Int(f"r_{j}") for j, key in enumerate(keys)}
        initial = {(mask, tuple(beta)): value for mask, beta, value in warm["residual"]} if warm else {}
        for key, value in variables.items():
            optimizer.add(value >= -q//2, value < q//2)
            optimizer.set_initial_value(value, initial.get(key, 0))
        optimizer.add(z3.Or([value != 0 for (_, beta), value in variables.items() if sum(beta) in (1, 2)]))
        constraints = 0
        for number, (key, coefficients) in enumerate(sorted(rows.items())):
            if key[0].bit_count() > 2:
                expression = z3.Sum([value*variables[source] for source, value in coefficients.items()])
                optimizer.add(expression+((1 << level) if key == target else 0) == q*z3.Int(f"z_{number}"))
                constraints += 1
        by_beta = defaultdict(dict)
        for (mask, beta), value in variables.items():
            by_beta[beta][mask] = value
        terms, absolute_count = [], 0
        for beta, coefficients in by_beta.items():
            for mask in base.supports(n, degree-sum(beta)):
                expression = z3.Sum([(1 << (degree-source.bit_count()))*value
                                     for source, value in coefficients.items() if source & mask == mask])
                absolute = z3.Int(f"abs_{absolute_count}")
                absolute_count += 1
                optimizer.add(absolute >= expression, absolute >= -expression)
                terms.append(radius**sum(beta)*absolute)
        objective = z3.Sum(terms)
        optimizer.add(objective <= (1 << degree)*limit)
        optimizer.minimize(objective)
        built = time.monotonic()
        record = dict(encoding="all_error_residual", variables=len(variables),
                      pruned_error_coefficients=pruned, constraints=constraints,
                      program_coefficients=len(base.grammar(n, width, degree)),
                      solver_version=z3.get_version_string(), build_seconds=round(built-started, 3))
        remaining = seconds-(built-started)-0.5
        if remaining <= 0:
            record["status"] = "build_deadline"
        else:
            optimizer.set(timeout=max(1, int(remaining*1000)))
            status = optimizer.check()
            record["status"] = str(status)
            if status == z3.unknown:
                record["reason"] = optimizer.reason_unknown()
            if status != z3.unsat:
                try:
                    model = optimizer.model()
                    concrete = {key: model.eval(value, model_completion=True).as_long() for key, value in variables.items()}
                    output = {key: ((1 << level) if key == target else 0)+
                                   sum(value*concrete[source] for source, value in coefficients.items())
                              for key, coefficients in rows.items() if key[0].bit_count() <= 2}
                    program = base.serialize_program(output, n, width, degree, q)
                    candidate = make_certificate(matrix, degree, program, indices, level, bits, radius)
                    assert {(mask, tuple(beta)): value for mask, beta, value in candidate["residual"]} == {
                        key: value for key, value in concrete.items() if value}
                    assert lower_order_nonzero(candidate) and int(candidate["bound"]["J"]) <= limit
                    record["candidate"] = candidate
                except Exception as error:
                    record["model_unavailable_or_rejected"] = type(error).__name__+": "+str(error)[:200]
        record["elapsed_seconds"] = round(time.monotonic()-started, 3)
        connection.send(record)
    except Exception as error:
        connection.send(dict(status="worker_error", error=type(error).__name__+": "+str(error)[:300]))
    finally:
        connection.close()


def attempt_search(matrix, bits, radius, requested_degree, indices, level, limit, warm, seconds, coefficient_limit):
    if limit < radius:
        return dict(status="nonzero_error_floor", certified_lower_bound=str(radius), worker_started=False)
    degree = effective_degree(requested_degree, radius, limit)
    program_count = len(base.grammar(len(matrix), len(matrix[0]), degree))
    residual_count = len(residual_grammar(len(matrix), len(matrix[0]), degree))
    if max(program_count, residual_count) > coefficient_limit:
        return dict(status="coefficient_limit", worker_started=False,
                    program_coefficients=program_count, residual_coefficients=residual_count)
    response = base.bounded_call(solve_worker, (matrix, bits, radius, degree, indices, level, limit, warm, seconds), seconds)
    response["worker_started"] = True
    return response


def accept_model(entry, matrix, case, seed):
    if "candidate" not in entry:
        return
    certificate = entry["candidate"]
    assert certificate["radius"] == case["radius"]
    assert certificate["degree"] == entry["effective_degree"]
    independent_verify(certificate, matrix, case["bits"])
    reconstruct_program(certificate, matrix, case["bits"])
    assert lower_order_nonzero(certificate)
    assert int(certificate["bound"]["J"]) <= int(entry["query_limit"])
    entry["fixtures"] = [base.fixture(matrix, certificate, case["bits"], seed+i) for i in range(4)]
    for value in entry["fixtures"]:
        base.verify_fixture(value, certificate, matrix, case["bits"])
    entry["budget"] = budget(case["n"], case["bits"], certificate["radius"], int(certificate["bound"]["J"]))
    verify_budget(entry["budget"], case["n"], case["bits"], certificate["radius"], int(certificate["bound"]["J"]))
    assert entry["budget"]["strict_budget"]


def regression_checks():
    assert sha256(OLD_ARTIFACT) == OLD_ARTIFACT_SHA, "old artifact changed"
    old = json.loads(OLD_ARTIFACT.read_text())
    count = fixtures = improved = 0
    for case in old["cases"]:
        matrix = base.joined(case["blocks"])
        items = list(case["baselines"])+[entry for entry in case["attempts"] if "candidate" in entry]
        for item in items:
            certificate = item.get("certificate", item.get("candidate"))
            base.independent_verify(certificate, matrix, case["bits"])
            adapted = make_certificate(matrix, certificate["degree"], certificate["program"],
                                       certificate["indices"], certificate["level"], case["bits"], certificate["radius"])
            independent_verify(adapted, matrix, case["bits"])
            assert int(adapted["bound"]["J"]) <= int(certificate["bound"]["J"])
            improved += int(int(adapted["bound"]["J"]) < int(certificate["bound"]["J"]))
            for value in item["fixtures"]:
                base.verify_fixture(value, adapted, matrix, case["bits"])
                fixtures += 1
            count += 1
    assert count == 82 and fixtures == 112
    return dict(certificates=count, full_coordinate_fixtures=fixtures, nonworsened=count,
                strictly_improved_bounds=improved, old_script_sha256=OLD_SCRIPT_SHA, old_artifact_sha256=OLD_ARTIFACT_SHA)


def structured_fixture():
    matrix = [[128, 0, 0], [0, 1, 0], [0, 0, 1]]
    certificate = make_certificate(matrix, 3, [[6, [1, 0, 0], 1]], (0, 1, 2), 7, 8, 2)
    return matrix, certificate


def self_checks():
    counts = dict(structured_phase_cases=0, inverse_roundtrips=0, dense_certificates=0,
                  residual_high_secret_supports=0, malformed_certificates_rejected=0,
                  corrupted_coordinate_views_rejected=0, integer_boolean_norm_checks=0,
                  full_coordinate_fixtures=0, budget_checks=0)
    matrix, certificate = structured_fixture()
    independent_verify(certificate, matrix, 8)
    reconstruct_program(certificate, matrix, 8)
    counts["inverse_roundtrips"] += 1
    assert certificate["bound"]["J"] == "2" and base.class_lower_bound(2, 7) == 8
    assert lower_order_nonzero(certificate)
    for secret in itertools.product((0, 1), repeat=3):
        for errors in itertools.product(range(-2, 3), repeat=3):
            bodies = [(sum(secret[i]*matrix[i][j] for i in range(3))+errors[j]) % 256 for j in range(3)]
            t, c, b = base.compile_control(certificate["program"], 3, bodies, 256)
            phase = b+sum(secret[i]*c[i] for i in range(3))-sum(secret[i]*t[i][j]*secret[j] for i in range(3) for j in range(3))
            assert base.centered(phase-128*math.prod(secret), 256) == errors[0]*secret[1]*secret[2]
            counts["structured_phase_cases"] += 1
    examples = [(matrix, certificate, 8)]
    for n in (3, 4):
        for bits in (1, 3, 5):
            q = 1 << bits
            rng = random.Random(20261027+100*n+bits)
            dense = [[rng.randrange(q) for _ in range(3)] for _ in range(n)]
            for degree in DEGREES:
                keys = base.grammar(n, 3, degree)
                chosen = rng.sample(keys, 7)
                program = base.serialize_program({key: rng.randrange(q) for key in chosen}, n, 3, degree, q)
                cert = make_certificate(dense, degree, program, (0, 1, 2), bits-1, bits, 2)
                independent_verify(cert, dense, bits)
                reconstruct_program(cert, dense, bits)
                counts["inverse_roundtrips"] += 1
                counts["dense_certificates"] += 1
                counts["residual_high_secret_supports"] += sum(mask.bit_count() > 2 and any(beta) for mask, beta, _ in cert["residual"])
                examples.append((dense, cert, bits))
    # A deliberate order-one, secret-degree-three coefficient must be retained.
    dense = [[1, 2, 3], [3, 1, 2], [2, 4, 1], [1, 1, 1]]
    cert = make_certificate(dense, 4, [[0, [4, 0, 0], 1]], (0, 1, 2), 4, 5, 2)
    independent_verify(cert, dense, 5)
    reconstruct_program(cert, dense, 5)
    assert any(mask.bit_count() == 3 and sum(beta) == 1 for mask, beta, _ in cert["residual"])
    counts["inverse_roundtrips"] += 1
    examples.append((dense, cert, 5))
    # Cancellation inside a positive-error coefficient: (2*s-1)*e^3+e^4.
    identity = [[int(i == j) for j in range(3)] for i in range(3)]
    helper = base.serialize_program({(0, (4, 0, 0)): 1, (0, (3, 0, 0)): -1,
                                    (1, (3, 0, 0)): -2, (1, (2, 0, 0)): 3,
                                    (1, (1, 0, 0)): -1}, 3, 3, 4, 256)
    cert = make_certificate(identity, 4, helper, (0, 1, 2), 0, 8, 2)
    independent_verify(cert, identity, 8)
    assert cert["bound"]["J"] == "25"
    assert base.make_certificate(identity, 4, helper, (0, 1, 2), 0, 256, 2)["bound"]["J"] == "41"
    examples.append((identity, cert, 8))
    for coefficients in itertools.product((-1, 0, 1), repeat=4):
        if any(coefficients):
            h = [sum((Fraction(coefficients[u], 2**u.bit_count()) for u in range(4) if u & k == k), Fraction()) for k in range(4)]
            assert sum(map(abs, h)) >= 1
            counts["integer_boolean_norm_checks"] += 1
    for fault in ("J", "numerator", "walsh", "layers", "program", "duplicate", "lower_order", "degree"):
        broken = copy.deepcopy(certificate)
        if fault in ("J", "numerator"):
            broken["bound"][fault] = "999999"
        elif fault == "walsh":
            broken["bound"]["walsh_scaled"][0][2] += 1
        elif fault == "layers":
            broken["bound"]["weighted_numerator_by_order"][0][1] = "0"
        elif fault == "program":
            broken["program"][0][2] = 256
        elif fault == "duplicate":
            broken["residual"].append(broken["residual"][0])
        elif fault == "lower_order":
            broken["residual"] = []
        else:
            broken["degree"] = 2
        try:
            independent_verify(broken, matrix, 8)
        except AssertionError:
            counts["malformed_certificates_rejected"] += 1
        else:
            raise AssertionError("accepted malformed certificate: "+fault)
    for j, (a, cert, bits) in enumerate(examples):
        value = base.fixture(a, cert, bits, 20261028+j)
        base.verify_fixture(value, cert, a, bits)
        counts["full_coordinate_fixtures"] += 1
        if j < 3:
            for coordinate in range(3):
                broken = copy.deepcopy(value)
                control = broken["output"]["control"]
                if coordinate == 0:
                    control[0][0][0] ^= 1
                elif coordinate == 1:
                    control[1][0] ^= 1
                else:
                    control[2] ^= 1
                try:
                    base.verify_fixture(broken, cert, a, bits)
                except AssertionError:
                    counts["corrupted_coordinate_views_rejected"] += 1
                else:
                    raise AssertionError("accepted corrupt output coordinate")
    for n, m, bits in CONFIGURATIONS:
        radius = base.family_radius(bits)
        record = budget(n, bits, radius, 0)
        cap = int(record["J_cap"])
        assert radius <= cap < radius**3
        for j in (0, cap, cap+1):
            verify_budget(budget(n, bits, radius, j), n, bits, radius, j)
            counts["budget_checks"] += 1
        assert effective_degree(4, radius, cap) == (4 if n == 6 else 3)
    assert int(budget(4, 64, 256, 0)["J_cap"]) == 98 < 256
    assert counts["residual_high_secret_supports"] > 0
    return counts


def solver_check():
    matrix, certificate = structured_fixture()
    response = base.bounded_call(solve_worker, (matrix, 8, 2, 3, (0, 1, 2), 7, 2, certificate, 5), 5)
    assert "candidate" in response, response
    independent_verify(response["candidate"], matrix, 8)
    reconstruct_program(response["candidate"], matrix, 8)
    assert response["candidate"]["bound"]["J"] == "2" and lower_order_nonzero(response["candidate"])
    return response


def summarize(result):
    entries = [entry for case in result["cases"] for entry in case["attempts"]]
    table_entries = [slot["attempt"] for table in result["full_tables"] for slot in table["slots"]]
    models = [entry for entry in entries+table_entries if "candidate" in entry]
    fixtures = [f for case in result["cases"] for f in case["baseline"]["fixtures"]]
    fixtures += [f for entry in models for f in entry["fixtures"]]
    fixtures += [f for table in result["full_tables"] for slot in table["slots"] for f in slot["fixtures"]]
    return dict(cases=len(result["cases"]), screen_entries=len(entries),
                screen_statuses={status: sum(entry["status"] == status for entry in entries) for status in sorted({entry["status"] for entry in entries})},
                optimizer_queries=sum(entry.get("worker_started", False) for entry in entries+table_entries),
                accepted_models=len(models), baseline_certificates=len(result["cases"]),
                full_tables=len(result["full_tables"]), full_table_slots=len(table_entries),
                full_table_budget_passes=sum(table.get("budget", {}).get("strict_budget", False) for table in result["full_tables"]),
                verified_source_phases=len(fixtures), sampled_margin_failures=sum(not f["strict_decoding_margin"] for f in fixtures),
                toy_source_unique_key_fixtures=sum(len(f["compatible_binary_keys"]) == 1 for f in fixtures))


def expand_full_table(result, case, winner, args, started):
    n, m, bits, radius = case["n"], case["m"], case["bits"], case["radius"]
    matrix = base.joined(case["blocks"])
    cap = int(case["zero_discrepancy_budget"]["J_cap"])
    table = dict(n=n, m=m, bits=bits, radius=radius, slots=[], case_index=result["cases"].index(case))
    result["full_tables"].append(table)
    for indices in itertools.combinations(range(n), 3):
        for level in range(bits):
            certificate = make_certificate(matrix, 3, base.zero_baseline(n, 3*m, 3, indices, level, 1 << bits),
                                           indices, level, bits, radius)
            if list(indices) == winner["candidate"]["indices"] and level == winner["candidate"]["level"]:
                certificate = winner["candidate"]
            if int(certificate["bound"]["J"]) <= cap:
                entry = dict(status="existing_certificate_fits", worker_started=False)
            elif time.monotonic()-started >= args.global_seconds:
                entry = dict(status="global_deadline_unstarted", worker_started=False)
            else:
                seconds = min(args.query_seconds, args.global_seconds-(time.monotonic()-started))
                entry = dict(query_limit=str(cap), requested_degree=winner["requested_degree"],
                             effective_degree=effective_degree(winner["requested_degree"], radius, cap))
                entry.update(attempt_search(matrix, bits, radius, winner["requested_degree"], indices, level,
                                            cap, certificate, seconds, args.coefficient_limit))
                accept_model(entry, matrix, case, case["seed"]+40000000+10000*level+sum(1 << i for i in indices))
                certificate = entry.get("candidate", certificate)
            independent_verify(certificate, matrix, bits)
            value = base.fixture(matrix, certificate, bits, case["seed"]+50000000+10000*level+sum(1 << i for i in indices))
            base.verify_fixture(value, certificate, matrix, bits)
            table["slots"].append(dict(indices=list(indices), level=level, selected=certificate,
                                       attempt=entry, fixtures=[value]))
            result["summary"] = summarize(result)
            base.atomic_write(args.output, result)
    table["expected_slots"] = math.comb(n, 3)*bits
    assert len(table["slots"]) == table["expected_slots"]
    maximum = max(int(slot["selected"]["bound"]["J"]) for slot in table["slots"])
    table["budget"] = budget(n, bits, radius, maximum)
    table["all_slots_certified"] = True
    table["all_queries_finished"] = all(slot["attempt"]["status"] in ("sat", "unsat", "existing_certificate_fits", "nonzero_error_floor") for slot in table["slots"])


def runner_checks():
    before = {process.pid for process in multiprocessing.active_children()}
    assert base.bounded_call(base.runner_fixture, ("success",), 1)["status"] == "fixture_success"
    assert base.bounded_call(base.runner_fixture, ("timeout",), 0.02)["status"] == "wall_timeout"
    assert base.bounded_call(base.runner_fixture, ("no_result",), 1)["status"] == "worker_no_result"
    assert {process.pid for process in multiprocessing.active_children()} == before
    seed, blocks = base.case_masks(3, 1, 3)
    matrix = base.joined(blocks)
    certificate = make_certificate(matrix, 3, base.zero_baseline(3, 3, 3, (0, 1, 2), 2, 8), (0, 1, 2), 2, 3, 1)
    case = dict(n=3, m=1, bits=3, seed=seed, blocks=blocks, radius=1, attempts=[],
                baseline=dict(certificate=certificate, fixtures=[]), zero_discrepancy_budget=budget(3, 3, 1, 0))
    result = dict(cases=[case], full_tables=[])
    with tempfile.TemporaryDirectory(prefix="fhe-bounded-error-runner-") as directory:
        args = SimpleNamespace(output=Path(directory)/"checkpoint.json", global_seconds=0,
                               query_seconds=1, coefficient_limit=600)
        expand_full_table(result, case, dict(candidate=certificate, requested_degree=4), args, time.monotonic())
        table = result["full_tables"][0]
        assert table["all_slots_certified"] and len(table["slots"]) == table["expected_slots"] == 3
        assert all(slot["attempt"]["status"] == "global_deadline_unstarted" for slot in table["slots"])
        assert not table["all_queries_finished"] and not table["budget"]["strict_budget"]
    return dict(worker_lifecycle_fixtures=3, deadline_full_table_slots=3)


def study(args):
    started = time.monotonic()
    result = dict(version=VERSION, scope="Finite bounded-error compiler exploration; not a security theorem",
                  config=dict(query_seconds=args.query_seconds, global_seconds=args.global_seconds,
                              coefficient_limit=args.coefficient_limit, quick=args.quick,
                              conservative_budget_multiplier=4),
                  provenance=dict(script_sha256=sha256(Path(__file__)), old_script_sha256=OLD_SCRIPT_SHA,
                                  old_artifact_sha256=OLD_ARTIFACT_SHA),
                  dependencies=dict(generation="optional Z3 4.13.3, existing isolated installation",
                                    replay="Python standard library"),
                  self_checks=self_checks(), regression=regression_checks(), runner_checks=runner_checks(),
                  solver_fixture=solver_check(), cases=[], full_tables=[], status="running",
                  proved_family_success=False, proved_polynomial_time_generator=False, production_Lean_changed=False)
    configurations = CONFIGURATIONS[:1] if args.quick else CONFIGURATIONS
    for n, m, bits in configurations:
        seed, blocks = base.case_masks(n, m, bits)
        radius, matrix = base.family_radius(bits), base.joined(blocks)
        baseline = make_certificate(matrix, 3, base.zero_baseline(n, 3*m, 3, (0, 1, 2), bits-1, 1 << bits),
                                    (0, 1, 2), bits-1, bits, radius)
        independent_verify(baseline, matrix, bits)
        value = base.fixture(matrix, baseline, bits, seed+20000000)
        base.verify_fixture(value, baseline, matrix, bits)
        gate = budget(n, bits, radius, 0)
        assert radius <= int(gate["J_cap"]) < base.class_lower_bound(radius, bits-1)
        result["cases"].append(dict(n=n, m=m, bits=bits, seed=seed, blocks=blocks, radius=radius,
                                    zero_discrepancy_budget=gate, old_class_lower_bound=str(base.class_lower_bound(radius, bits-1)),
                                    relaxed_class_lower_bound=str(class_lower_bound(radius, bits-1)),
                                    baseline=dict(certificate=baseline, fixtures=[value]), attempts=[]))
    cache = {}
    for requested_degree in DEGREES:
        for case_index, case in enumerate(result["cases"]):
            n, m, bits, radius = case["n"], case["m"], case["bits"], case["radius"]
            matrix = base.joined(case["blocks"])
            prior_models = [entry["candidate"] for entry in case["attempts"] if "candidate" in entry]
            warm = min(prior_models, key=lambda c: int(c["bound"]["J"])) if prior_models else case["baseline"]["certificate"]
            limit = min(int(case["zero_discrepancy_budget"]["J_cap"]), int(warm["bound"]["J"])-1)
            degree = effective_degree(requested_degree, radius, limit)
            entry = dict(requested_degree=requested_degree, effective_degree=degree, query_limit=str(limit),
                         indices=[0, 1, 2], level=bits-1)
            key = (case_index, degree, limit)
            remaining = args.global_seconds-(time.monotonic()-started)
            if key in cache:
                reference = cache[key]
                original = case["attempts"][reference]
                entry.update(status="equivalent_query_reused", worker_started=False,
                             reference_attempt=reference, referenced_status=original["status"],
                             reason="Budget forces body degree <=1; quadratic secret degree makes total degree <=3")
            elif remaining <= 0:
                entry.update(status="global_deadline_unstarted", worker_started=False)
            else:
                entry.update(attempt_search(matrix, bits, radius, requested_degree, (0, 1, 2), bits-1,
                                            limit, warm, min(args.query_seconds, remaining), args.coefficient_limit))
                if entry.get("worker_started"):
                    cache[key] = len(case["attempts"])
                accept_model(entry, matrix, case, case["seed"]+30000000+100000*requested_degree)
            case["attempts"].append(entry)
            result["summary"] = summarize(result)
            result["elapsed_seconds"] = round(time.monotonic()-started, 3)
            base.atomic_write(args.output, result)
            print(json.dumps(dict(event="screen", n=n, m=m, bits=bits, degree=requested_degree,
                                  effective_degree=degree, limit=str(limit), status=entry["status"],
                                  candidate_J=entry.get("candidate", {}).get("bound", {}).get("J"))), flush=True)
    winners = [(case, min((entry for entry in case["attempts"] if "candidate" in entry),
                          key=lambda e: int(e["candidate"]["bound"]["J"])))
               for case in result["cases"] if any("candidate" in entry for entry in case["attempts"])]
    if winners:
        expand_full_table(result, *winners[0], args, started)
    result["status"] = "screen_complete"
    result["advancement"] = dict(screen_budget_candidate=bool(winners),
                                 finite_complete_table_pass=any(t["budget"]["strict_budget"] for t in result["full_tables"]),
                                 production_gate_satisfied=False,
                                 reason="Family probability, polynomial-time generation and complete joint ordinary-LWE integration remain unproved")
    result["summary"] = summarize(result)
    result["elapsed_seconds"] = round(time.monotonic()-started, 3)
    base.atomic_write(args.output, result)
    print(json.dumps(result["summary"]), flush=True)


def replay(path):
    result = json.loads(path.read_text())
    assert result["version"] == VERSION and result["status"] == "screen_complete"
    assert result["provenance"] == dict(script_sha256=sha256(Path(__file__)), old_script_sha256=OLD_SCRIPT_SHA,
                                        old_artifact_sha256=OLD_ARTIFACT_SHA)
    assert result["config"]["conservative_budget_multiplier"] == 4
    assert result["self_checks"] == self_checks()
    assert result["regression"] == regression_checks()
    assert result["runner_checks"] == runner_checks()
    matrix, _ = structured_fixture()
    independent_verify(result["solver_fixture"]["candidate"], matrix, 8)
    reconstruct_program(result["solver_fixture"]["candidate"], matrix, 8)
    assert result["solver_fixture"]["candidate"]["bound"]["J"] == "2"
    assert lower_order_nonzero(result["solver_fixture"]["candidate"])
    assert not result["proved_family_success"] and not result["proved_polynomial_time_generator"]
    assert not result["production_Lean_changed"]
    configs = CONFIGURATIONS[:1] if result["config"]["quick"] else CONFIGURATIONS
    assert [(c["n"], c["m"], c["bits"]) for c in result["cases"]] == list(configs)
    checked = phases = 0

    def verify_item(cert, fixtures, case):
        nonlocal checked, phases
        matrix = base.joined(case["blocks"])
        independent_verify(cert, matrix, case["bits"])
        reconstruct_program(cert, matrix, case["bits"])
        checked += 1
        for value in fixtures:
            assert value == base.fixture(matrix, cert, case["bits"], value["seed"])
            base.verify_fixture(value, cert, matrix, case["bits"])
            phases += 1

    def verify_entry(entry, case):
        if "candidate" in entry:
            cert = entry["candidate"]
            assert cert["radius"] == case["radius"]
            assert cert["degree"] == entry["effective_degree"] and lower_order_nonzero(cert)
            assert int(cert["bound"]["J"]) <= int(entry["query_limit"])
            assert len(entry["fixtures"]) == 4
            verify_item(cert, entry["fixtures"], case)
            verify_budget(entry["budget"], case["n"], case["bits"], case["radius"], int(cert["bound"]["J"]))
            assert entry["budget"]["strict_budget"]

    winner_cases = []
    for case_index, case in enumerate(result["cases"]):
        n, m, bits, radius = case["n"], case["m"], case["bits"], case["radius"]
        seed, blocks = base.case_masks(n, m, bits)
        assert case["seed"] == seed and case["blocks"] == blocks and radius == base.family_radius(bits)
        gate = case["zero_discrepancy_budget"]
        verify_budget(gate, n, bits, radius, 0)
        assert case["old_class_lower_bound"] == str(base.class_lower_bound(radius, bits-1))
        assert case["relaxed_class_lower_bound"] == str(class_lower_bound(radius, bits-1))
        assert radius <= int(gate["J_cap"]) < int(case["old_class_lower_bound"])
        baseline = case["baseline"]["certificate"]
        assert baseline["program"] == base.zero_baseline(n, 3*m, 3, (0, 1, 2), bits-1, 1 << bits)
        assert baseline["degree"] == 3 and baseline["level"] == bits-1 and baseline["indices"] == [0, 1, 2]
        assert baseline["radius"] == radius
        verify_item(baseline, case["baseline"]["fixtures"], case)
        assert [e["requested_degree"] for e in case["attempts"]] == list(DEGREES)
        incumbent = int(baseline["bound"]["J"])
        seen_queries = {}
        for j, entry in enumerate(case["attempts"]):
            limit = min(int(gate["J_cap"]), incumbent-1)
            assert int(entry["query_limit"]) == limit
            assert entry["effective_degree"] == effective_degree(entry["requested_degree"], radius, limit)
            assert entry["indices"] == [0, 1, 2] and entry["level"] == bits-1
            key = (entry["effective_degree"], limit)
            if entry["status"] == "equivalent_query_reused":
                assert key in seen_queries and entry["reference_attempt"] == seen_queries[key]
                previous = case["attempts"][entry["reference_attempt"]]
                assert entry["referenced_status"] == previous["status"] and previous["worker_started"]
                assert entry["effective_degree"] == 3 and maximum_error_order(radius, limit, 4) == 1
                assert not entry["worker_started"] and "candidate" not in entry
            if entry.get("worker_started"):
                assert key not in seen_queries
                seen_queries[key] = j
            verify_entry(entry, case)
            if "candidate" in entry:
                assert entry["candidate"]["indices"] == [0, 1, 2] and entry["candidate"]["level"] == bits-1
                incumbent = int(entry["candidate"]["bound"]["J"])
        if any("candidate" in e for e in case["attempts"]):
            winner_cases.append(case_index)
    assert len(result["full_tables"]) == int(bool(winner_cases))
    for table in result["full_tables"]:
        assert table["case_index"] == winner_cases[0]
        case = result["cases"][table["case_index"]]
        assert (table["n"], table["m"], table["bits"], table["radius"]) == (case["n"], case["m"], case["bits"], case["radius"])
        expected = [(list(indices), level) for indices in itertools.combinations(range(case["n"]), 3) for level in range(case["bits"])]
        assert [(s["indices"], s["level"]) for s in table["slots"]] == expected
        assert table["expected_slots"] == len(expected) and table["all_slots_certified"]
        for slot in table["slots"]:
            cert = slot["selected"]
            assert cert["indices"] == slot["indices"] and cert["level"] == slot["level"] and cert["radius"] == case["radius"]
            verify_entry(slot["attempt"], case)
            verify_item(cert, slot["fixtures"], case)
            if "candidate" in slot["attempt"]:
                assert cert == slot["attempt"]["candidate"]
            if slot["attempt"]["status"] == "existing_certificate_fits":
                assert int(cert["bound"]["J"]) <= int(case["zero_discrepancy_budget"]["J_cap"])
        maximum = max(int(s["selected"]["bound"]["J"]) for s in table["slots"])
        verify_budget(table["budget"], case["n"], case["bits"], case["radius"], maximum)
        assert table["all_queries_finished"] == all(s["attempt"]["status"] in ("sat", "unsat", "existing_certificate_fits", "nonzero_error_floor") for s in table["slots"])
    assert result["summary"] == summarize(result)
    assert result["advancement"] == dict(screen_budget_candidate=bool(winner_cases),
                                          finite_complete_table_pass=any(t["budget"]["strict_budget"] for t in result["full_tables"]),
                                          production_gate_satisfied=False,
                                          reason="Family probability, polynomial-time generation and complete joint ordinary-LWE integration remain unproved")
    print(json.dumps(dict(replayed_main_certificates=checked, replayed_main_source_phases=phases,
                          regression=result["regression"], summary=result["summary"])), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--verify-runner", action="store_true")
    mode.add_argument("--verify-solver", action="store_true")
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--query-seconds", type=float, default=30)
    parser.add_argument("--global-seconds", type=float, default=1200)
    parser.add_argument("--coefficient-limit", type=int, default=600)
    args = parser.parse_args()
    assert args.query_seconds > 0 and args.global_seconds > 0 and args.coefficient_limit > 0
    if args.self_test:
        print(json.dumps(dict(self_checks=self_checks(), regression=regression_checks())), flush=True)
    elif args.verify_runner:
        print(json.dumps(runner_checks()), flush=True)
    elif args.verify_solver:
        print(json.dumps(solver_check()), flush=True)
    elif args.verify_existing:
        replay(args.verify_existing)
    else:
        study(args)


if __name__ == "__main__":
    main()
