#!/usr/bin/env python3
"""Exact Boolean polynomial compiler exploration; not an FHE security proof.

The mask-only builder searches coefficients of P(s,y), quadratic in s and
of bounded total degree. Runtime compilation evaluates only y-polynomials.
Independent replay uses Boolean truth tables and univariate polynomial
convolution, not the builder's Boolean symbolic substitution. Z3 is optional
for replay. Oracle keys/errors are validation witnesses, never builder inputs.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
import math
import multiprocessing
from pathlib import Path
import random
import tempfile
import time
from types import SimpleNamespace


VERSION = 1
ROOT = Path(__file__).resolve().parent.parent
CONFIGURATIONS = ((3, 1), (4, 1), (6, 1), (3, 2))
BITS = (12, 24)
DEGREES = (3, 4, 5)


def centered(value, q):
    return (int(value)+q//2) % q-q//2


def ceil_fraction(value):
    return -(-value.numerator//value.denominator)


def exponents(width, maximum):
    """Canonical total-degree order, including the constant monomial."""
    for degree in range(maximum+1):
        for indices in itertools.combinations_with_replacement(range(width), degree):
            powers = [0]*width
            for i in indices:
                powers[i] += 1
            yield tuple(powers)


def supports(n, maximum):
    return [sum(1 << i for i in subset) for degree in range(min(n, maximum)+1)
            for subset in itertools.combinations(range(n), degree)]


def grammar(n, width, degree):
    return [(mask, powers) for mask in supports(n, 2)
            for powers in exponents(width, degree-mask.bit_count())]


def joined(blocks):
    return [sum((block[i] for block in blocks), []) for i in range(len(blocks[0]))]


def case_masks(n, m, bits):
    seed = 20261020+100000*n+1000*m+bits
    rng = random.Random(seed)
    return seed, [[[rng.randrange(1 << bits) for _ in range(m)] for _ in range(n)] for _ in range(3)]


def family_radius(bits):
    return 1 << (math.isqrt(bits-1)+1)


def expansion_columns(matrix, degree, q):
    """Expand (A^T*s+e)^nu with s_i^2=s_i, without derivatives/division."""
    n, width = len(matrix), len(matrix[0])
    zero = (0,)*width
    expanded = {zero: {(0, zero): 1}}
    powers = list(exponents(width, degree))
    for nu in powers[1:]:
        column = next(i for i, value in enumerate(nu) if value)
        earlier = list(nu)
        earlier[column] -= 1
        output = defaultdict(int)
        for (mask, beta), coefficient in expanded[tuple(earlier)].items():
            error_power = list(beta)
            error_power[column] += 1
            output[(mask, tuple(error_power))] += coefficient
            for i, row in enumerate(matrix):
                output[(mask | (1 << i), beta)] += coefficient*row[column]
        expanded[nu] = {key: value % q for key, value in output.items() if value % q}
    columns = []
    for mask, nu in grammar(n, width, degree):
        output = defaultdict(int)
        for (inner, beta), value in expanded[nu].items():
            output[(mask | inner, beta)] += value
        columns.append({key: value % q for key, value in output.items() if value % q})
    return columns


def program_terms(program, n, width, degree, q):
    allowed = set(grammar(n, width, degree))
    values = {}
    for term in program:
        key = (term[0], tuple(term[1]))
        assert key in allowed and key not in values
        coefficient = term[2]
        assert isinstance(coefficient, int) and centered(coefficient, q) == coefficient and coefficient != 0
        values[key] = coefficient
    return values


def serialize_program(values, n, width, degree, q):
    return [[mask, list(nu), centered(values.get((mask, nu), 0), q)]
            for mask, nu in grammar(n, width, degree) if values.get((mask, nu), 0) % q]


def zero_baseline(n, width, degree, indices, level, q):
    weight = 1 << level
    quotient = (centered(-weight, q)+4)//8
    zero = (0,)*width
    values = {(0, zero): -quotient}
    for i in indices:
        values[(1 << i, zero)] = 2*quotient
    for i, j in itertools.combinations(indices, 2):
        values[((1 << i) | (1 << j), zero)] = -4*quotient
    return serialize_program(values, n, width, degree, q)


def tensor_program(matrix, tensor, q):
    """Known third-order cancellation fixture, allowing repeated source columns."""
    n, width = len(matrix), len(matrix[0])
    values = defaultdict(int)
    for positions, coefficient in tensor:
        nu = [0]*width
        for position in positions:
            nu[position] += 1
        values[(0, tuple(nu))] += coefficient
        for removed in range(3):
            nu = [0]*width
            for r in range(3):
                if r != removed:
                    nu[positions[r]] += 1
            for i in range(n):
                values[(1 << i, tuple(nu))] -= coefficient*matrix[i][positions[removed]]
        for first, second in itertools.combinations(range(3), 2):
            last = next(r for r in range(3) if r not in (first, second))
            nu = tuple(int(column == positions[last]) for column in range(width))
            for i in range(n):
                for j in range(n):
                    values[((1 << i) | (1 << j), nu)] += coefficient*matrix[i][positions[first]]*matrix[j][positions[second]]
    return serialize_program(values, n, width, 3, q)


def normal_form(matrix, degree, program, indices, level, q):
    n, width = len(matrix), len(matrix[0])
    values = program_terms(program, n, width, degree, q)
    result = defaultdict(int)
    for key, column in zip(grammar(n, width, degree), expansion_columns(matrix, degree, q)):
        coefficient = values.get(key, 0)
        if coefficient:
            for output, factor in column.items():
                result[output] += coefficient*factor
    result[(sum(1 << i for i in indices), (0,)*width)] -= 1 << level
    return {key: centered(value, q) for key, value in result.items() if value % q}


def bound_from_residual(residual, n, degree, radius):
    """Integer lift of the Boolean Walsh bound, plus supported error powers."""
    zero_order = {mask: coefficient for (mask, beta), coefficient in residual.items() if not any(beta)}
    walsh = {mask: sum((1 << (degree-source.bit_count()))*value
                       for source, value in zero_order.items() if mask & source == mask)
             for mask in supports(n, degree)}
    layers = defaultdict(int)
    for (mask, beta), coefficient in residual.items():
        order = sum(beta)
        if order:
            assert order >= 3, (mask, beta, coefficient)
            layers[order] += abs(coefficient)
    scale = 1 << degree
    numerator = sum(map(abs, walsh.values()))+scale*sum(radius**order*value for order, value in layers.items())
    return dict(walsh_scaled=[[mask, value] for mask, value in walsh.items() if value],
                error_l1_by_order=[[order, value] for order, value in sorted(layers.items())],
                scale=scale, numerator=str(numerator), J=str((numerator+scale-1)//scale))


def make_certificate(matrix, degree, program, indices, level, q, radius):
    residual = normal_form(matrix, degree, program, indices, level, q)
    bound = bound_from_residual(residual, len(matrix), degree, radius)
    return dict(degree=degree, indices=list(indices), level=level, radius=radius, program=program,
                residual=[[mask, list(beta), value] for (mask, beta), value in sorted(residual.items())],
                bound=bound)


def compile_control(program, n, bodies, q):
    """Actual public compiler. All T,c,b entries are returned; no secret input."""
    matrix, linear, body = [[0]*n for _ in range(n)], [0]*n, 0
    for mask, powers, coefficient in program:
        value = coefficient*math.prod(pow(y, exponent, q) for y, exponent in zip(bodies, powers)) % q
        indices = [i for i in range(n) if mask & (1 << i)]
        if not indices:
            body += value
        elif len(indices) == 1:
            linear[indices[0]] += value
        else:
            i, j = indices
            matrix[i][j] -= value
    return [[[value % q for value in row] for row in matrix], [value % q for value in linear], body % q]


def public_zero(matrix, mask, outputs, body, q):
    return [matrix, [(y-a) % q for y, a in zip(outputs, mask)], body % q]


def compile_view(table, program, n, bodies, zero, q):
    control = compile_control(program, n, bodies, q)
    control = [[[(a+b) % q for a, b in zip(row, other)] for row, other in zip(control[0], zero[0])],
               [(a+b) % q for a, b in zip(control[1], zero[1])], (control[2]+zero[2]) % q]
    return dict(public_table=table, control=control)


def budget(n, bits, radius, J):
    rows = n*n+n+1
    growth = rows*bits
    lookup = 1 << (8*rows-1).bit_length()
    complete = J+(n+1)*radius
    factor = lookup**2*rows*growth*(growth+1)**2
    return dict(control_bound=str(complete), refresh_factor=str(factor),
                refresh_bound=str(factor*complete), strict_budget=factor*complete < 1 << bits)


def class_lower_bound(radius, level):
    """Lower bound on THIS supported certificate, not every possible sampler.

    A nonzero error coefficient contributes at least E^3. Otherwise P(s,y)
    is independent of y in the Boolean polynomial ring (translate e by -x).
    Setting y=0 then leaves a quadratic, whose cubic discrepancy has Walsh
    coefficient -w/8. Hence ceil(J) >= min(E^3, ceil(w/8)).
    """
    return min(radius**3, ((1 << level)+7)//8)


def attempt_search(matrix, bits, radius, degree, indices, level, incumbent, seconds):
    lower = class_lower_bound(radius, level)
    assert int(incumbent["bound"]["J"]) >= lower
    if int(incumbent["bound"]["J"]) == lower:
        return dict(status="certificate_lower_bound", certified_lower_bound=str(lower),
                    reason="No strict improvement of this integer supported certificate is possible")
    return bounded_call(solve_worker, (matrix, bits, radius, degree, indices, level, incumbent, seconds), seconds)


def univariate_multiply(first, second, q):
    result = [0]*(len(first)+len(second)-1)
    for i, x in enumerate(first):
        for j, y in enumerate(second):
            result[i+j] = (result[i+j]+x*y) % q
    return result


def independent_verify(certificate, matrix, bits):
    """Truth-table Hasse coefficients, then Boolean Mobius inversion.

    At each Boolean key expand each source factor as the UNIVARIATE
    (known noiseless scalar + formal error)^power; convolve the multivariate
    error coefficients. This does not call expansion_columns/normal_form.
    """
    n, width, degree = len(matrix), len(matrix[0]), certificate["degree"]
    q, radius = 1 << bits, certificate["radius"]
    program_terms(certificate["program"], n, width, degree, q)
    indices, level = certificate["indices"], certificate["level"]
    assert len(indices) == 3 and len(set(indices)) == 3 and all(0 <= i < n for i in indices)
    assert 0 <= level < bits and radius >= 1
    evaluations = {}
    for key in range(1 << n):
        secret = [(key >> i) & 1 for i in range(n)]
        x = [sum(secret[i]*matrix[i][j] for i in range(n)) % q for j in range(width)]
        values = defaultdict(int)
        for mask, powers, coefficient in certificate["program"]:
            if mask & key != mask:
                continue
            one_variable = []
            for value, power in zip(x, powers):
                poly = [1]
                for _ in range(power):
                    poly = univariate_multiply(poly, [value, 1], q)
                one_variable.append(poly)
            for beta in itertools.product(*(range(len(poly)) for poly in one_variable)):
                factor = coefficient
                for poly, exponent in zip(one_variable, beta):
                    factor *= poly[exponent]
                values[beta] += factor
        values[(0,)*width] -= (1 << level)*math.prod(secret[i] for i in indices)
        evaluations[key] = {beta: value % q for beta, value in values.items() if value % q}
    residual = {}
    for beta in exponents(width, degree):
        values = [evaluations[key].get(beta, 0) for key in range(1 << n)]
        for i in range(n):
            for key in range(1 << n):
                if key & (1 << i):
                    values[key] = (values[key]-values[key ^ (1 << i)]) % q
        for mask, value in enumerate(values):
            if value:
                assert mask.bit_count()+sum(beta) <= degree
                assert sum(beta) not in (1, 2), (mask, beta, value)
                residual[(mask, beta)] = centered(value, q)
    recorded = {(mask, tuple(beta)): value for mask, beta, value in certificate["residual"]}
    assert len(recorded) == len(certificate["residual"]) and recorded == residual
    # Independent rational Walsh transform by averaging the zero-error truth table.
    zero = (0,)*width
    values = [sum(coefficient for (mask, beta), coefficient in residual.items()
                  if beta == zero and mask & key == mask) for key in range(1 << n)]
    walsh = {}
    for mask in range(1 << n):
        coefficient = sum(value*(-1)**((mask & ~key).bit_count()) for key, value in enumerate(values))
        coefficient = Fraction(coefficient, 1 << n)
        if coefficient:
            assert mask.bit_count() <= degree
            walsh[mask] = coefficient
    layers = defaultdict(int)
    for (mask, beta), coefficient in residual.items():
        if sum(beta):
            layers[sum(beta)] += abs(coefficient)
    exact = sum(map(abs, walsh.values()))+sum(radius**order*value for order, value in layers.items())
    scale = 1 << degree
    assert all((value*scale).denominator == 1 for value in walsh.values())
    expected = dict(walsh_scaled=[[mask, int(value*scale)] for mask, value in
                                 sorted(walsh.items(), key=lambda pair: (pair[0].bit_count(), tuple(i for i in range(n) if pair[0] & (1 << i))))],
                    error_l1_by_order=[[order, value] for order, value in sorted(layers.items())],
                    scale=scale, numerator=str(int(exact*scale)), J=str(ceil_fraction(exact)))
    assert certificate["bound"] == expected
    return residual


def check_residual_reconstruction(certificate, matrix, bits):
    """Round-trip the new solver coordinates on independently checked fixtures."""
    q, degree = 1 << bits, certificate["degree"]
    n, width = len(matrix), len(matrix[0])
    inverse = dict(zip(grammar(n, width, degree), expansion_columns(
        [[-value for value in row] for row in matrix], degree, q)))
    output = defaultdict(int)
    output[(sum(1 << i for i in certificate["indices"]), (0,)*width)] = 1 << certificate["level"]
    for mask, beta, coefficient in certificate["residual"]:
        key = (mask, tuple(beta))
        column = inverse[key] if any(beta) else {key: 1}
        for target, factor in column.items():
            output[target] += coefficient*factor
    assert all(value % q == 0 for (mask, _), value in output.items() if mask.bit_count() > 2)
    values = {key: value for key, value in output.items() if key[0].bit_count() <= 2}
    assert serialize_program(values, n, width, degree, q) == certificate["program"]


def solve_worker(connection, matrix, bits, radius, degree, indices, level, baseline, seconds):
    started = time.monotonic()
    try:
        import z3
        q, n, width = 1 << bits, len(matrix), len(matrix[0])
        keys = grammar(n, width, degree)
        # Equivalent residual parameterization. R has no error orders 1 or 2.
        # Invert e=y-A^T*s and require target+R(s,y-A^T*s) to be quadratic
        # in s. Thus no source-error cancellation constraints are lost.
        columns = expansion_columns([[-value for value in row] for row in matrix], degree, q)
        rows = defaultdict(dict)
        zero = (0,)*width
        residual_keys = [(mask, zero) for mask in supports(n, degree)]
        residual_keys += [key for key in keys if sum(key[1]) >= 3]
        inverse = {key: column for key, column in zip(keys, columns) if sum(key[1]) >= 3}
        for key in residual_keys:
            column = inverse.get(key, {key: 1})
            for output, coefficient in column.items():
                rows[output][key] = centered(coefficient, q)
        target_key = (sum(1 << i for i in indices), zero)
        rows.setdefault(target_key, {})
        optimizer = z3.Optimize()
        residuals = {key: z3.Int(f"r_{j}") for j, key in enumerate(residual_keys)}
        warm = {(mask, tuple(beta)): coefficient for mask, beta, coefficient in baseline["residual"]}
        for key, value in residuals.items():
            optimizer.add(value >= -q//2, value < q//2)
            optimizer.set_initial_value(value, warm.get(key, 0))
        constraints = 0
        for number, (key, coefficients) in enumerate(sorted(rows.items())):
            if key[0].bit_count() > 2:
                expression = z3.Sum([coefficient*residuals[source] for source, coefficient in coefficients.items()])
                target = (1 << level) if key == target_key else 0
                optimizer.add(expression+target == q*z3.Int(f"z_{number}"))
                constraints += 1
        absolute_values = []
        def absolute(expression):
            value = z3.Int(f"abs_{len(absolute_values)}")
            optimizer.add(value >= expression, value >= -expression)
            absolute_values.append(value)
            return value
        walsh = []
        for mask in supports(n, degree):
            expression = z3.Sum([(1 << (degree-source.bit_count()))*value
                                 for (source, beta), value in residuals.items()
                                 if beta == zero and source & mask == mask])
            walsh.append(absolute(expression))
        terms = list(walsh)
        for (mask, beta), value in residuals.items():
            order = sum(beta)
            if order:
                terms.append((1 << degree)*radius**order*absolute(value))
        objective = z3.Sum(terms)
        # Strict improvement in the INTEGER supported bound, not just a rational score.
        threshold = int(baseline["bound"]["J"])
        optimizer.add(objective <= (1 << degree)*(threshold-1))
        optimizer.minimize(objective)
        built = time.monotonic()
        remaining = seconds-(built-started)-0.5
        if remaining <= 0:
            connection.send(dict(status="build_deadline", variables=len(residuals), constraints=constraints,
                                 program_coefficients=len(keys), encoding="residual"))
            return
        optimizer.set(timeout=max(1, int(1000*remaining)))
        status = optimizer.check()
        record = dict(status=str(status), variables=len(residuals), constraints=constraints,
                      program_coefficients=len(keys), encoding="residual",
                      build_seconds=round(built-started, 3),
                      solver_version=z3.get_version_string())
        if status == z3.unknown:
            record["reason"] = optimizer.reason_unknown()
        try:
            model = optimizer.model()
            concrete = {key: model.eval(value, model_completion=True).as_long() for key, value in residuals.items()}
            values = {key: ((1 << level) if key == target_key else 0)+
                           sum(coefficient*concrete[source] for source, coefficient in coefficients.items())
                      for key, coefficients in rows.items() if key[0].bit_count() <= 2}
            program = serialize_program(values, n, width, degree, q)
            candidate = make_certificate(matrix, degree, program, indices, level, q, radius)
            assert {(mask, tuple(beta)): coefficient for mask, beta, coefficient in candidate["residual"]} == {
                key: value for key, value in concrete.items() if value}
            assert int(candidate["bound"]["J"]) < threshold
            record["candidate"] = candidate
        except Exception as error:
            record["model_unavailable_or_rejected"] = type(error).__name__+": "+str(error)[:200]
        record["elapsed_seconds"] = round(time.monotonic()-started, 3)
        connection.send(record)
    except Exception as error:
        connection.send(dict(status="worker_error", error=type(error).__name__+": "+str(error)[:300]))
    finally:
        connection.close()


def bounded_call(target, arguments, seconds):
    context = multiprocessing.get_context("fork")
    receiver, sender = context.Pipe(duplex=False)
    process = context.Process(target=target, args=(sender, *arguments))
    process.start()
    sender.close()
    started = time.monotonic()
    try:
        if receiver.poll(seconds):
            try:
                result = receiver.recv()
            except EOFError:
                result = dict(status="worker_no_result")
        else:
            result = dict(status="wall_timeout")
        process.join(timeout=0.1)
        result["wall_seconds"] = round(time.monotonic()-started, 3)
        return result
    finally:
        if process.is_alive():
            process.kill()
        process.join()
        receiver.close()


def fixture(matrix, certificate, bits, seed):
    n, width, radius, q = len(matrix), len(matrix[0]), certificate["radius"], 1 << bits
    rng = random.Random(seed)
    secret = [rng.randrange(2) for _ in range(n)]
    errors = [rng.randint(-radius, radius) for _ in range(width)]
    bodies = [(sum(secret[i]*matrix[i][j] for i in range(n))+errors[j]) % q for j in range(width)]
    def zero_source():
        a = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
        mask = [rng.randrange(q) for _ in range(n)]
        noise = [rng.randint(-radius, radius) for _ in range(n+1)]
        y = [(sum(secret[i]*a[i][j] for i in range(n))+noise[j]) % q for j in range(n)]
        body = (sum(x*y for x, y in zip(secret, mask))+noise[-1]) % q
        return public_zero(a, mask, y, body, q), dict(matrix=a, mask=mask, outputs=y, body=body, errors=noise)
    zero, zero_witness = zero_source()
    table_pairs = [zero_source() for _ in range(3)]
    table = [pair[0] for pair in table_pairs]
    result = compile_view(table, certificate["program"], n, bodies, zero, q)
    assert result["public_table"] is table
    t, c, b = result["control"]
    phase = b+sum(x*y for x, y in zip(secret, c))-sum(secret[i]*t[i][j]*secret[j] for i in range(n) for j in range(n))
    target = (1 << certificate["level"])*math.prod(secret[i] for i in certificate["indices"])
    phase_error = centered(phase-target, q)
    compatible = []
    for key in itertools.product((0, 1), repeat=n):
        if all(abs(centered(y-sum(key[i]*matrix[i][j] for i in range(n)), q)) <= radius
               for j, y in enumerate(bodies)):
            compatible.append(list(key))
    return dict(seed=seed, secret=secret, errors=errors, bodies=bodies, zero_source=zero_witness,
                public_table=table, public_table_sources=[pair[1] for pair in table_pairs],
                output=result, compatible_binary_keys=compatible,
                actual_phase_error=phase_error, strict_decoding_margin=2*abs(phase_error) < (1 << certificate["level"]),
                recovery_scope="exhaustive finite toy-key enumeration, not a polynomial-time family attack")


def verify_fixture(value, certificate, matrix, bits):
    n, q, radius = len(matrix), 1 << bits, certificate["radius"]
    secret, errors, bodies = value["secret"], value["errors"], value["bodies"]
    assert len(secret) == n and all(x in (0, 1) for x in secret)
    assert all(abs(e) <= radius for e in errors)
    assert bodies == [(sum(secret[i]*matrix[i][j] for i in range(n))+errors[j]) % q for j in range(len(bodies))]
    witness = value["zero_source"]
    assert all(abs(e) <= radius for e in witness["errors"])
    assert witness["outputs"] == [(sum(secret[i]*witness["matrix"][i][j] for i in range(n))+
                                     witness["errors"][j]) % q for j in range(n)]
    assert witness["body"] == (sum(x*y for x, y in zip(secret, witness["mask"]))+witness["errors"][-1]) % q
    assert len(value["public_table"]) == len(value["public_table_sources"]) == 3
    for column, source in zip(value["public_table"], value["public_table_sources"]):
        assert all(abs(e) <= radius for e in source["errors"])
        assert source["outputs"] == [(sum(secret[i]*source["matrix"][i][j] for i in range(n))+
                                        source["errors"][j]) % q for j in range(n)]
        assert source["body"] == (sum(x*y for x, y in zip(secret, source["mask"]))+source["errors"][-1]) % q
        assert column == [source["matrix"], [(y-a) % q for y, a in zip(source["outputs"], source["mask"])], source["body"]]
    # Reconstruct each coordinate directly, without calling the compiler.
    polynomial = defaultdict(int)
    for mask, powers, coefficient in certificate["program"]:
        monomial = coefficient
        for y, power in zip(bodies, powers):
            monomial *= y**power
        polynomial[mask] += monomial
    t = [[(witness["matrix"][i][j]-polynomial.get((1 << i) | (1 << j), 0)*int(i < j)) % q
          for j in range(n)] for i in range(n)]
    c = [(witness["outputs"][i]-witness["mask"][i]+polynomial.get(1 << i, 0)) % q for i in range(n)]
    b = (witness["body"]+polynomial.get(0, 0)) % q
    assert value["output"] == dict(public_table=value["public_table"], control=[t, c, b])
    phase = b+sum(x*y for x, y in zip(secret, c))-sum(secret[i]*t[i][j]*secret[j] for i in range(n) for j in range(n))
    target = (1 << certificate["level"])*math.prod(secret[i] for i in certificate["indices"])
    residual = 0
    for mask, beta, coefficient in certificate["residual"]:
        if all(secret[i] for i in range(n) if mask & (1 << i)):
            residual += coefficient*math.prod(e**power for e, power in zip(errors, beta))
    zero_error = witness["errors"][-1]+sum(x*y for x, y in zip(secret, witness["errors"][:-1]))
    assert (phase-target-residual-zero_error) % q == 0
    assert abs(centered(residual, q)) <= int(certificate["bound"]["J"])
    assert abs(centered(phase-target, q)) <= int(certificate["bound"]["J"])+(n+1)*radius
    assert value["actual_phase_error"] == centered(phase-target, q)
    assert value["strict_decoding_margin"] == (2*abs(centered(phase-target, q)) < (1 << certificate["level"]))
    compatible = [list(key) for key in itertools.product((0, 1), repeat=n)
                  if all(abs(centered(y-sum(key[i]*matrix[i][j] for i in range(n)), q)) <= radius
                         for j, y in enumerate(bodies))]
    assert value["compatible_binary_keys"] == compatible and secret in compatible


def identity_checks():
    counts = dict(quartic_identity=0, cubic_full_phase=0, corrupted_certificates_rejected=0,
                  quartic_certificates=0, full_view_fixtures=0, nonunit_checks=0,
                  dense_source_exhaustive_phases=0, residual_coordinate_roundtrips=0)
    # Quartic zero-message identity outside the constant-cubic-error class.
    for bits in range(1, 9):
        q = 1 << bits
        for s in (0, 1):
            for e in range(-8, 9):
                y = (s+e) % q
                assert (y**4+s*(-2*y**3+2*y-1)-2*s*e**3-e**4) % q == 0
                counts["quartic_identity"] += 1
    n, width, degree = 3, 3, 3
    matrix = [[int(i == j) for j in range(width)] for i in range(n)]
    terms = {(0, (1, 1, 1)): 1}
    for i in range(3):
        nu = tuple(int(j != i) for j in range(3))
        terms[(1 << i, nu)] = -1
    for i, j in itertools.combinations(range(3), 2):
        terms[((1 << i) | (1 << j), tuple(int(k not in (i, j)) for k in range(3)))] = 1
    for bits in (1, 3, 5):
        q = 1 << bits
        program = serialize_program(terms, n, width, degree, q)
        cert = make_certificate(matrix, degree, program, (0, 1, 2), 0, q, 1)
        independent_verify(cert, matrix, bits)
        check_residual_reconstruction(cert, matrix, bits)
        counts["residual_coordinate_roundtrips"] += 1
        for secret in itertools.product((0, 1), repeat=n):
            for errors in itertools.product((-1, 0, 1), repeat=width):
                bodies = [(s+e) % q for s, e in zip(secret, errors)]
                t, c, b = compile_control(program, n, bodies, q)
                phase = b+sum(s*x for s, x in zip(secret, c))-sum(secret[i]*t[i][j]*secret[j] for i in range(n) for j in range(n))
                assert phase % q == (math.prod(secret)+math.prod(errors)) % q
                counts["cubic_full_phase"] += 1
        for radius in (1, 3):
            cert = make_certificate(matrix, degree, program, (0, 1, 2), 0, q, radius)
            value = fixture(matrix, cert, bits, 20261023+bits+radius)
            verify_fixture(value, cert, matrix, bits)
            counts["full_view_fixtures"] += 1
        for fault in ("bound", "program", "residual"):
            broken = json.loads(json.dumps(cert))
            if fault == "bound":
                broken["bound"]["J"] = "999999"
            elif fault == "program":
                broken["program"][0][2] += 1
            else:
                broken["residual"].append([0, [0, 0, 0], 1])
            try:
                independent_verify(broken, matrix, bits)
            except AssertionError:
                counts["corrupted_certificates_rejected"] += 1
            else:
                raise AssertionError("accepted corrupt certificate")
    for bits in (1, 2, 3, 6):
        q = 1 << bits
        for factor in (1, 2, 4):
            values = {(0, (4, 0, 0)): factor, (1, (3, 0, 0)): -2*factor,
                      (1, (1, 0, 0)): 2*factor, (1, (0, 0, 0)): -factor}
            program = serialize_program(values, 3, 3, 4, q)
            cert = make_certificate(matrix, 4, program, (0, 1, 2), bits-1, q, 1)
            independent_verify(cert, matrix, bits)
            check_residual_reconstruction(cert, matrix, bits)
            counts["residual_coordinate_roundtrips"] += 1
            value = fixture(matrix, cert, bits, 20261024+10*bits+factor)
            verify_fixture(value, cert, matrix, bits)
            counts["quartic_certificates"] += 1
            counts["nonunit_checks"] += int(factor != 1)
            counts["full_view_fixtures"] += 1
    for width in (3, 6):
        for bits in (1, 3, 5):
            q = 1 << bits
            rng = random.Random(20261025+100*width+bits)
            dense = [[rng.randrange(q) for _ in range(width)] for _ in range(3)]
            tensor = [((0, 1, 2), 1), ((0, 0, width-1), 2)]
            program = tensor_program(dense, tensor, q)
            cert = make_certificate(dense, 3, program, (0, 1, 2), bits-1, q, 1)
            independent_verify(cert, dense, bits)
            check_residual_reconstruction(cert, dense, bits)
            counts["residual_coordinate_roundtrips"] += 1
            for secret in itertools.product((0, 1), repeat=3):
                x = [sum(secret[i]*dense[i][j] for i in range(3)) for j in range(width)]
                noiseless = sum(coefficient*math.prod(x[j] for j in positions) for positions, coefficient in tensor)
                for errors in itertools.product((-1, 0, 1), repeat=width):
                    bodies = [(a+e) % q for a, e in zip(x, errors)]
                    t, c, b = compile_control(program, 3, bodies, q)
                    phase = b+sum(s*a for s, a in zip(secret, c))-sum(secret[i]*t[i][j]*secret[j] for i in range(3) for j in range(3))
                    noise = sum(coefficient*math.prod(errors[j] for j in positions) for positions, coefficient in tensor)
                    assert (phase-noiseless-noise) % q == 0
                    counts["dense_source_exhaustive_phases"] += 1
    return counts


def runner_fixture(connection, kind):
    if kind == "timeout":
        time.sleep(1)
    elif kind == "success":
        connection.send(dict(status="fixture_success"))
    connection.close()


def runner_checks():
    before = {process.pid for process in multiprocessing.active_children()}
    assert bounded_call(runner_fixture, ("success",), 1)["status"] == "fixture_success"
    assert bounded_call(runner_fixture, ("timeout",), 0.02)["status"] == "wall_timeout"
    assert bounded_call(runner_fixture, ("no_result",), 1)["status"] == "worker_no_result"
    assert {process.pid for process in multiprocessing.active_children()} == before
    # Exercise conditional all-target expansion even if no real search wins.
    seed, blocks = case_masks(3, 1, 3)
    case = dict(n=3, m=1, bits=3, seed=seed, blocks=blocks, attempts=[], baselines=[])
    result = dict(cases=[case], full_tables=[])
    with tempfile.TemporaryDirectory(prefix="fhe-boolean-runner-") as directory:
        args = SimpleNamespace(output=Path(directory)/"checkpoint.json", global_seconds=0, query_seconds=1)
        expand_full_table(result, case, dict(radius=1, degree=4), {}, args, time.monotonic())
        table = result["full_tables"][0]
        assert table["expected_slots"] == len(table["slots"]) == 3
        assert all(item["attempt"]["status"] == "global_deadline_unstarted" for item in table["slots"])
        assert not table["all_queries_finished"] and not table["budget"]["strict_budget"]
    return dict(worker_lifecycle_fixtures=3, deadline_full_table_slots=3)


def atomic_write(path, result):
    temporary = path.with_suffix(path.suffix+".tmp")
    temporary.write_text(json.dumps(result, separators=(",", ":"))+"\n")
    temporary.replace(path)


def summarize(result):
    attempts = [entry for case in result["cases"] for entry in case["attempts"]]
    candidates = [entry for entry in attempts if entry.get("candidate")]
    fixtures = [value for entry in candidates for value in entry["fixtures"]]
    fixtures += [value for case in result["cases"] for item in case["baselines"] for value in item["fixtures"]]
    fixtures += [value for table in result["full_tables"] for item in table["slots"] for value in item["fixtures"]]
    return dict(cases=len(result["cases"]), attempts=len(attempts),
                statuses={status: sum(entry["status"] == status for entry in attempts) for status in sorted({entry["status"] for entry in attempts})},
                accepted_improvements=len(candidates),
                higher_degree_improvements=sum(entry.get("genuine_higher_degree", False) for entry in candidates),
                baseline_certificates=sum(len(case["baselines"]) for case in result["cases"]),
                full_tables=len(result["full_tables"]),
                full_table_budget_passes=sum(table.get("budget", {}).get("strict_budget", False) for table in result["full_tables"]),
                full_table_queries=sum(len(table["slots"]) for table in result["full_tables"]),
                verified_source_phases=len(fixtures),
                sampled_margin_failures=sum(not value["strict_decoding_margin"] for value in fixtures),
                toy_source_unique_key_fixtures=sum(len(value["compatible_binary_keys"]) == 1 for value in fixtures))


def study(args):
    started = time.monotonic()
    prior = json.loads(args.prior_study.read_text()) if args.prior_study else None
    requested_seconds = args.global_seconds
    if prior:
        assert prior["status"] == "interrupted_for_residual_encoding"
        args.global_seconds = max(0, requested_seconds-prior["interrupted_elapsed_seconds"])
    result = dict(version=VERSION, scope="Finite exact Boolean polynomial search, not an FHE proof",
                  config=dict(query_seconds=args.query_seconds, global_seconds=requested_seconds,
                              current_run_seconds=args.global_seconds, encoding="residual",
                              coefficient_limit=args.coefficient_limit, quick=args.quick),
                  provenance=dict(script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),
                  dependencies=dict(generation="Z3 4.13.3 in the existing isolated environment", replay="Python standard library"),
                  identities=identity_checks(), runner_checks=runner_checks(), cases=[], full_tables=[],
                  proved_family_success=False, proved_polynomial_time_generator=False,
                  production_Lean_changed=False, status="running")
    if prior:
        result["prior_study"] = prior
    configurations = CONFIGURATIONS[:1] if args.quick else CONFIGURATIONS
    bit_grid = (12,) if args.quick else BITS
    for n, m in configurations:
        for bits in bit_grid:
            seed, blocks = case_masks(n, m, bits)
            result["cases"].append(dict(n=n, m=m, bits=bits, seed=seed, blocks=blocks, attempts=[], baselines=[]))
    best = {}
    # Hardest level first, with breadth across cases before lower levels.
    for level_kind in ("top", "middle", "low"):
        for radius_kind in ("family", "one", "three"):
            for case in result["cases"]:
                n, m, bits = case["n"], case["m"], case["bits"]
                matrix, q = joined(case["blocks"]), 1 << bits
                radius = {"family": family_radius(bits), "one": 1, "three": 3}[radius_kind]
                level = {"top": bits-1, "middle": bits//2, "low": 0}[level_kind]
                indices = (0, 1, 2)
                key = (n, m, bits, radius, indices, level)
                baseline = make_certificate(matrix, 3, zero_baseline(n, 3*m, 3, indices, level, q), indices, level, q, radius)
                independent_verify(baseline, matrix, bits)
                baseline_fixture = fixture(matrix, baseline, bits, case["seed"]+10000*radius+100*level)
                verify_fixture(baseline_fixture, baseline, matrix, bits)
                case["baselines"].append(dict(certificate=baseline, fixtures=[baseline_fixture]))
                best.setdefault(key, baseline)
                for degree in DEGREES:
                    count = len(grammar(n, 3*m, degree))
                    entry = dict(degree=degree, radius=radius, radius_kind=radius_kind, level=level,
                                 indices=list(indices), baseline_J=baseline["bound"]["J"],
                                 incumbent_J=best[key]["bound"]["J"])
                    remaining = args.global_seconds-(time.monotonic()-started)
                    if count > args.coefficient_limit:
                        entry.update(status="coefficient_limit", variables=count)
                    elif remaining <= 0:
                        entry.update(status="global_deadline_unstarted", variables=count)
                    else:
                        seconds = min(args.query_seconds, remaining)
                        response = attempt_search(matrix, bits, radius, degree, indices, level, best[key], seconds)
                        entry.update(response)
                        if "candidate" in entry:
                            candidate = entry["candidate"]
                            independent_verify(candidate, matrix, bits)
                            assert int(candidate["bound"]["J"]) < int(entry["incumbent_J"])
                            entry["fixtures"] = [fixture(matrix, candidate, bits, case["seed"]+10000000*degree+10000*radius+100*level+i) for i in range(4)]
                            for value in entry["fixtures"]:
                                verify_fixture(value, candidate, matrix, bits)
                            entry["budget"] = budget(n, bits, radius, int(candidate["bound"]["J"]))
                            entry["genuine_higher_degree"] = any(mask.bit_count()+sum(powers) > 3
                                                                  for mask, powers, _ in candidate["program"])
                            best[key] = candidate
                    case["attempts"].append(entry)
                    result["summary"] = summarize(result)
                    result["elapsed_seconds"] = round(time.monotonic()-started, 3)
                    atomic_write(args.output, result)
                    print(json.dumps(dict(event="query", n=n, m=m, bits=bits, degree=degree, radius=radius, level=level,
                                          status=entry["status"], candidate_J=entry.get("candidate", {}).get("bound", {}).get("J"))), flush=True)
    winners = [(case, entry) for case in result["cases"] for entry in case["attempts"]
               if entry.get("genuine_higher_degree")]
    if winners:
        case, winner = winners[0]
        expand_full_table(result, case, winner, best, args, started)
    result["advancement"] = dict(genuine_higher_degree_candidate=bool(winners),
                                 production_gate_satisfied=False,
                                 reason="Family success probability, efficient generation and full ordinary-LWE integration remain unproved")
    result["status"] = "screen_complete"
    result["summary"] = summarize(result)
    result["elapsed_seconds"] = round(time.monotonic()-started, 3)
    atomic_write(args.output, result)
    print(json.dumps(result["summary"]), flush=True)


def expand_full_table(result, case, winner, best, args, started):
    """First winning case/radius, all triples and ALL gadget levels.

    A deadline stops only new optimization: exact baseline certificates still
    cover every slot. This is not mislabeled completion of the optimizers.
    """
    n, m, bits = case["n"], case["m"], case["bits"]
    radius, degree = winner["radius"], winner["degree"]
    matrix, q = joined(case["blocks"]), 1 << bits
    table = dict(n=n, m=m, bits=bits, radius=radius, search_degree=degree, slots=[])
    result["full_tables"].append(table)
    for indices in itertools.combinations(range(n), 3):
        for level in range(bits):
            key = (n, m, bits, radius, indices, level)
            baseline = best.get(key)
            if baseline is None:
                baseline = make_certificate(matrix, 3, zero_baseline(n, 3*m, 3, indices, level, q), indices, level, q, radius)
            remaining = args.global_seconds-(time.monotonic()-started)
            if remaining <= 0:
                attempt = dict(status="global_deadline_unstarted")
            else:
                seconds = min(args.query_seconds, remaining)
                attempt = attempt_search(matrix, bits, radius, degree, indices, level, baseline, seconds)
            candidate = attempt.pop("candidate", None)
            selected = candidate or baseline
            independent_verify(selected, matrix, bits)
            if candidate:
                assert int(candidate["bound"]["J"]) < int(baseline["bound"]["J"])
            value = fixture(matrix, selected, bits, case["seed"]+20000000+10000*radius+100*level+sum(1 << i for i in indices))
            verify_fixture(value, selected, matrix, bits)
            table["slots"].append(dict(indices=list(indices), level=level, incumbent_J=baseline["bound"]["J"],
                                       candidate_improved=candidate is not None, attempt=attempt,
                                       selected=selected, fixtures=[value]))
            result["summary"] = summarize(result)
            atomic_write(args.output, result)
    table["expected_slots"] = math.comb(n, 3)*bits
    assert len(table["slots"]) == table["expected_slots"]
    table["budget"] = budget(n, bits, radius, max(int(item["selected"]["bound"]["J"]) for item in table["slots"]))
    table["all_queries_finished"] = all(item["attempt"]["status"] in ("sat", "unsat", "certificate_lower_bound") for item in table["slots"])
    table["toy_source_unique_key_fixtures"] = sum(len(item["fixtures"][0]["compatible_binary_keys"]) == 1 for item in table["slots"])


def replay(path):
    result = json.loads(path.read_text())
    assert result["version"] == VERSION and result["identities"] == identity_checks()
    assert not result["proved_family_success"] and not result["proved_polynomial_time_generator"]
    assert not result["production_Lean_changed"]
    if "prior_study" in result:
        prior = result["prior_study"]
        assert prior["status"] == "interrupted_for_residual_encoding"
        assert prior["summary"] == summarize(prior)
        assert not prior["summary"]["accepted_improvements"]
        assert result["config"]["current_run_seconds"] == max(0, result["config"]["global_seconds"]-prior["interrupted_elapsed_seconds"])
        for case in prior["cases"]:
            _, blocks = case_masks(case["n"], case["m"], case["bits"])
            assert case["blocks"] == blocks
            for item in case["baselines"]:
                independent_verify(item["certificate"], joined(blocks), case["bits"])
                for value in item["fixtures"]:
                    verify_fixture(value, item["certificate"], joined(blocks), case["bits"])
    assert result["provenance"]["script_sha256"] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    assert result["runner_checks"] == dict(worker_lifecycle_fixtures=3, deadline_full_table_slots=3)
    expected_cases = [(n, m, bits) for n, m in (CONFIGURATIONS[:1] if result["config"]["quick"] else CONFIGURATIONS)
                      for bits in ((12,) if result["config"]["quick"] else BITS)]
    assert [(case["n"], case["m"], case["bits"]) for case in result["cases"]] == expected_cases
    checked = phases = 0
    for case in result["cases"]:
        n, m, bits = case["n"], case["m"], case["bits"]
        seed, blocks = case_masks(n, m, bits)
        assert case["seed"] == seed and case["blocks"] == blocks
        matrix = joined(blocks)
        baseline_values = {}
        expected_slots = [(radius, level) for level in (bits-1, bits//2, 0) for radius in (family_radius(bits), 1, 3)]
        assert [(item["certificate"]["radius"], item["certificate"]["level"]) for item in case["baselines"]] == expected_slots
        for item in case["baselines"]:
            certificate = item["certificate"]
            independent_verify(certificate, matrix, bits)
            assert certificate["program"] == zero_baseline(n, 3*m, 3, (0, 1, 2), certificate["level"], 1 << bits)
            baseline_values[(certificate["radius"], certificate["level"])] = certificate
            for value in item["fixtures"]:
                assert value == fixture(matrix, certificate, bits, value["seed"])
                verify_fixture(value, certificate, matrix, bits)
                phases += 1
            checked += 1
        assert [(entry["radius"], entry["level"], entry["degree"]) for entry in case["attempts"]] == [
            (radius, level, degree) for radius, level in expected_slots for degree in DEGREES]
        incumbents = dict(baseline_values)
        for entry in case["attempts"]:
            key = (entry["radius"], entry["level"])
            assert entry["baseline_J"] == baseline_values[key]["bound"]["J"]
            assert entry["incumbent_J"] == incumbents[key]["bound"]["J"]
            assert entry["indices"] == [0, 1, 2]
            variables = len(grammar(n, 3*m, entry["degree"]))
            if variables > result["config"]["coefficient_limit"]:
                assert entry["status"] == "coefficient_limit"
            if entry["status"] == "certificate_lower_bound":
                assert int(entry["incumbent_J"]) == class_lower_bound(entry["radius"], entry["level"])
                assert entry["certified_lower_bound"] == entry["incumbent_J"]
            if entry.get("candidate"):
                candidate = entry["candidate"]
                assert candidate["degree"] == entry["degree"] and candidate["radius"] == entry["radius"]
                assert candidate["indices"] == entry["indices"] and candidate["level"] == entry["level"]
                independent_verify(candidate, matrix, bits)
                assert int(candidate["bound"]["J"]) < int(entry["incumbent_J"])
                assert entry["genuine_higher_degree"] == any(mask.bit_count()+sum(powers) > 3 for mask, powers, _ in candidate["program"])
                assert entry["budget"] == budget(n, bits, entry["radius"], int(candidate["bound"]["J"]))
                for value in entry["fixtures"]:
                    assert value == fixture(matrix, candidate, bits, value["seed"])
                    verify_fixture(value, candidate, matrix, bits)
                    phases += 1
                checked += 1
                incumbents[key] = candidate
    for table in result["full_tables"]:
        n, m, bits, radius = table["n"], table["m"], table["bits"], table["radius"]
        case = next(case for case in result["cases"] if (case["n"], case["m"], case["bits"]) == (n, m, bits))
        matrix = joined(case["blocks"])
        assert table["expected_slots"] == math.comb(n, 3)*bits
        assert [(item["indices"], item["level"]) for item in table["slots"]] == [
            (list(indices), level) for indices in itertools.combinations(range(n), 3) for level in range(bits)]
        for item in table["slots"]:
            certificate = item["selected"]
            independent_verify(certificate, matrix, bits)
            assert certificate["radius"] == radius and certificate["indices"] == item["indices"] and certificate["level"] == item["level"]
            if item["candidate_improved"]:
                assert int(certificate["bound"]["J"]) < int(item["incumbent_J"])
            else:
                assert certificate["bound"]["J"] == item["incumbent_J"]
            for value in item["fixtures"]:
                assert value == fixture(matrix, certificate, bits, value["seed"])
                verify_fixture(value, certificate, matrix, bits)
                phases += 1
            checked += 1
        assert table["budget"] == budget(n, bits, radius, max(int(item["selected"]["bound"]["J"]) for item in table["slots"]))
        assert table["all_queries_finished"] == all(item["attempt"]["status"] in ("sat", "unsat", "certificate_lower_bound") for item in table["slots"])
        assert table["toy_source_unique_key_fixtures"] == sum(len(item["fixtures"][0]["compatible_binary_keys"]) == 1 for item in table["slots"])
    assert result["summary"] == summarize(result)
    print(json.dumps(dict(replayed_certificates=checked, replayed_source_phases=phases, summary=result["summary"])), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--verify-runner", action="store_true")
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--query-seconds", type=float, default=30)
    parser.add_argument("--global-seconds", type=float, default=1200)
    parser.add_argument("--coefficient-limit", type=int, default=600)
    parser.add_argument("--prior-study", type=Path, help="Preserve an interrupted coefficient-encoding pilot and charge its time to the global budget")
    args = parser.parse_args()
    assert args.query_seconds > 0 and args.global_seconds > 0 and args.coefficient_limit > 0
    if args.self_test:
        print(json.dumps(identity_checks()))
    elif args.verify_runner:
        print(json.dumps(runner_checks()))
    elif args.verify_existing:
        replay(args.verify_existing)
    else:
        study(args)


if __name__ == "__main__":
    main()
