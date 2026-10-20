#!/usr/bin/env python3
"""Public three-source cubic compilation with exact certificates.

The compiler cancels all first/second-order errors. Its true original-key
phase is the target cubic plus a trilinear source-error contraction.
Public LLL/Babai builds the coefficient tensor; shortness is NOT assumed.
Finite refresh margins do not establish hard source parameters or FHE.
Generation requires fpylll 0.6.4/cysignals. Replay uses only the standard library.
"""
import argparse
from fractions import Fraction
import itertools
import json
import math
import multiprocessing
from pathlib import Path
import random
import time


def centered(x, q):
    return (x+q//2) % q-q//2


def contract(tensor, first, second, third):
    return sum(d*first[a]*second[b]*third[c] for (a, b, c), d in tensor.items())


def phase(secret, ciphertext, q):
    t, c, b = ciphertext
    return (b+sum(s*x for s, x in zip(secret, c))-
            sum(secret[i]*t[i][j]*secret[j] for i in range(len(secret))
                for j in range(len(secret)))) % q


def coefficients(blocks, q):
    """Boolean-reduced coefficients of sum D_abc*x1_a*x2_b*x3_c."""
    n, m = len(blocks[0]), len(blocks[0][0])
    monomials = [tuple(c) for degree in (1, 2, 3)
                 for c in itertools.combinations(range(n), degree)]
    coordinates = list(itertools.product(range(m), repeat=3))
    rows = []
    for support in monomials:
        assignments = [v for v in itertools.product(support, repeat=3) if set(v) == set(support)]
        rows.append([sum(blocks[0][i][a]*blocks[1][j][b]*blocks[2][k][c]
                         for i, j, k in assignments) % q for a, b, c in coordinates])
    return monomials, coordinates, rows


class UnsolvableTarget(ValueError):
    def __init__(self, combination, divisor, residue):
        super().__init__(f"row combination is divisible by {divisor}, target residue is {residue}")
        self.witness = dict(combination=combination, divisor=divisor, target_residue=residue)


def general_public_solver(matrix, q, bits):
    """Diagonalize over Z/(2^bits), retaining even pivots and exact obstructions."""
    from fpylll import FPLLL, GSO, IntegerMatrix, LLL
    height, width = len(matrix), len(matrix[0])
    table = [[x % q for x in row] for row in matrix]
    left = [[int(i == j) for j in range(height)] for i in range(height)]
    right = [[int(i == j) for j in range(width)] for i in range(width)]
    pivots = []
    for index in range(min(height, width)):
        candidates = [(table[i][j] & -table[i][j], i, j)
                      for i in range(index, height) for j in range(index, width) if table[i][j]]
        if not candidates:
            break
        power, row, column = min(candidates)
        for data in (table, left):
            data[index], data[row] = data[row], data[index]
        for data in (table, right):
            for line in data:
                line[index], line[column] = line[column], line[index]
        inv = pow(table[index][index]//power, -1, q)
        table[index] = [x*inv % q for x in table[index]]
        left[index] = [x*inv % q for x in left[index]]
        assert table[index][index] == power
        for i in range(index+1, height):
            assert table[i][index] % power == 0
            multiple = table[i][index]//power
            table[i] = [(x-multiple*y) % q for x, y in zip(table[i], table[index])]
            left[i] = [(x-multiple*y) % q for x, y in zip(left[i], left[index])]
        for j in range(index+1, width):
            assert table[index][j] % power == 0
            multiple = table[index][j]//power
            for data in (table, right):
                for line in data:
                    line[j] = (line[j]-multiple*line[index]) % q
        pivots.append(power)
    assert all(table[i][j] == (pivots[i] if i == j and i < len(pivots) else 0)
               for i in range(height) for j in range(width))
    cached = []

    def solve(target):
        transformed = [sum(a*b for a, b in zip(row, target)) % q for row in left]
        for i, value in enumerate(transformed):
            divisor = pivots[i] if i < len(pivots) else q
            if value % divisor:
                # A directly checkable row certificate of nonmembership.
                witness_row = [sum(left[i][k]*matrix[k][j] for k in range(height)) % q
                               for j in range(width)]
                assert all(x % divisor == 0 for x in witness_row)
                raise UnsolvableTarget(left[i], divisor, value)
        diagonal_solution = [transformed[i]//pivots[i] if i < len(pivots) else 0
                             for i in range(width)]
        particular = [centered(sum(a*b for a, b in zip(row, diagonal_solution)), q) for row in right]
        if not cached:
            # These rows generate the complete inverse-image lattice. Including
            # qI permits reducing the column transformation modulo q safely.
            generators = [[q*int(i == j) for j in range(width)] for i in range(width)]
            for i in range(width):
                multiplier = q//pivots[i] if i < len(pivots) else 1
                vector = [centered(right[j][i]*multiplier, q) for j in range(width)]
                if any(vector):
                    generators.append(vector)
            lattice = IntegerMatrix.from_matrix(generators)
            FPLLL.set_precision(max(192, 4*bits))
            LLL.reduction(lattice)
            basis = [[int(lattice[i, j]) for j in range(width)] for i in range(len(generators))
                     if any(lattice[i, j] for j in range(width))]
            assert len(basis) == width
            assert all(all(sum(a*b for a, b in zip(row, v)) % q == 0 for row in matrix) for v in basis)
            lattice = IntegerMatrix.from_matrix(basis)
            cached.extend((basis, GSO.Mat(lattice, float_type="mpfr", update=True)))
        basis, gso = cached
        approximation = tuple(map(int, gso.babai(particular)))
        answer = [particular[j]-sum(approximation[i]*basis[i][j] for i in range(width))
                  for j in range(width)]
        assert all(sum(a*b for a, b in zip(row, answer)) % q == t % q
                   for row, t in zip(matrix, target))
        return answer
    return solve


def public_solver(matrix, q, bits):
    """Exact modular certificate, LLL reduction and checked Babai combination."""
    from fpylll import FPLLL, GSO, IntegerMatrix, LLL
    rows, width = len(matrix), len(matrix[0])
    reduced = [[x % q for x in row] for row in matrix]
    transform = [[int(i == j) for j in range(rows)] for i in range(rows)]
    pivots = []
    for column in range(width):
        rank = len(pivots)
        pivot = next((i for i in range(rank, rows) if reduced[i][column] & 1), None)
        if pivot is None:
            continue
        for table in (reduced, transform):
            table[rank], table[pivot] = table[pivot], table[rank]
        inv = pow(reduced[rank][column], -1, q)
        reduced[rank] = [x*inv % q for x in reduced[rank]]
        transform[rank] = [x*inv % q for x in transform[rank]]
        for i in range(rows):
            if i != rank:
                factor = reduced[i][column]
                reduced[i] = [(x-factor*y) % q for x, y in zip(reduced[i], reduced[rank])]
                transform[i] = [(x-factor*y) % q for x, y in zip(transform[i], transform[rank])]
        pivots.append(column)
        if len(pivots) == rows:
            break
    if len(pivots) != rows:
        return general_public_solver(matrix, q, bits)
    basis = [[q*int(j == pivot) for j in range(width)] for pivot in pivots]
    for column in range(width):
        if column in pivots:
            continue
        v = [int(j == column) for j in range(width)]
        for i, pivot in enumerate(pivots):
            v[pivot] = centered(-reduced[i][column], q)
        basis.append(v)
    lattice = IntegerMatrix.from_matrix(basis)
    FPLLL.set_precision(max(192, 4*bits))
    LLL.reduction(lattice)
    basis = [[int(lattice[i, j]) for j in range(width)] for i in range(width)]
    assert all(all(sum(a*b for a, b in zip(row, v)) % q == 0 for row in matrix) for v in basis)
    gso = GSO.Mat(lattice, float_type="mpfr", update=True)

    def solve(target):
        particular = [0]*width
        for i, pivot in enumerate(pivots):
            particular[pivot] = centered(sum(a*b for a, b in zip(transform[i], target)), q)
        coefficients = tuple(map(int, gso.babai(particular)))
        nearby = [sum(coefficients[i]*basis[i][j] for i in range(width)) for j in range(width)]
        answer = [a-b for a, b in zip(particular, nearby)]
        assert all(sum(a*b for a, b in zip(row, answer)) % q == t % q
                   for row, t in zip(matrix, target))
        return answer
    return solve


def preprocess(blocks, vector, q):
    """Public linear/quadratic coefficient tables; no body, key or error input."""
    n, m = len(blocks[0]), len(blocks[0][0])
    positions = list(itertools.product(range(m), repeat=3))
    tensor = {position: d for position, d in zip(positions, vector) if d}
    monomials, _, rows = coefficients(blocks, q)
    polynomial = [sum(a*b for a, b in zip(row, vector)) % q for row in rows]
    lower_linear = {support[0]: value for support, value in zip(monomials, polynomial) if len(support) == 1}
    lower_quadratic = {support: value for support, value in zip(monomials, polynomial) if len(support) == 2}
    # qtables[body block][body column][secret row][secret column].
    qtables = [[[[0]*n for _ in range(n)] for _ in range(m)] for _ in range(3)]
    # ltables[missing body block][other column 1][other column 2][secret row].
    ltables = [[[[0]*n for _ in range(m)] for _ in range(m)] for _ in range(3)]
    for (a, b, c), d in tensor.items():
        for i in range(n):
            ltables[0][b][c][i] += d*blocks[0][i][a]
            ltables[1][a][c][i] += d*blocks[1][i][b]
            ltables[2][a][b][i] += d*blocks[2][i][c]
            for j in range(n):
                qtables[0][a][i][j] += d*blocks[1][i][b]*blocks[2][j][c]
                qtables[1][b][i][j] += d*blocks[0][i][a]*blocks[2][j][c]
                qtables[2][c][i][j] += d*blocks[0][i][a]*blocks[1][j][b]
    def modular(value):
        return [modular(x) for x in value] if isinstance(value, list) else value % q
    return dict(n=n, m=m, q=q, tensor=tensor, quadratic=modular(qtables), linear=modular(ltables),
                lower_linear=lower_linear, lower_quadratic=lower_quadratic,
                polynomial=polynomial, monomials=monomials)


def compile(model, bodies):
    """Positive full-coordinate public compiler; original secret never an input."""
    n, m, q = model["n"], model["m"], model["q"]
    body = contract(model["tensor"], *bodies) % q
    linear = [0]*n
    matrix = [[0]*n for _ in range(n)]
    for i in range(n):
        linear[i] = -model["lower_linear"][i]
        for a, b in itertools.product(range(m), repeat=2):
            linear[i] -= bodies[1][a]*bodies[2][b]*model["linear"][0][a][b][i]
            linear[i] -= bodies[0][a]*bodies[2][b]*model["linear"][1][a][b][i]
            linear[i] -= bodies[0][a]*bodies[1][b]*model["linear"][2][a][b][i]
        for j in range(n):
            matrix[i][j] = -sum(bodies[r][a]*model["quadratic"][r][a][i][j]
                                for r in range(3) for a in range(m))
    for (i, j), value in model["lower_quadratic"].items():
        matrix[i][j] += value
    return [[[x % q for x in row] for row in matrix], [x % q for x in linear], body]


def bodies_for(blocks, secret, errors, q):
    return [[(sum(s*blocks[r][i][j] for i, s in enumerate(secret))+errors[r][j]) % q
             for j in range(len(blocks[r][0]))] for r in range(3)]


def identity_checks():
    """Exhaust all binary keys and ternary errors for a two-column tensor."""
    count = 0
    moments = []
    for q in (2, 8, 97):
        rng = random.Random(6180+q)
        n, m = 3, 2
        blocks = [[[rng.randrange(q) for _ in range(m)] for _ in range(n)] for _ in range(3)]
        vector = [rng.randrange(-2, 3) for _ in range(m**3)]
        model = preprocess(blocks, vector, q)
        errors_for_moments = [contract(model["tensor"], raw[:m], raw[m:2*m], raw[2*m:])
                             for raw in itertools.product((-1, 0, 1), repeat=3*m)]
        assert sum(errors_for_moments) == 0
        second_moment = Fraction(sum(x*x for x in errors_for_moments), len(errors_for_moments))
        expected_second_moment = Fraction(2, 3)**3*sum(x*x for x in vector)
        assert second_moment == expected_second_moment
        moments.append(str(second_moment))
        for secret in itertools.product((0, 1), repeat=n):
            # Subtracting the stored lower polynomial leaves just this cubic.
            cubic = sum(value*math.prod(secret[i] for i in monomial)
                        for monomial, value in zip(model["monomials"], model["polynomial"])
                        if len(monomial) == 3) % q
            for raw_errors in itertools.product((-1, 0, 1), repeat=3*m):
                errors = [list(raw_errors[r*m:(r+1)*m]) for r in range(3)]
                bodies = bodies_for(blocks, secret, errors, q)
                output = compile(model, bodies)
                residual = contract(model["tensor"], *errors)
                assert phase(secret, output, q) == (cubic+residual) % q
                assert abs(residual) <= sum(map(abs, vector))
                count += 1
    return dict(full_coordinate_phase_error_cases=count, keys_per_modulus=8,
                error_vectors_per_key=729, moduli=[2, 8, 97],
                exact_centered_error_moments=moments)


def solver_checks():
    """Compare modular-image membership with exhaustive, independent enumeration."""
    rng = random.Random(62091)
    matrices = targets = obstructions = 0
    for q in (2, 4, 8):
        height = 3 if q == 8 else 2
        raw_matrices = itertools.product(range(q), repeat=4) if q < 8 else [
            tuple(rng.randrange(q) for _ in range(6)) for _ in range(64)]
        for raw in raw_matrices:
            matrix = [list(raw[2*i:2*i+2]) for i in range(height)]
            image = {tuple(sum(a*b for a, b in zip(row, x)) % q for row in matrix)
                     for x in itertools.product(range(q), repeat=2)}
            # Exercise both the fast public entry and the nonunit implementation.
            for solve in (public_solver(matrix, q, q.bit_length()-1),
                          general_public_solver(matrix, q, q.bit_length()-1)):
                for target in itertools.product(range(q), repeat=height):
                    try:
                        answer = solve(target)
                    except UnsolvableTarget as error:
                        assert target not in image
                        witness = error.witness
                        combination, divisor = witness["combination"], witness["divisor"]
                        assert all(sum(combination[i]*matrix[i][j] for i in range(height)) % divisor == 0
                                   for j in range(2))
                        residue = sum(a*b for a, b in zip(combination, target)) % q
                        assert residue == witness["target_residue"] and residue % divisor != 0
                        obstructions += 1
                    else:
                        assert target in image
                        assert tuple(sum(a*b for a, b in zip(row, answer)) % q for row in matrix) == target
                    targets += 1
            matrices += 1
    print(json.dumps(dict(solver_matrices=matrices, solver_target_trials=targets,
                          exact_nonmembership_certificates=obstructions)), flush=True)


def bootstrap_budget(n, bits, bound, radius):
    rows = n*n+n+1
    growth = rows*bits
    lookup = 1 << (8*rows-1).bit_length()
    common = max(bound, (n+1)*radius)
    output_bound = lookup*rows*growth*(growth+1)*common
    public_samples = growth+2*bits+17
    assert public_samples*(n+1)*radius <= output_bound
    budget = lookup*(growth+1)*output_bound
    return dict(control_bound=str(bound), common_bound=str(common),
                public_samples=public_samples, fresh_encryption_bound=str(public_samples*(n+1)*radius),
                budget=str(budget), modulus=str(1 << bits),
                strict_budget=budget < (1 << bits), lookup=lookup)


def linear_recovery(blocks, q, bits):
    """Public ordinary-source filter, not an assumed independent hardness test."""
    n = len(blocks[0])
    matrix = [sum((blocks[r][i] for r in range(3)), []) for i in range(n)]
    try:
        solve = public_solver(matrix, q, bits)
    except ValueError as error:
        return dict(status="unit_rank_failure", reason=str(error), vectors=[])
    vectors = []
    for i in range(n):
        target = [q//2*int(i == j) for j in range(n)]
        try:
            vector = solve(target)
        except UnsolvableTarget as error:
            return dict(status="incomplete_key_recovery", coordinate=i,
                        witness=error.witness, vectors=vectors)
        vectors.append(dict(coordinate=i, coefficients=vector, l1=str(sum(map(abs, vector)))))
    return dict(status="ok", vectors=vectors,
                guaranteed_key_recovery_radius_one=all(4*int(v["l1"]) < q for v in vectors))


def run_case(n, m, bits, seed):
    started = time.monotonic()
    q = 1 << bits
    rng = random.Random(seed)
    blocks = [[[rng.randrange(q) for _ in range(m)] for _ in range(n)] for _ in range(3)]
    monomials, positions, all_rows = coefficients(blocks, q)
    cubic_rows = [row for monomial, row in zip(monomials, all_rows) if len(monomial) == 3]
    cubic_monomials = [v for v in monomials if len(v) == 3]
    record = dict(n=n, m=m, bits=bits, seed=seed, blocks=blocks,
                  cubic_constraints=len(cubic_rows), lattice_dimension=m**3, controls=[], rejected_controls=[])
    record["linear_source_filter"] = linear_recovery(blocks, q, bits)
    try:
        solve = public_solver(cubic_rows, q, bits)
    except ValueError as error:
        return dict(**record, status="unit_rank_failure", reason=str(error),
                    elapsed_seconds=round(time.monotonic()-started, 3))
    targets = sorted({(0, 1, 2), (n-3, n-2, n-1)})
    for target_indices in targets:
        for level in sorted({0, bits-2, bits-1}):
            weight = 1 << level
            target = [weight*int(indices == target_indices) for indices in cubic_monomials]
            try:
                vector = solve(target)
            except UnsolvableTarget as error:
                record["rejected_controls"].append(dict(indices=list(target_indices), level=level,
                                                        witness=error.witness))
                continue
            l1 = sum(map(abs, vector))
            model = preprocess(blocks, vector, q)
            trials, failures, examples = 0, 0, []
            keys = list(itertools.product((0, 1), repeat=n)) if n <= 4 else [
                tuple(int(i == j) for i in range(n)) for j in range(n)]+[
                tuple(rng.randrange(2) for _ in range(n)) for _ in range(24)]
            for radius in (1, 3):
                for secret in keys:
                    errors = [[rng.randint(-radius, radius) for _ in range(m)] for _ in range(3)]
                    bodies = bodies_for(blocks, secret, errors, q)
                    output = compile(model, bodies)
                    target_phase = weight*math.prod(secret[i] for i in target_indices)
                    actual_error = contract(model["tensor"], *errors)
                    expected = (target_phase+actual_error) % q
                    assert phase(secret, output, q) == expected
                    assert abs(actual_error) <= radius**3*l1
                    fails = 8*abs(centered(expected-target_phase, q)) >= q//2
                    failures += fails
                    trials += 1
                    if (fails or not examples) and len(examples) < 3:
                        examples.append(dict(secret=list(secret), radius=radius, errors=errors,
                                             bodies=bodies, output=output, target_phase=target_phase,
                                             actual_integer_error=str(actual_error)))
            control = dict(indices=list(target_indices), level=level, coefficients=vector,
                           l1=str(l1), frobenius_squared=str(sum(x*x for x in vector)),
                           phase_trials=trials, decoding_margin_failures=failures, examples=examples,
                           supported_margin_radius_one=16*l1 < q,
                           supported_margin_radius_three=16*27*l1 < q,
                           bootstrap_budgets=[bootstrap_budget(n, bits, radius**3*l1, radius) for radius in (1, 3)])
            record["controls"].append(control)
    record["status"] = "certified" if not record["rejected_controls"] else "partial"
    record["elapsed_seconds"] = round(time.monotonic()-started, 3)
    return record


def worker(connection, args):
    try:
        connection.send(run_case(*args))
    except Exception as error:
        connection.send(dict(n=args[0], m=args[1], bits=args[2], seed=args[3],
                             status="worker_error", reason=type(error).__name__+": "+str(error)))
    finally:
        connection.close()


def bounded_case(args, seconds):
    context = multiprocessing.get_context("fork")
    parent, child = context.Pipe(duplex=False)
    process = context.Process(target=worker, args=(child, args))
    process.start()
    child.close()
    deadline = time.monotonic()+seconds
    while time.monotonic() < deadline:
        if parent.poll(0.25):
            try:
                result = parent.recv()
            except EOFError:
                process.join(5)
                return dict(n=args[0], m=args[1], bits=args[2], seed=args[3],
                            status="worker_exit", exitcode=process.exitcode)
            process.join(5)
            return result
        if not process.is_alive():
            process.join()
            return dict(n=args[0], m=args[1], bits=args[2], seed=args[3],
                        status="worker_exit", exitcode=process.exitcode)
    process.terminate()
    process.join(5)
    if process.is_alive():
        process.kill()
        process.join()
    return dict(n=args[0], m=args[1], bits=args[2], seed=args[3],
                status="timeout", timeout_seconds=seconds)


def verify_existing(path):
    result = json.loads(path.read_text())
    assert result["version"] == 2
    assert result["identity_checks"] == identity_checks()
    controls = examples = recoveries = trials = rejections = 0
    for case in result["cases"]:
        if "blocks" not in case:
            continue
        q = 1 << case["bits"]
        n, m, blocks = case["n"], case["m"], case["blocks"]
        rng = random.Random(case["seed"])
        assert blocks == [[[rng.randrange(q) for _ in range(m)] for _ in range(n)] for _ in range(3)]
        monomials, positions, rows = coefficients(blocks, q)
        cubic_rows = [row for support, row in zip(monomials, rows) if len(support) == 3]
        cubic_monomials = [support for support in monomials if len(support) == 3]
        expected_slots = {(indices, level) for indices in {(0, 1, 2), (n-3, n-2, n-1)}
                          for level in {0, case["bits"]-2, case["bits"]-1}}
        slots = [(tuple(c["indices"]), c["level"]) for c in case["controls"]+case["rejected_controls"]]
        assert set(slots) == expected_slots and len(slots) == len(expected_slots)
        for rejection in case["rejected_controls"]:
            witness = rejection["witness"]
            combination, divisor = witness["combination"], witness["divisor"]
            assert len(combination) == len(cubic_rows) and 1 <= divisor <= q and q % divisor == 0
            assert all(sum(combination[i]*cubic_rows[i][j] for i in range(len(cubic_rows))) % divisor == 0
                       for j in range(m**3))
            target = [(1 << rejection["level"])*int(indices == tuple(rejection["indices"]))
                      for indices in cubic_monomials]
            residue = sum(a*b for a, b in zip(combination, target)) % q
            assert residue == witness["target_residue"] and residue % divisor != 0
            rejections += 1
        for control in case["controls"]:
            vector = control["coefficients"]
            assert len(vector) == m**3
            support = tuple(control["indices"])
            weight = 1 << control["level"]
            for monomial, row in zip(monomials, rows):
                if len(monomial) == 3:
                    assert sum(a*b for a, b in zip(row, vector)) % q == weight*int(monomial == support)
            assert control["l1"] == str(sum(map(abs, vector)))
            assert control["frobenius_squared"] == str(sum(x*x for x in vector))
            model = preprocess(blocks, vector, q)
            assert control["supported_margin_radius_one"] == (16*sum(map(abs, vector)) < q)
            assert control["supported_margin_radius_three"] == (16*27*sum(map(abs, vector)) < q)
            assert control["bootstrap_budgets"] == [
                bootstrap_budget(n, case["bits"], radius**3*sum(map(abs, vector)), radius) for radius in (1, 3)]
            # Reconstruct every source tape, including the key/error RNG schedule.
            keys = list(itertools.product((0, 1), repeat=n)) if n <= 4 else [
                tuple(int(i == j) for i in range(n)) for j in range(n)]+[
                tuple(rng.randrange(2) for _ in range(n)) for _ in range(24)]
            replayed_trials = replayed_failures = 0
            replayed_examples = []
            for radius in (1, 3):
                for secret in keys:
                    errors = [[rng.randint(-radius, radius) for _ in range(m)] for _ in range(3)]
                    bodies = bodies_for(blocks, secret, errors, q)
                    output = compile(model, bodies)
                    target_phase = weight*math.prod(secret[i] for i in support)
                    actual_error = contract(model["tensor"], *errors)
                    t, c, b = output
                    direct = b+sum(secret[i]*c[i] for i in range(n))
                    direct -= sum(secret[i]*t[i][j]*secret[j] for i in range(n) for j in range(n))
                    assert direct % q == (target_phase+actual_error) % q
                    assert abs(actual_error) <= radius**3*sum(map(abs, vector))
                    fails = 16*abs(centered(actual_error, q)) >= q
                    replayed_failures += fails
                    replayed_trials += 1
                    if (fails or not replayed_examples) and len(replayed_examples) < 3:
                        replayed_examples.append(dict(secret=list(secret), radius=radius, errors=errors,
                                                      bodies=bodies, output=output, target_phase=target_phase,
                                                      actual_integer_error=str(actual_error)))
            assert replayed_trials == control["phase_trials"]
            assert replayed_failures == control["decoding_margin_failures"]
            assert replayed_examples == control["examples"]
            trials += replayed_trials
            for example in control["examples"]:
                s, errors, bodies = example["secret"], example["errors"], example["bodies"]
                assert bodies == bodies_for(blocks, s, errors, q)
                output = compile(model, bodies)
                assert output == example["output"]
                actual_error = contract(model["tensor"], *errors)
                assert str(actual_error) == example["actual_integer_error"]
                # Direct full-ciphertext integer phase, independent of phase().
                t, c, b = output
                value = (b+sum(s[i]*c[i] for i in range(n))-
                         sum(s[i]*t[i][j]*s[j] for i in range(n) for j in range(n)))
                assert value % q == (example["target_phase"]+actual_error) % q
                assert example["target_phase"] == weight*math.prod(s[i] for i in support)
                examples += 1
            controls += 1
        linear = case["linear_source_filter"]
        if linear["status"] == "ok":
            matrix = [sum((blocks[r][i] for r in range(3)), []) for i in range(n)]
            assert len(linear["vectors"]) == n
            assert {v["coordinate"] for v in linear["vectors"]} == set(range(n))
            for vector in linear["vectors"]:
                coefficients_ = vector["coefficients"]
                assert len(coefficients_) == 3*m
                assert vector["l1"] == str(sum(map(abs, coefficients_)))
                assert all(sum(a*b for a, b in zip(row, coefficients_)) % q ==
                           q//2*int(i == vector["coordinate"]) for i, row in enumerate(matrix))
                recoveries += 1
            assert linear["guaranteed_key_recovery_radius_one"] == all(
                4*int(v["l1"]) < q for v in linear["vectors"])
    assert result["summary"] == summarize(result["cases"])
    assert not result["production_Lean_changed"]
    assert not result["asymptotic_shortness_theorem"]
    print(json.dumps(dict(replayed_control_certificates=controls, replayed_full_ciphertexts=examples,
                          replayed_linear_recovery_certificates=recoveries,
                          replayed_source_phase_trials=trials,
                          replayed_infeasible_targets=rejections)), flush=True)


def summarize(cases):
    controls = [control for case in cases for control in case.get("controls", [])]
    return dict(cases=len(cases), certified_cases=sum(c["status"] == "certified" for c in cases),
                partial_cases=sum(c["status"] == "partial" for c in cases),
                infeasible_targets=sum(len(c.get("rejected_controls", [])) for c in cases),
                control_certificates=len(controls), phase_trials=sum(c["phase_trials"] for c in controls),
                decoding_margin_failures=sum(c["decoding_margin_failures"] for c in controls),
                radius_one_bootstrap_margins=sum(c["bootstrap_budgets"][0]["strict_budget"] for c in controls),
                guaranteed_linear_key_recovery_cases=sum(c.get("linear_source_filter", {}).get(
                    "guaranteed_key_recovery_radius_one", False) for c in cases))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    mode.add_argument("--verify-solver", action="store_true")
    mode.add_argument("--extend-nonunit", type=Path,
                      help="extend a saved unit-pivot run, preserving its other outcomes")
    parser.add_argument("--case-seconds", type=int, default=90)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if args.verify_existing:
        verify_existing(args.verify_existing)
        return
    if args.verify_solver:
        solver_checks()
        return
    start = time.monotonic()
    identities = identity_checks()
    cases = []
    previous = json.loads(args.extend_nonunit.read_text()) if args.extend_nonunit else None
    grid = list(itertools.product(((3, 2), (4, 3), (6, 4), (8, 5), (8, 6)), (12, 24, 64, 128)))
    if args.quick:
        grid = [((3, 2), 12), ((4, 3), 24)]
    if previous:
        grid = [((c["n"], c["m"]), c["bits"]) for c in previous["cases"]]
    for index, ((n, m), bits) in enumerate(grid):
        if previous and previous["cases"][index]["status"] != "unit_rank_failure":
            saved = previous["cases"][index]
            saved.setdefault("rejected_controls", [])
            # Only the fresh-public-sample count changed; recompute its exact
            # budget arithmetic, preserving every source tape and LLL outcome.
            for control in saved.get("controls", []):
                control["bootstrap_budgets"] = [
                    bootstrap_budget(n, bits, radius**3*int(control["l1"]), radius) for radius in (1, 3)]
            cases.append(saved)
            print(json.dumps(dict(event="preserved_initial_outcome", n=n, m=m, bits=bits,
                                  status=saved["status"])), flush=True)
            continue
        seed = 20261019+1000*n+100*m+bits
        print(json.dumps(dict(event="case_start", n=n, m=m, bits=bits)), flush=True)
        record = bounded_case((n, m, bits, seed), args.case_seconds)
        cases.append(record)
        print(json.dumps(dict(event="case_result", n=n, m=m, bits=bits, status=record["status"],
                              controls=len(record.get("controls", [])))), flush=True)
    result = dict(scope="Three-block positive cubic compiler, finite public tensor-preimage trials; not an FHE theorem",
                  version=2, coefficient_solver="unit fast path plus nonunit modular diagonalization",
                  identity_checks=identities, cases=cases, quick=previous["quick"] if previous else args.quick,
                  summary=summarize(cases),
                  production_Lean_changed=False, asymptotic_shortness_theorem=False,
                  elapsed_seconds=round(time.monotonic()-start, 3))
    if previous:
        result["nonunit_extension"] = dict(
            preserved_cases=sum(c["status"] != "unit_rank_failure" for c in previous["cases"]),
            extended_cases=sum(c["status"] == "unit_rank_failure" for c in previous["cases"]),
            initial_summary=previous["summary"])
    (args.output or args.extend_nonunit).write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result["summary"]), flush=True)


if __name__ == "__main__":
    main()
