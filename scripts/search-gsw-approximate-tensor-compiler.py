#!/usr/bin/env python3
"""Certified approximate cubic compilation; bounded research, not an FHE proof.

Generation optionally uses fpylll. Saved-certificate replay is standard-library
only and independently reconstructs complete ciphertext coordinates. No secret
or source error is an input to the coefficient builder or public compiler.
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
import math
import multiprocessing
from pathlib import Path
import random
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BASE_PATH = HERE / "search-gsw-cubic-tensor-compiler.py"
OLD_PATH = ROOT / "docs/GSWCubicTensorCompilerExploration.json"
spec = importlib.util.spec_from_file_location("gsw_exact_tensor", BASE_PATH)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
SCALES = (8, 2, 32)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cubic_matrix(blocks, q):
    monomials, _, rows = base.coefficients(blocks, q)
    return ([i for i in monomials if len(i) == 3],
            [row for i, row in zip(monomials, rows) if len(i) == 3])


def independent_cubic_matrix(blocks, q):
    """Boolean finite differences, independent of the assignment enumeration."""
    n, m = len(blocks[0]), len(blocks[0][0])
    triples = list(itertools.combinations(range(n), 3))
    rows = []
    for triple in triples:
        row = []
        for position in itertools.product(range(m), repeat=3):
            value = 0
            for degree in (1, 2, 3):
                for subset in itertools.combinations(triple, degree):
                    value += (-1)**(3-degree)*math.prod(sum(blocks[r][i][position[r]] for i in subset)
                                                       for r in range(3))
            row.append(value % q)
        rows.append(row)
    return triples, rows


def certificate(matrix, triples, vector, indices, level, radius, q):
    """Mask-only exact public error certificate, with signed integer rounding."""
    weight = 1 << level
    if not any(vector):
        return zero_certificate(triples, indices, level, q)
    residues = [base.centered(sum(a*b for a, b in zip(row, vector))-
                              weight*int(triple == tuple(indices)), q)
                for triple, row in zip(triples, matrix)]
    quotients = [(r+4)//8 for r in residues]
    remainders = [r-8*d for r, d in zip(residues, quotients)]
    assert all(-4 <= e <= 3 for e in remainders)
    l1 = sum(map(abs, vector))
    discrepancy = sum(abs(d)+abs(e) for d, e in zip(quotients, remainders))
    return dict(r=residues, d=quotients, epsilon=remainders, tensor_l1=str(l1),
                discrepancy_bound=str(discrepancy), J=str(radius**3*l1+discrepancy))


def zero_certificate(triples, indices, level, q):
    r = [base.centered(-(1 << level)*int(i == tuple(indices)), q) for i in triples]
    d = [(x+4)//8 for x in r]
    epsilon = [x-8*y for x, y in zip(r, d)]
    discrepancy = sum(abs(a)+abs(b) for a, b in zip(d, epsilon))
    return dict(r=r, d=d, epsilon=epsilon, tensor_l1="0",
                discrepancy_bound=str(discrepancy), J=str(discrepancy))


def independent_certificate_check(matrix, triples, vector, cert, indices, level, radius, q):
    """Check equations/ranges directly, without the certificate constructor."""
    assert len(vector) == len(matrix[0])
    assert len(cert["r"]) == len(cert["d"]) == len(cert["epsilon"]) == len(triples)
    is_zero = not any(vector)
    for triple, row, residue, quotient, remainder in zip(triples, matrix, cert["r"], cert["d"], cert["epsilon"]):
        total = 0 if is_zero else sum(row[i]*vector[i] for i in range(len(vector)))
        target = (1 << level) if triple == tuple(indices) else 0
        assert (total-target-residue) % q == 0
        assert -(q//2) <= residue < q-q//2
        assert residue == 8*quotient+remainder and -4 <= remainder <= 3
    norm = sum(abs(x) for x in vector)
    discrepancy = sum(abs(x) for x in cert["d"])+sum(abs(x) for x in cert["epsilon"])
    assert cert["tensor_l1"] == str(norm)
    assert cert["discrepancy_bound"] == str(discrepancy)
    assert cert["J"] == str(radius*radius*radius*norm+discrepancy)


def corrected_compile(blocks, bodies, vector, cert, q):
    """Return all T,c,b coordinates; Boolean correction includes the body."""
    n = len(blocks[0])
    if any(vector):
        model = base.preprocess(blocks, vector, q)
        matrix, linear, body = base.compile(model, bodies)
    else:
        matrix, linear, body = [[0]*n for _ in range(n)], [0]*n, 0
    triples = list(itertools.combinations(range(n), 3))
    body -= sum(cert["d"])
    for triple, d in zip(triples, cert["d"]):
        for i in triple:
            linear[i] += 2*d
        for i, j in itertools.combinations(triple, 2):
            matrix[i][j] += 4*d
    return [[[x % q for x in row] for row in matrix], [x % q for x in linear], body % q]


def direct_compile(blocks, bodies, vector, cert, q):
    """Independent unoptimized integer reconstruction, preserving all entries."""
    n, m = len(blocks[0]), len(blocks[0][0])
    tensor = [(position, d) for position, d in zip(itertools.product(range(m), repeat=3), vector) if d]
    monomials = [i for degree in (1, 2, 3) for i in itertools.combinations(range(n), degree)]
    if tensor:
        _, _, rows = base.coefficients(blocks, q)
        polynomial = {support: sum(a*b for a, b in zip(row, vector)) % q
                      for support, row in zip(monomials, rows)}
    else:
        polynomial = dict.fromkeys(monomials, 0)
    body = sum(d*bodies[0][a]*bodies[1][b]*bodies[2][c] for (a, b, c), d in tensor)
    linear = [-sum(d*(blocks[0][i][a]*bodies[1][b]*bodies[2][c]+
                      bodies[0][a]*blocks[1][i][b]*bodies[2][c]+
                      bodies[0][a]*bodies[1][b]*blocks[2][i][c])
                   for (a, b, c), d in tensor)-polynomial[(i,)] for i in range(n)]
    matrix = [[-sum(d*(blocks[0][i][a]*blocks[1][j][b]*bodies[2][c]+
                       blocks[0][i][a]*bodies[1][b]*blocks[2][j][c]+
                       bodies[0][a]*blocks[1][i][b]*blocks[2][j][c])
                    for (a, b, c), d in tensor) for j in range(n)] for i in range(n)]
    for i, j in itertools.combinations(range(n), 2):
        matrix[i][j] += polynomial[(i, j)]
    body -= sum(cert["d"])
    triples = [i for i in monomials if len(i) == 3]
    for triple, d in zip(triples, cert["d"]):
        for i in triple:
            linear[i] += 2*d
        for i, j in itertools.combinations(triple, 2):
            matrix[i][j] += 4*d
    return [[[x % q for x in row] for row in matrix], [x % q for x in linear], body % q]


def add_ciphertexts(first, second, q):
    return [[[int(a+b) % q for a, b in zip(row, other)] for row, other in zip(first[0], second[0])],
            [(a+b) % q for a, b in zip(first[1], second[1])], (first[2]+second[2]) % q]


def compile_public_view(table, blocks, bodies, vector, cert, zero, q):
    """The published table is retained; no private oracle input is accepted."""
    return dict(public_table=table,
                control=add_ciphertexts(corrected_compile(blocks, bodies, vector, cert, q), zero, q))


def zero_from_public_source(matrix, mask, outputs, body, q):
    """Ordinary-transcript adapter, requiring neither the secret nor errors."""
    return [matrix, [(x-a) % q for x, a in zip(outputs, mask)], body % q]


def zero_source(secret, q, radius, rng):
    """Oracle-side fixture generation of an ordinary-source recursive zero."""
    n = len(secret)
    matrix = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
    mask = [rng.randrange(q) for _ in range(n)]
    errors = [rng.randint(-radius, radius) for _ in range(n+1)]
    outputs = [(sum(secret[i]*matrix[i][j] for i in range(n))+errors[j]) % q for j in range(n)]
    body = (sum(s*a for s, a in zip(secret, mask))+errors[-1]) % q
    ciphertext = zero_from_public_source(matrix, mask, outputs, body, q)
    return ciphertext, dict(matrix=matrix, mask=mask, outputs=outputs, body=body, errors=errors)


def replay_zero(witness, secret, q, radius):
    n = len(secret)
    assert len(witness["matrix"]) == n and all(len(row) == n for row in witness["matrix"])
    assert len(witness["mask"]) == len(witness["outputs"]) == n
    assert len(witness["errors"]) == n+1
    assert all(abs(e) <= radius for e in witness["errors"])
    assert witness["outputs"] == [(sum(secret[i]*witness["matrix"][i][j] for i in range(n))+
                                    witness["errors"][j]) % q for j in range(n)]
    assert witness["body"] == (sum(s*a for s, a in zip(secret, witness["mask"]))+
                                witness["errors"][-1]) % q
    return zero_from_public_source(witness["matrix"], witness["mask"], witness["outputs"], witness["body"], q)


def check_fixture(blocks, vector, cert, indices, level, radius, secret, errors, rng):
    n, q = len(secret), rng[0]
    random_source = rng[1]
    bodies = base.bodies_for(blocks, secret, errors, q)
    zero, witness = zero_source(secret, q, radius, random_source)
    table_pairs = [zero_source(secret, q, radius, random_source) for _ in range(3)]
    table = [pair[0] for pair in table_pairs]
    table_snapshot = json.dumps(table)
    view = compile_public_view(table, blocks, bodies, vector, cert, zero, q)
    assert view["public_table"] is table and json.dumps(table) == table_snapshot
    direct = direct_compile(blocks, bodies, vector, cert, q)
    assert direct == corrected_compile(blocks, bodies, vector, cert, q)
    assert view["control"] == add_ciphertexts(direct, zero, q)
    positions = list(itertools.product(range(len(blocks[0][0])), repeat=3))
    residual = sum(t*errors[0][a]*errors[1][b]*errors[2][c] for (a, b, c), t in zip(positions, vector))
    triples = list(itertools.combinations(range(n), 3))
    residual += sum(d*math.prod(2*secret[i]-1 for i in triple)+e*math.prod(secret[i] for i in triple)
                    for triple, d, e in zip(triples, cert["d"], cert["epsilon"]))
    assert abs(residual) <= int(cert["J"])
    zero_error = witness["errors"][-1]+sum(s*e for s, e in zip(secret, witness["errors"][:-1]))
    target = (1 << level)*math.prod(secret[i] for i in indices)
    t, c, b = view["control"]
    actual = b+sum(secret[i]*c[i] for i in range(n))
    actual -= sum(secret[i]*t[i][j]*secret[j] for i in range(n) for j in range(n))
    assert actual % q == (target+residual+zero_error) % q
    assert abs(residual+zero_error) <= int(cert["J"])+(n+1)*radius
    return dict(secret=list(secret), errors=errors, bodies=bodies, zero_witness=witness,
                table_witnesses=[pair[1] for pair in table_pairs], output=view["control"],
                integer_residual=str(residual), zero_error=zero_error,
                decoding_margin_failure=16*abs(base.centered(residual+zero_error, q)) >= q)


def boundary_checks():
    rounding = 0
    for r in range(-65536, 65537):
        d = (r+4)//8
        epsilon = r-8*d
        assert -4 <= epsilon <= 3 and r == 8*d+epsilon
        rounding += 1
    truth = 0
    for d in range(-16, 17):
        for s in itertools.product((0, 1), repeat=3):
            left = 8*d*math.prod(s)-4*d*sum(s[i]*s[j] for i, j in itertools.combinations(range(3), 2))
            left += 2*d*sum(s)-d
            assert left == d*math.prod(2*x-1 for x in s)
            truth += 1
    phase_checks = 0
    # All binary keys, ternary errors, and low/top weights, including q=2.
    for q in (2, 8, 32, 97):
        rng = random.Random(20261021+q)
        blocks = [[[rng.randrange(q) for _ in range(2)] for _ in range(3)] for _ in range(3)]
        triples, matrix = cubic_matrix(blocks, q)
        vector = [rng.randrange(-2, 3) for _ in range(8)]
        for weight in (1, q//2):
            # Non-power-of-two fixture still uses an actual power-of-two weight.
            level = weight.bit_length()-1
            cert = certificate(matrix, triples, vector, (0, 1, 2), level, 1, q)
            model = base.preprocess(blocks, vector, q)
            for s in itertools.product((0, 1), repeat=3):
                for raw in itertools.product((-1, 0, 1), repeat=6):
                    errors = [raw[i*2:i*2+2] for i in range(3)]
                    bodies = base.bodies_for(blocks, s, errors, q)
                    t, c, b = base.compile(model, bodies)
                    d = cert["d"][0]
                    b -= d
                    c = [x+2*d for x in c]
                    for i, j in itertools.combinations(range(3), 2):
                        t[i][j] += 4*d
                    actual = b+sum(x*y for x, y in zip(s, c))
                    actual -= sum(s[i]*t[i][j]*s[j] for i in range(3) for j in range(3))
                    residual = sum(v*errors[0][a]*errors[1][b_]*errors[2][c_]
                                   for (a, b_, c_), v in zip(itertools.product(range(2), repeat=3), vector))
                    residual += d*math.prod(2*x-1 for x in s)+cert["epsilon"][0]*math.prod(s)
                    assert actual % q == ((1 << level)*math.prod(s)+residual) % q
                    assert abs(residual) <= int(cert["J"])
                    phase_checks += 1
    for bits in (4, 12, 24, 64, 128):
        q = 1 << bits
        top = zero_certificate([(0, 1, 2)], (0, 1, 2), bits-1, q)
        assert int(top["J"]) == q//16
    return dict(signed_rounding_cases=rounding, centered_cubic_truth_cases=truth,
                exhaustive_phase_cases=phase_checks, top_zero_tensor_bound="q/16")


def lattice_worker(connection, blocks, bits, radius, scale, requests):
    try:
        from fpylll import FPLLL, GSO, IntegerMatrix, LLL
        q = 1 << bits
        triples, matrix = cubic_matrix(blocks, q)
        width, height = len(matrix[0]), len(matrix)
        alpha = scale*radius**3
        raw = [[alpha*int(i == j) for j in range(width)]+[matrix[k][i] for k in range(height)]
               for i in range(width)]
        raw += [[0]*width+[q*int(i == j) for j in range(height)] for i in range(height)]
        lattice = IntegerMatrix.from_matrix(raw)
        FPLLL.set_precision(max(192, 4*bits))
        started = time.monotonic()
        LLL.reduction(lattice, delta=0.75)
        reduction_elapsed = round(time.monotonic()-started, 3)
        connection.send(dict(event="reduction_finished", reduction_seconds=reduction_elapsed))
        basis = [[int(lattice[i, j]) for j in range(width+height)] for i in range(width+height)]
        # Certify membership of the entire reduced basis in the input lattice.
        for row in basis:
            assert all(x % alpha == 0 for x in row[:width])
            v = [x//alpha for x in row[:width]]
            assert all((sum(a*b for a, b in zip(crow, v))-row[width+i]) % q == 0
                       for i, crow in enumerate(matrix))
        gso = GSO.Mat(lattice, float_type="mpfr", update=True)
        connection.send(dict(event="basis_ready", dimension=width+height, alpha=str(alpha),
                             reduction_seconds=reduction_elapsed))
        batch = []
        for indices, level in requests:
            target = [0]*width+[(1 << level)*int(i == tuple(indices)) for i in triples]
            combination = tuple(map(int, gso.babai(target)))
            nearby = [sum(combination[i]*basis[i][j] for i in range(width+height))
                      for j in range(width+height)]
            assert all(x % alpha == 0 for x in nearby[:width])
            vector = [x//alpha for x in nearby[:width]]
            assert all((sum(a*b for a, b in zip(row, vector))-nearby[width+i]) % q == 0
                       for i, row in enumerate(matrix))
            cert = certificate(matrix, triples, vector, indices, level, radius, q)
            batch.append(dict(indices=list(indices), level=level, coefficients=vector, J=cert["J"]))
            if len(batch) >= 16:
                connection.send(dict(event="candidates", values=batch))
                batch = []
        if batch:
            connection.send(dict(event="candidates", values=batch))
        connection.send(dict(event="complete"))
    except Exception as error:
        connection.send(dict(event="error", reason=type(error).__name__+": "+str(error)))
    finally:
        connection.close()


def recovery_worker(connection, blocks, bits):
    try:
        connection.send(dict(event="recovery", value=base.linear_recovery(blocks, 1 << bits, bits)))
    except Exception as error:
        connection.send(dict(event="error", reason=type(error).__name__+": "+str(error)))
    finally:
        connection.close()


def run_worker(target, args, reduction_seconds, deadline, consume):
    """Kill only this task's worker; preserve every delivered exact certificate."""
    context = multiprocessing.get_context("fork")
    receiver, sender = context.Pipe(duplex=False)
    process = context.Process(target=target, args=(sender, *args))
    started = time.monotonic()
    process.start()
    sender.close()
    ready = False
    status = "worker_exit"
    info = {}
    try:
        while True:
            now = time.monotonic()
            limit = deadline if ready else min(deadline, started+reduction_seconds)
            if now >= limit:
                status = "case_timeout" if now >= deadline else "reduction_timeout"
                break
            if receiver.poll(min(0.2, limit-now)):
                try:
                    event = receiver.recv()
                except EOFError:
                    break
                if event["event"] in ("basis_ready", "reduction_finished"):
                    ready = True
                    info.update({k: v for k, v in event.items() if k != "event"})
                elif event["event"] in ("complete", "recovery"):
                    if event["event"] == "recovery":
                        consume(event)
                    status = "complete"
                    break
                elif event["event"] == "error":
                    status = "worker_error"
                    info["reason"] = event["reason"]
                    break
                else:
                    consume(event)
            elif not process.is_alive():
                # Drain already buffered messages before treating exit as terminal.
                if not receiver.poll():
                    break
        if process.is_alive():
            process.join(0.2 if status == "complete" else 0)
            if process.is_alive():
                process.terminate()
        process.join(3)
        if process.is_alive():
            process.kill()
            process.join()
        return dict(status=status, elapsed_seconds=round(time.monotonic()-started, 3), **info)
    finally:
        if process.is_alive():
            process.terminate()
            process.join(3)
            if process.is_alive():
                process.kill()
                process.join()
        receiver.close()


def case_blocks(n, m, bits):
    seed = 20261019+1000*n+100*m+bits
    rng = random.Random(seed)
    return seed, [[[rng.randrange(1 << bits) for _ in range(m)] for _ in range(n)] for _ in range(3)]


def cached_case(old, n, m, bits, blocks):
    return next((c for c in old["cases"] if (c["n"], c["m"], c["bits"]) == (n, m, bits)
                 and c.get("blocks") == blocks), None)


def budget_info(n, bits, radius, J):
    # Include the independent recursive-zero source's actual supported error.
    return base.bootstrap_budget(n, bits, J+(n+1)*radius, radius)


def independent_budget_check(value, n, bits, radius, J):
    rows = n*n+n+1
    growth = rows*bits
    lookup = 1
    while lookup < 8*rows:
        lookup *= 2
    bound = J+(n+1)*radius
    public_samples = growth+2*bits+17
    fresh = public_samples*(n+1)*radius
    output = lookup*rows*growth*(growth+1)*bound
    budget = lookup*(growth+1)*output
    assert fresh <= output
    assert value == dict(control_bound=str(bound), common_bound=str(bound), public_samples=public_samples,
                         fresh_encryption_bound=str(fresh), budget=str(budget), modulus=str(1 << bits),
                         strict_budget=budget < 1 << bits, lookup=lookup)


def family_audit():
    records = []
    for parameter in (1, 2, 4, 8, 16, 32, 64):
        s = parameter+1
        n, bits, E = 2*s**5, s*s, 1 << s
        m = (3*n+3)//4
        rows = n*n+n+1
        growth = rows*bits
        lookup = 1 << (8*rows-1).bit_length()
        factor = lookup**2*rows*growth*(growth+1)**2
        control_budget = ((1 << bits)-1)//(4*factor)
        records.append(dict(parameter=parameter, n=n, m=m, bits=bits, radius=str(E),
                            augmented_dimension=m**3+math.comb(n, 3),
                            control_budget=str(control_budget), zero_source_bound=str((n+1)*E),
                            positive_search_threshold=control_budget >= (n+1)*E,
                            all_cubic_slots=math.comb(n, 3)*bits))
    # If per-block success >= 1/4 were proved, 4*s trials suffice. This checks
    # only the amplification arithmetic, never that missing success premise.
    assert 3**4 < 2**7
    return dict(parameter_records=records, proved_complete_table_success_probability=False,
                proved_polynomial_time_implementation=False, new_hardness_assumption=False,
                amplification_arithmetic="(3/4)^(4*(parameter+1)) <= 2^(-(parameter+1))",
                ordinary_LWE_security_reduction_instantiated=False, production_Lean_changed=False,
                gate="unproved; finite success is not a certificate of this theorem")


def chosen_entry(entry):
    candidates = entry["candidates"]
    # Earlier insertion wins a tie: zero, cached exact, scale8, scale2, scale32.
    index = min(range(len(candidates)), key=lambda i: (int(candidates[i]["J"]), i))
    return index, candidates[index]


def candidate_vector(candidate, width):
    return [0]*width if candidate["method"] == "zero" else candidate["coefficients"]


def finish_case(case):
    n, m, bits, blocks = case["n"], case["m"], case["bits"], case["blocks"]
    q = 1 << bits
    triples, matrix = cubic_matrix(blocks, q)
    width = m**3
    for run in case["radii"]:
        radius = run["radius"]
        for entry in run["entries"]:
            index, best = chosen_entry(entry)
            entry["selected_index"] = index
            vector = candidate_vector(best, width)
            cert = certificate(matrix, triples, vector, entry["indices"], entry["level"], radius, q)
            assert cert["J"] == best["J"]
            entry["certificate"] = cert
        worst = max(int(e["certificate"]["J"]) for e in run["entries"])
        run["complete_table_budget"] = budget_info(n, bits, radius, worst)
        run["optimizer_complete"] = all(a["status"] == "complete" for a in run["attempts"]) and len(run["attempts"]) == 3
        linear = case["linear_source_filter"]
        run["guaranteed_source_key_recovery"] = linear["status"] == "ok" and len(linear["vectors"]) == n and all(
            4*radius*int(v["l1"]) < q for v in linear["vectors"])
        # Marginal level/triple coverage is explicit; certificate coverage is
        # the full Cartesian product. These are not described as the same check.
        count = max(bits, len(triples))
        fixtures = []
        rng = random.Random(case["seed"]+19*radius)
        entries = {(tuple(e["indices"]), e["level"]): e for e in run["entries"]}
        for i in range(count):
            indices, level = triples[i % len(triples)], i % bits
            entry = entries[indices, level]
            best = entry["candidates"][entry["selected_index"]]
            vector = candidate_vector(best, width)
            if i % 4 == 0:
                secret = (1,)*n
            elif i % 4 == 1:
                secret = tuple(j % 2 for j in range(n))
            elif i % 4 == 2:
                secret = tuple(int(j == i % n) for j in range(n))
            else:
                secret = tuple(rng.randrange(2) for _ in range(n))
            errors = [[rng.randint(-radius, radius) for _ in range(m)] for _ in range(3)]
            value = check_fixture(blocks, vector, entry["certificate"], indices, level, radius,
                                  secret, errors, (q, rng))
            fixtures.append(dict(indices=list(indices), level=level, **value))
        assert {f["level"] for f in fixtures} == set(range(bits))
        assert {tuple(f["indices"]) for f in fixtures} == set(triples)
        run["fixtures"] = fixtures
        run["fixture_level_coverage"] = list(range(bits))
        run["fixture_triple_coverage"] = [list(i) for i in triples]
    return case


def run_case(n, bits, old, config, global_deadline):
    m = (3*n+3)//4
    seed, blocks = case_blocks(n, m, bits)
    q = 1 << bits
    triples, matrix = cubic_matrix(blocks, q)
    levels = [bits-1, bits-2]+list(range(bits-2))
    requests = [(indices, level) for indices in triples for level in levels]
    cached = cached_case(old, n, m, bits, blocks)
    cached_controls = {(tuple(e["indices"]), e["level"]): e for e in cached.get("controls", [])} if cached else {}
    family_radius = 1 << math.isqrt(bits)
    if math.isqrt(bits)**2 < bits:
        family_radius *= 2
    radii = list(dict.fromkeys((family_radius, 1, 3)))
    started = time.monotonic()
    deadline = min(global_deadline, started+config["case_seconds"])
    case = dict(n=n, m=m, bits=bits, seed=seed, blocks=blocks, expected_slots=len(requests),
                linear_source_filter=dict(status="unknown", vectors=[]), radii=[])
    if cached and cached.get("linear_source_filter", {}).get("status") == "ok":
        case["linear_source_filter"] = cached["linear_source_filter"]
        case["recovery_origin"] = "saved matching-mask certificate; no repeated solve"
    elif time.monotonic() < deadline:
        def recovery(event):
            case["linear_source_filter"] = event["value"]
        case["recovery_attempt"] = run_worker(recovery_worker, (blocks, bits), 15, deadline, recovery)
    for radius in radii:
        entries = {}
        for indices, level in requests:
            zero = zero_certificate(triples, indices, level, q)
            candidates = [dict(method="zero", J=zero["J"])]
            if (indices, level) in cached_controls:
                vector = cached_controls[indices, level]["coefficients"]
                cert = certificate(matrix, triples, vector, indices, level, radius, q)
                assert all(r == 0 for r in cert["r"])
                candidates.append(dict(method="cached_exact", coefficients=vector, J=cert["J"]))
            entries[indices, level] = dict(indices=list(indices), level=level, candidates=candidates)
        run = dict(radius=radius, family_scaled_radius=radius == family_radius, entries=list(entries.values()), attempts=[])
        for scale in SCALES:
            if time.monotonic() >= deadline:
                run["attempts"].append(dict(scale=scale, status="not_started_case_budget", candidate_count=0))
                continue
            count = [0]
            def consume(event):
                assert event["event"] == "candidates"
                for value in event["values"]:
                    key = tuple(value["indices"]), value["level"]
                    entries[key]["candidates"].append(dict(method=f"scale{scale}",
                                                          coefficients=value["coefficients"], J=value["J"]))
                    count[0] += 1
            attempt = run_worker(lattice_worker, (blocks, bits, radius, scale, requests),
                                 config["reduction_seconds"], deadline, consume)
            attempt.update(scale=scale, candidate_count=count[0])
            if attempt["status"] == "complete":
                assert count[0] == len(requests)
            run["attempts"].append(attempt)
            print(json.dumps(dict(event="lattice_result", n=n, bits=bits, radius=radius,
                                  **attempt)), flush=True)
        case["radii"].append(run)
    case["search_elapsed_seconds"] = round(time.monotonic()-started, 3)
    finish_case(case)
    case["total_elapsed_seconds"] = round(time.monotonic()-started, 3)
    return case


def regression(old, config, deadline):
    records = []
    phase_trials = 0
    for case in old["cases"]:
        n, m, bits = case["n"], case["m"], case["bits"]
        if n not in (3, 4) or bits not in (24, 64):
            continue
        blocks, q = case["blocks"], 1 << bits
        triples, matrix = cubic_matrix(blocks, q)
        requests = [((0, 1, 2), bits-2), ((0, 1, 2), bits-1)]
        for radius in (1, 3):
            received = []
            attempt = run_worker(lattice_worker, (blocks, bits, radius, 8, requests),
                                 config["reduction_seconds"], deadline,
                                 lambda event: received.extend(event["values"]))
            assert attempt["status"] == "complete" and len(received) == 2
            for value in received:
                cert = certificate(matrix, triples, value["coefficients"], value["indices"],
                                   value["level"], radius, q)
                exact = next(e for e in case["controls"] if e["indices"] == value["indices"] and e["level"] == value["level"])
                exact_bound = radius**3*int(exact["l1"])
                fixtures = []
                rng = random.Random(191+radius+value["level"])
                for secret in itertools.product((0, 1), repeat=n):
                    errors = [[rng.randint(-radius, radius) for _ in range(m)] for _ in range(3)]
                    fixtures.append(check_fixture(blocks, value["coefficients"], cert, value["indices"],
                                                  value["level"], radius, secret, errors, (q, rng)))
                    phase_trials += 1
                records.append(dict(n=n, m=m, bits=bits, radius=radius, **value, certificate=cert,
                                    exact_bound=str(exact_bound), improved=int(cert["J"]) < exact_bound,
                                    fixtures=fixtures))
    assert len(records) == 16 and phase_trials == 192
    return dict(records=records, comparisons=16, improved=sum(r["improved"] for r in records),
                phase_trials=phase_trials, interpretation="known easy sources; algebra/optimization evidence only")


def summarize(result):
    cases = result["cases"]
    radii = [r for c in cases for r in c["radii"]]
    entries = [e for r in radii for e in r["entries"]]
    attempts = [a for r in radii for a in r["attempts"]]
    return dict(parameter_cases=len(cases), radius_tables=len(radii),
                full_slot_certificates=len(entries), approximate_candidates=sum(
                    a["candidate_count"] for a in attempts),
                completed_lattice_searches=sum(a["status"] == "complete" for a in attempts),
                reduction_timeouts=sum(a["status"] == "reduction_timeout" for a in attempts),
                case_timeouts=sum(a["status"] == "case_timeout" for a in attempts),
                unstarted_searches=sum(a["status"] == "not_started_case_budget" for a in attempts),
                worker_errors=sum(a["status"] in ("worker_error", "worker_exit") for a in attempts),
                complete_optimizer_tables=sum(r["optimizer_complete"] for r in radii),
                finite_table_budget_passes=sum(r["complete_table_budget"]["strict_budget"] for r in radii),
                budget_passes_without_source_recovery=sum(r["complete_table_budget"]["strict_budget"] and not
                                                         r["guaranteed_source_key_recovery"] for r in radii),
                sampled_complete_view_phases=sum(len(r["fixtures"]) for r in radii),
                sampled_decoding_margin_failures=sum(f["decoding_margin_failure"] for r in radii for f in r["fixtures"]))


def atomic_write(path, result):
    temporary = path.with_suffix(path.suffix+".tmp")
    temporary.write_text(json.dumps(result, separators=(",", ":"))+"\n")
    temporary.replace(path)


def verify_fixture(fixture, blocks, vector, cert, indices, level, radius, q):
    secret, errors = fixture["secret"], fixture["errors"]
    n, m = len(secret), len(blocks[0][0])
    assert set(secret) <= {0, 1} and len(secret) == len(blocks[0])
    assert len(errors) == 3 and all(len(e) == m for e in errors)
    assert all(abs(e) <= radius for row in errors for e in row)
    assert fixture["bodies"] == [[(sum(secret[i]*blocks[r][i][j] for i in range(n))+errors[r][j]) % q
                                   for j in range(m)] for r in range(3)]
    zero = replay_zero(fixture["zero_witness"], secret, q, radius)
    assert len(fixture["table_witnesses"]) == 3
    table = [replay_zero(w, secret, q, radius) for w in fixture["table_witnesses"]]
    output = add_ciphertexts(direct_compile(blocks, fixture["bodies"], vector, cert, q), zero, q)
    assert output == fixture["output"]
    view = compile_public_view(table, blocks, fixture["bodies"], vector, cert, zero, q)
    assert view["public_table"] is table and view["control"] == output
    residual = sum(t*errors[0][a]*errors[1][b]*errors[2][c] for (a, b, c), t in
                   zip(itertools.product(range(m), repeat=3), vector))
    triples, _ = cubic_matrix(blocks, q)
    residual += sum(d*math.prod(2*secret[i]-1 for i in triple)+e*math.prod(secret[i] for i in triple)
                    for triple, d, e in zip(triples, cert["d"], cert["epsilon"]))
    assert str(residual) == fixture["integer_residual"] and abs(residual) <= int(cert["J"])
    zero_error = fixture["zero_witness"]["errors"][-1]+sum(s*e for s, e in zip(secret, fixture["zero_witness"]["errors"][:-1]))
    assert zero_error == fixture["zero_error"]
    t, c, b = output
    direct_phase = b+sum(secret[i]*c[i] for i in range(n))
    direct_phase -= sum(secret[i]*t[i][j]*secret[j] for i in range(n) for j in range(n))
    assert direct_phase % q == ((1 << level)*math.prod(secret[i] for i in indices)+residual+zero_error) % q
    assert fixture["decoding_margin_failure"] == (16*abs(base.centered(residual+zero_error, q)) >= q)


def verify_existing(path):
    result = json.loads(path.read_text())
    old = json.loads(OLD_PATH.read_text())
    assert result["version"] == 1 and result["provenance"] == dict(exact_script_sha256=sha(BASE_PATH), exact_artifact_sha256=sha(OLD_PATH))
    assert result["boundary_checks"] == boundary_checks()
    assert result["family_audit"] == family_audit()
    assert result["config"]["scales"] == list(SCALES)
    assert result["config"]["table_fixture_columns"] == 3
    expected_grid = list(itertools.product((3, 4, 6, 8), (12, 24, 64, 128)))
    if result["config"]["quick"]:
        expected_grid = [(3, 12), (4, 24)]
    assert result["planned_grid"] == [list(pair) for pair in expected_grid]
    assert [(c["n"], c["bits"]) for c in result["cases"]] == expected_grid[:len(result["cases"])]
    if result["status"] == "complete_bounded_study":
        assert len(result["cases"]) == len(expected_grid)
    comparisons = improvements = phases = candidates = certificates = recoveries = 0
    for record in result["regression"]["records"]:
        case = next(c for c in old["cases"] if (c["n"], c["m"], c["bits"]) == (record["n"], record["m"], record["bits"]))
        q = 1 << record["bits"]
        triples, matrix = cubic_matrix(case["blocks"], q)
        assert (triples, matrix) == independent_cubic_matrix(case["blocks"], q)
        cert = certificate(matrix, triples, record["coefficients"], record["indices"], record["level"], record["radius"], q)
        independent_certificate_check(matrix, triples, record["coefficients"], record["certificate"], record["indices"], record["level"], record["radius"], q)
        assert cert == record["certificate"] and cert["J"] == record["J"]
        exact = next(e for e in case["controls"] if e["indices"] == record["indices"] and e["level"] == record["level"])
        assert record["exact_bound"] == str(record["radius"]**3*int(exact["l1"]))
        assert record["improved"] == (int(cert["J"]) < int(record["exact_bound"]))
        assert {tuple(f["secret"]) for f in record["fixtures"]} == set(itertools.product((0, 1), repeat=record["n"]))
        rng = random.Random(191+record["radius"]+record["level"])
        for secret, f in zip(itertools.product((0, 1), repeat=record["n"]), record["fixtures"]):
            assert f["secret"] == list(secret)
            assert f["errors"] == [[rng.randint(-record["radius"], record["radius"]) for _ in range(record["m"])] for _ in range(3)]
            assert zero_source(secret, q, record["radius"], rng)[1] == f["zero_witness"]
            assert [zero_source(secret, q, record["radius"], rng)[1] for _ in range(3)] == f["table_witnesses"]
            verify_fixture(f, case["blocks"], record["coefficients"], cert, record["indices"], record["level"], record["radius"], q)
            phases += 1
        comparisons += 1
        improvements += record["improved"]
    assert (comparisons, improvements, phases) == (16, result["regression"]["improved"], 192)
    assert result["regression"]["comparisons"] == comparisons and result["regression"]["phase_trials"] == phases
    assert len({(r["n"], r["m"], r["bits"], r["radius"], r["level"]) for r in result["regression"]["records"]}) == 16
    for case in result["cases"]:
        n, m, bits = case["n"], case["m"], case["bits"]
        q = 1 << bits
        assert m == (3*n+3)//4
        assert (case["seed"], case["blocks"]) == case_blocks(n, m, bits)
        triples, matrix = cubic_matrix(case["blocks"], q)
        assert (triples, matrix) == independent_cubic_matrix(case["blocks"], q)
        expected = {(t, level) for t in triples for level in range(bits)}
        assert case["expected_slots"] == len(expected)
        family_radius = 1 << math.isqrt(bits)
        if math.isqrt(bits)**2 < bits:
            family_radius *= 2
        assert [r["radius"] for r in case["radii"]] == list(dict.fromkeys((family_radius, 1, 3)))
        cached = cached_case(old, n, m, bits, case["blocks"])
        linear = case["linear_source_filter"]
        if linear["status"] == "ok":
            assert len(linear["vectors"]) == n and {v["coordinate"] for v in linear["vectors"]} == set(range(n))
            masks = [sum((case["blocks"][r][i] for r in range(3)), []) for i in range(n)]
            for v in linear["vectors"]:
                assert len(v["coefficients"]) == 3*m and v["l1"] == str(sum(map(abs, v["coefficients"])))
                assert all(sum(a*b for a, b in zip(row, v["coefficients"])) % q == q//2*int(i == v["coordinate"])
                           for i, row in enumerate(masks))
                recoveries += 1
        for run in case["radii"]:
            E = run["radius"]
            assert run["family_scaled_radius"] == (E == family_radius)
            assert {(tuple(e["indices"]), e["level"]) for e in run["entries"]} == expected
            assert len(run["entries"]) == len(expected)
            counts = {scale: 0 for scale in SCALES}
            lookup = {}
            for entry in run["entries"]:
                methods = [c["method"] for c in entry["candidates"]]
                assert methods[0] == "zero" and len(methods) == len(set(methods))
                for candidate in entry["candidates"]:
                    vector = candidate_vector(candidate, m**3)
                    assert len(vector) == m**3
                    cert = certificate(matrix, triples, vector, entry["indices"], entry["level"], E, q)
                    independent_certificate_check(matrix, triples, vector, cert, entry["indices"], entry["level"], E, q)
                    assert cert["J"] == candidate["J"]
                    if candidate["method"].startswith("scale"):
                        scale = int(candidate["method"][5:])
                        assert scale in SCALES
                        counts[scale] += 1
                        candidates += 1
                    elif candidate["method"] == "cached_exact":
                        assert cached is not None
                        original = next(c for c in cached["controls"] if c["indices"] == entry["indices"] and c["level"] == entry["level"])
                        assert vector == original["coefficients"] and all(x == 0 for x in cert["r"])
                    else:
                        assert candidate["method"] == "zero"
                index, best = chosen_entry(entry)
                assert entry["selected_index"] == index
                vector = candidate_vector(best, m**3)
                independent_certificate_check(matrix, triples, vector, entry["certificate"], entry["indices"], entry["level"], E, q)
                assert entry["certificate"] == certificate(matrix, triples, vector, entry["indices"], entry["level"], E, q)
                lookup[tuple(entry["indices"]), entry["level"]] = entry
                certificates += 1
            assert [a["scale"] for a in run["attempts"]] == list(SCALES)
            for attempt in run["attempts"]:
                assert attempt["candidate_count"] == counts[attempt["scale"]]
                if attempt["status"] == "complete":
                    assert attempt["candidate_count"] == len(expected)
            complete = all(a["status"] == "complete" for a in run["attempts"])
            assert run["optimizer_complete"] == complete
            worst = max(int(e["certificate"]["J"]) for e in run["entries"])
            assert run["complete_table_budget"] == budget_info(n, bits, E, worst)
            independent_budget_check(run["complete_table_budget"], n, bits, E, worst)
            recovery = linear["status"] == "ok" and len(linear["vectors"]) == n and all(4*E*int(v["l1"]) < q for v in linear["vectors"])
            assert run["guaranteed_source_key_recovery"] == recovery
            assert {f["level"] for f in run["fixtures"]} == set(range(bits))
            assert {tuple(f["indices"]) for f in run["fixtures"]} == set(triples)
            assert run["fixture_level_coverage"] == list(range(bits))
            assert run["fixture_triple_coverage"] == [list(t) for t in triples]
            assert len(run["fixtures"]) == max(bits, len(triples))
            rng = random.Random(case["seed"]+19*E)
            for i, f in enumerate(run["fixtures"]):
                assert (tuple(f["indices"]), f["level"]) == (triples[i % len(triples)], i % bits)
                if i % 4 == 0:
                    secret = (1,)*n
                elif i % 4 == 1:
                    secret = tuple(j % 2 for j in range(n))
                elif i % 4 == 2:
                    secret = tuple(int(j == i % n) for j in range(n))
                else:
                    secret = tuple(rng.randrange(2) for _ in range(n))
                assert f["secret"] == list(secret)
                assert f["errors"] == [[rng.randint(-E, E) for _ in range(m)] for _ in range(3)]
                assert zero_source(secret, q, E, rng)[1] == f["zero_witness"]
                assert [zero_source(secret, q, E, rng)[1] for _ in range(3)] == f["table_witnesses"]
                entry = lookup[tuple(f["indices"]), f["level"]]
                best = entry["candidates"][entry["selected_index"]]
                verify_fixture(f, case["blocks"], candidate_vector(best, m**3), entry["certificate"], f["indices"], f["level"], E, q)
                phases += 1
        print(json.dumps(dict(event="replayed_case", n=n, bits=bits, selected_certificates=certificates,
                              approximate_candidates=candidates, full_view_phases=phases)), flush=True)
    assert result["summary"] == summarize(result)
    assert result["status"] in ("complete_bounded_study", "global_budget_exhausted")
    print(json.dumps(dict(replayed_approximate_candidates=candidates, replayed_selected_certificates=certificates,
                          replayed_full_view_phases=phases, replayed_source_preimages=recoveries,
                          regression_improvements=improvements)), flush=True)


def runner_checks():
    """Exercise live worker timeouts, retained partial output and certificate rejection."""
    def slow(sender):
        time.sleep(2)

    def partial(sender):
        sender.send(dict(event="reduction_finished", reduction_seconds=0.0))
        sender.send(dict(event="candidates", values=[dict(delivered=True)]))
        time.sleep(2)

    def failed(sender):
        sender.send(dict(event="error", reason="deliberate runner fixture"))

    seen = []
    value = run_worker(slow, (), 0.2, time.monotonic()+1, seen.append)
    assert value["status"] == "reduction_timeout" and not seen
    value = run_worker(partial, (), 0.2, time.monotonic()+0.5, seen.append)
    assert value["status"] == "case_timeout" and seen == [dict(event="candidates", values=[dict(delivered=True)])]
    value = run_worker(failed, (), 0.2, time.monotonic()+1, seen.append)
    assert value["status"] == "worker_error"
    triples, matrix, vector = [(0, 1, 2)], [[1, 2]], [3, 4]
    cert = certificate(matrix, triples, vector, (0, 1, 2), 4, 1, 32)
    independent_certificate_check(matrix, triples, vector, cert, (0, 1, 2), 4, 1, 32)
    rejected = 0
    for field in ("r", "d", "epsilon"):
        bad = {**cert, field: [cert[field][0]+1]}
        try:
            independent_certificate_check(matrix, triples, vector, bad, (0, 1, 2), 4, 1, 32)
        except AssertionError:
            rejected += 1
        else:
            raise AssertionError("malformed certificate accepted")
    print(json.dumps(dict(worker_lifecycle_fixtures=3, malformed_certificates_rejected=rejected)), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--verify-runner", action="store_true")
    parser.add_argument("--reduction-seconds", type=float, default=60)
    parser.add_argument("--case-seconds", type=float, default=180)
    parser.add_argument("--global-seconds", type=float, default=7200)
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()
    if args.verify_existing:
        verify_existing(args.verify_existing)
        return
    if args.self_test:
        print(json.dumps(boundary_checks()), flush=True)
        return
    if args.verify_runner:
        runner_checks()
        return
    assert args.reduction_seconds > 0 and args.case_seconds > 0 and args.global_seconds > 0
    started = time.monotonic()
    deadline = started+args.global_seconds
    config = dict(reduction_seconds=args.reduction_seconds, case_seconds=args.case_seconds,
                  global_seconds=args.global_seconds, scales=list(SCALES), quick=args.quick,
                  table_fixture_columns=3, full_table_fixtures_are_toy=True)
    old = json.loads(OLD_PATH.read_text())
    import fpylll
    result = dict(version=1, scope="Approximate cubic compilation; bounded research, not an FHE theorem",
                  dependencies=dict(fpylll=fpylll.__version__, replay="Python standard library only"),
                  config=config, provenance=dict(exact_script_sha256=sha(BASE_PATH), exact_artifact_sha256=sha(OLD_PATH)),
                  boundary_checks=boundary_checks(), family_audit=family_audit(), cases=[], status="running")
    result["regression"] = regression(old, config, deadline)
    print(json.dumps(dict(event="regression", improvements=result["regression"]["improved"],
                          comparisons=16, phase_trials=192)), flush=True)
    grid = list(itertools.product((3, 4, 6, 8), (12, 24, 64, 128)))
    if args.quick:
        grid = [(3, 12), (4, 24)]
    result["planned_grid"] = [list(pair) for pair in grid]
    atomic_write(args.output, result)
    for n, bits in grid:
        if time.monotonic() >= deadline:
            break
        print(json.dumps(dict(event="case_start", n=n, bits=bits)), flush=True)
        case = run_case(n, bits, old, config, deadline)
        result["cases"].append(case)
        result["summary"] = summarize(result)
        result["elapsed_seconds"] = round(time.monotonic()-started, 3)
        atomic_write(args.output, result)
        print(json.dumps(dict(event="case_saved", n=n, bits=bits, summary=result["summary"])), flush=True)
    result["status"] = "complete_bounded_study" if len(result["cases"]) == len(grid) else "global_budget_exhausted"
    result["summary"] = summarize(result)
    result["elapsed_seconds"] = round(time.monotonic()-started, 3)
    atomic_write(args.output, result)
    print(json.dumps(dict(event="finished", status=result["status"], summary=result["summary"])), flush=True)


if __name__ == "__main__":
    main()
