#!/usr/bin/env python3
"""Bounded positive nonlinear cubic-control synthesis, not an FHE proof.

The public compiler consumes a jointly generated ordinary/quadratic source.
Its input contains no secret or source errors.  A separate oracle checks its
complete recursive ciphertext under the ORIGINAL secret.  The encryption
table is retained separately and is never changed by this compiler.

Solver installation is external; e.g. PYTHONPATH=/tmp/fhe-nonlinear-synthesis-deps.
Only a concrete compiler with an independent asymptotic noise/failure proof
could justify changes to production Lean.  Timeouts do not prove infeasibility.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import time


VERSION = 1
TRAIN_SEED = 20261019
VALIDATE_SEED = 20261020
KINDS = ("S", "V", "M")


def centered(value, q):
    return (int(value)+q//2) % q-q//2


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def matvec(matrix, vector, q):
    return [sum(x*y for x, y in zip(row, vector)) % q for row in matrix]


def matmul(first, second, q):
    return [[sum(x*y for x, y in zip(row, column)) % q
             for column in zip(*second)] for row in first]


def inverse(matrix, q):
    """Unit-pivot elimination over Z/2^k, returning None on a singular parity."""
    n = len(matrix)
    work = [[x % q for x in row]+[int(i == j) for j in range(n)]
            for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next((i for i in range(column, n) if work[i][column] & 1), None)
        if pivot is None:
            return None
        work[column], work[pivot] = work[pivot], work[column]
        multiplier = pow(work[column][column], -1, q)
        work[column] = [x*multiplier % q for x in work[column]]
        for i in range(n):
            if i != column:
                multiplier = work[i][column]
                work[i] = [(x-multiplier*y) % q for x, y in zip(work[i], work[column])]
    return [row[n:] for row in work]


def flatten(ciphertext):
    matrix, vector, body = ciphertext
    return sum(matrix, [])+list(vector)+[body]


def phase(secret, ciphertext, q):
    matrix, vector, body = ciphertext
    return (body+sum(x*y for x, y in zip(secret, vector))-
            sum(secret[i]*matrix[i][j]*secret[j]
                for i, j in itertools.product(range(len(secret)), repeat=2))) % q


def message(secret, indices, monomial, weight):
    return weight*math.prod(secret[indices[i]] for i in monomial)


def quadratic_source(secret, indices, monomial, weight, q, errors, rng):
    """Actual public quadratic simulation, including its dropped mask.

    T=A'-M, c=y-a'+linear, b=z+constant.  Every source row is ordinary
    same-secret LWE; source masks are independent and uniform.
    """
    n = len(secret)
    matrix = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
    mask = [rng.randrange(q) for _ in range(n)]
    outputs = [(sum(secret[i]*matrix[i][j] for i in range(n))+errors[j]) % q
               for j in range(n)]
    body = (sum(x*y for x, y in zip(secret, mask))+errors[-1]) % q
    shifted = [row[:] for row in matrix]
    vector = [(outputs[j]-mask[j]) % q for j in range(n)]
    if len(monomial) == 1:
        vector[indices[monomial[0]]] = (vector[indices[monomial[0]]]+weight) % q
    elif len(monomial) == 2:
        i, j = (indices[x] for x in monomial)
        shifted[i][j] = (shifted[i][j]-weight) % q
    else:
        assert not monomial
    ciphertext = [shifted, vector, body]
    target = message(secret, indices, monomial, weight)
    residual = errors[-1]+sum(x*y for x, y in zip(secret, errors[:-1]))
    assert phase(secret, ciphertext, q) == (target+residual) % q
    return ciphertext, dict(matrix=matrix, mask=mask, outputs=outputs, body=body,
                            errors=errors, monomial=list(monomial), weight=weight)


def make_case(n, bits, radius, level, secret, seed, indices=None):
    q = 1 << bits
    indices = list(indices or (0, 1, 2))
    assert len(set(indices)) == 3 and max(indices) < n
    rng = random.Random(seed)
    attempts = 0
    while True:
        attempts += 1
        a = [[rng.randrange(q) for _ in range(n)] for _ in range(n)]
        inv = inverse(a, q)
        if inv is not None:
            break
        assert attempts < 1024
    inv_t = transpose(inv)
    errors = [rng.randint(-radius, radius) for _ in range(n)]
    y = [(sum(secret[i]*a[i][j] for i in range(n))+errors[j]) % q for j in range(n)]
    u = matvec(inv_t, y, q)
    weight = 1 << level
    ciphers, witnesses = {}, {}
    specifications = [("zero", (), 0)]
    for label, scale in (("unit", 1), ("weighted", weight)):
        specifications += [(f"{label}_{''.join(map(str, m))}", m, scale)
                           for m in ((0,), (1,), (2,), (0, 1), (0, 2), (1, 2))]
    for name, monomial, scale in specifications:
        noise = [rng.randint(-radius, radius) for _ in range(n+1)]
        ciphers[name], witnesses[name] = quadratic_source(
            secret, indices, monomial, scale, q, noise, rng)
    public = dict(n=n, bits=bits, q=q, indices=indices, weight=weight,
                  A=a, inverse_transpose=inv_t, y=y, u=u, ciphertexts=ciphers)
    oracle = dict(secret=list(secret), raw_errors=errors, witnesses=witnesses,
                  radius=radius, target=message(secret, indices, (0, 1, 2), weight))
    return dict(seed=seed, guard_draws=attempts, public=public, oracle=oracle)


def check_case(case):
    """Independent integer-law checker; it does not call phase or generation."""
    p, o = case["public"], case["oracle"]
    n, q, s = p["n"], p["q"], o["secret"]
    identity = [[int(i == j) for j in range(n)] for i in range(n)]
    assert matmul(transpose(p["inverse_transpose"]), p["A"], q) == identity
    assert matmul(p["A"], transpose(p["inverse_transpose"]), q) == identity
    assert all((sum(s[i]*p["A"][i][j] for i in range(n))+o["raw_errors"][j]) % q
               == p["y"][j] for j in range(n))
    assert p["u"] == matvec(p["inverse_transpose"], p["y"], q)
    assert p["u"] == [(s[i]+x) % q for i, x in
                      enumerate(matvec(p["inverse_transpose"], o["raw_errors"], q))]
    for name, witness in o["witnesses"].items():
        t, c, b = p["ciphertexts"][name]
        m, w = witness["monomial"], witness["weight"]
        assert all(abs(e) <= o["radius"] for e in witness["errors"])
        assert witness["outputs"] == [
            (sum(s[i]*witness["matrix"][i][j] for i in range(n))+witness["errors"][j]) % q
            for j in range(n)]
        assert witness["body"] == (sum(s[i]*witness["mask"][i] for i in range(n))+
                                   witness["errors"][-1]) % q
        expected_t = [row[:] for row in witness["matrix"]]
        expected_c = [(witness["outputs"][j]-witness["mask"][j]) % q for j in range(n)]
        if len(m) == 2:
            i, j = (p["indices"][x] for x in m)
            expected_t[i][j] = (expected_t[i][j]-w) % q
        elif len(m) == 1:
            i = p["indices"][m[0]]
            expected_c[i] = (expected_c[i]+w) % q
        assert t == expected_t and c == expected_c and b == witness["body"]
        target = w
        for i in m:
            target *= s[p["indices"][i]]
        error = witness["errors"][-1]+sum(s[i]*witness["errors"][i] for i in range(n))
        actual = b
        for i in range(n):
            actual += s[i]*c[i]
            for j in range(n):
                actual -= s[i]*t[i][j]*s[j]
        assert (actual-target-error) % q == 0
    expected_target = p["weight"]
    for i in p["indices"]:
        expected_target *= s[i]
    assert expected_target == o["target"]
    assert all(abs(e) <= o["radius"] for e in o["raw_errors"])
    return True


def input_registers(public):
    n, q = public["n"], public["q"]
    entries = [
        ("zeroS", "S", 0), ("one", "S", 1), ("minusOne", "S", q-1),
        ("weight", "S", public["weight"]), ("half", "S", q//2),
        ("zeroV", "V", [0]*n), ("zeroM", "M", [[0]*n for _ in range(n)]),
        ("identity", "M", [[int(i == j) for j in range(n)] for i in range(n)]),
        ("A", "M", public["A"]), ("inverseT", "M", public["inverse_transpose"]),
        ("y", "V", public["y"]), ("u", "V", public["u"])]
    entries += [(f"basis{i}", "V", [int(j == index) for j in range(n)])
                for i, index in enumerate(public["indices"])]
    for name in sorted(public["ciphertexts"]):
        matrix, vector, body = public["ciphertexts"][name]
        entries += [(name+".T", "M", matrix), (name+".c", "V", vector), (name+".b", "S", body)]
    return entries


# Type, operand types. Indices select one of the three PUBLIC coordinate indices.
OPS = {
    "addS": ("S", "SS"), "subS": ("S", "SS"), "mulS": ("S", "SS"),
    "dot": ("S", "VV"), "at": ("S", "V"), "entry": ("S", "M"), "trace": ("S", "M"),
    "addV": ("V", "VV"), "subV": ("V", "VV"), "hadV": ("V", "VV"),
    "scaleV": ("V", "SV"), "mv": ("V", "MV"), "row": ("V", "M"), "col": ("V", "M"),
    "addM": ("M", "MM"), "subM": ("M", "MM"), "hadM": ("M", "MM"),
    "scaleM": ("M", "SM"), "mm": ("M", "MM"), "outer": ("M", "VV"),
    "transpose": ("M", "M")}
for _kind in KINDS:
    for _operation in ("parity", "high", "round"):
        OPS[_operation+_kind] = (_kind, _kind)
OPNAMES = list(OPS)


def eval_op(op, a, b, i, j, grid, public):
    n, q = public["n"], public["q"]
    ix, jx = public["indices"][i], public["indices"][j]
    if op in ("addS", "subS", "mulS"):
        return {"addS": lambda: a+b, "subS": lambda: a-b, "mulS": lambda: a*b}[op]() % q
    if op == "dot":
        return sum(x*y for x, y in zip(a, b)) % q
    if op == "at":
        return a[ix]
    if op == "entry":
        return a[ix][jx]
    if op == "trace":
        return sum(a[k][k] for k in range(n)) % q
    if op == "transpose":
        return transpose(a)
    if op == "row":
        return list(a[ix])
    if op == "col":
        return [row[ix] for row in a]
    if op == "mv":
        return matvec(a, b, q)
    if op == "mm":
        return matmul(a, b, q)
    if op == "outer":
        return [[x*y % q for y in b] for x in a]
    if op in ("scaleV", "scaleM"):
        return [a*x % q for x in b] if op == "scaleV" else [[a*x % q for x in row] for row in b]
    if op[:3] in ("add", "sub", "had"):
        f = {"add": lambda x, y: (x+y) % q, "sub": lambda x, y: (x-y) % q,
             "had": lambda x, y: x*y % q}[op[:3]]
        return [f(x, y) for x, y in zip(a, b)] if op[-1] == "V" else [
            [f(x, y) for x, y in zip(row, other)] for row, other in zip(a, b)]
    kind = op[-1]
    def f(x):
        if op.startswith("parity"):
            return x & 1
        if op.startswith("high"):
            return x >> (public["bits"]-1)
        h = q >> (1, 2, 4)[grid]
        return ((centered(x, q)+h//2)//h*h) % q
    return f(a) if kind == "S" else ([f(x) for x in a] if kind == "V" else
                                    [[f(x) for x in row] for row in a])


def check_program(program, public):
    kinds = [kind for _, kind, _ in input_registers(public)]
    for node in program["nodes"]:
        out, expected = OPS[node["op"]]
        for index, required in zip((node["a"], node["b"]), expected):
            assert 0 <= index < len(kinds) and kinds[index] == required
        assert all(0 <= node[name] < 3 for name in ("i", "j", "grid"))
        kinds.append(out)
    assert [kinds[index] for index in program["outputs"]] == ["M", "V", "S"]


def compile(public, indices, weight, program):
    """Public positive compiler. No oracle parameter or global secret is read."""
    assert indices == public["indices"] and weight == public["weight"]
    check_program(program, public)
    registers = [value for _, _, value in input_registers(public)]
    for node in program["nodes"]:
        registers.append(eval_op(node["op"], registers[node["a"]], registers[node["b"]],
                                 node["i"], node["j"], node["grid"], public))
    matrix, vector, body = (registers[index] for index in program["outputs"])
    zero = public["ciphertexts"]["zero"]
    q = public["q"]
    return [[[(x+y) % q for x, y in zip(row, other)] for row, other in zip(zero[0], matrix)],
            [(x+y) % q for x, y in zip(zero[1], vector)], (zero[2]+body) % q]


def compile_view(table_columns, requests, program):
    """Keep every public-table coordinate, compile only the control context."""
    return dict(table=table_columns, controls=[
        compile(source, source["indices"], source["weight"], program) for source in requests])


def trim_program(program, public):
    initial = len(input_registers(public))
    needed = set(program["outputs"])
    for i in range(len(program["nodes"])-1, -1, -1):
        if initial+i in needed:
            node = program["nodes"][i]
            needed.add(node["a"])
            if len(OPS[node["op"]][1]) == 2:
                needed.add(node["b"])
    mapping = {i: i for i in range(initial)}
    nodes = []
    for i, node in enumerate(program["nodes"]):
        if initial+i not in needed:
            continue
        out = dict(node)
        out["a"] = mapping[node["a"]]
        out["b"] = mapping[node["b"]] if len(OPS[node["op"]][1]) == 2 else 0
        mapping[initial+i] = initial+len(nodes)
        nodes.append(out)
    return dict(label=program["label"], nodes=nodes, outputs=[mapping[i] for i in program["outputs"]])


def residual(case, output):
    p, o = case["public"], case["oracle"]
    n, s, q = p["n"], o["secret"], p["q"]
    assert len(output[0]) == n and len(output[1]) == n
    assert all(len(row) == n for row in output[0])
    assert all(isinstance(x, int) and 0 <= x < q for x in flatten(output))
    # Independent coordinate flattening, not the generation phase helper.
    coordinates = flatten(output)
    value = coordinates[-1]-o["target"]
    value += sum(coordinates[n*n+i]*s[i] for i in range(n))
    value -= sum(coordinates[n*i+j]*s[i]*s[j] for i in range(n) for j in range(n))
    return centered(value, q)


def test_bound(case):
    p, o = case["public"], case["oracle"]
    return min(p["q"]//32, 8*(p["n"]+1)*(o["radius"]+1)**2)


def program_digest(program):
    core = {key: program[key] for key in ("nodes", "outputs")}
    return hashlib.sha256(json.dumps(core, sort_keys=True).encode()).hexdigest()


def seed_programs(public):
    names = {name: index for index, (name, _, _) in enumerate(input_registers(public))}
    result = []
    def add(label, nodes, outputs):
        result.append(dict(label=label, nodes=nodes, outputs=outputs))
    def node(op, a, b=0, i=0, j=0, grid=0):
        return dict(op=op, a=a, b=b, i=i, j=j, grid=grid)
    out0 = [names["zeroM"], names["zeroV"], names["zeroS"]]
    add("zero-shift baseline", [], out0)
    # Copying a quadratic source is a known safe control but not the cubic.
    add("quadratic-message baseline",
        [node("subM", names["weighted_01.T"], names["zero.T"]),
         node("subV", names["weighted_01.c"], names["zero.c"]),
         node("subS", names["weighted_01.b"], names["zero.b"])],
        [len(names)+i for i in range(3)])
    for extract in ("parityS", "highS"):
        # Gate on the ORIGINAL secret via the output matrix, using a noisy
        # public full-residue estimate only for the third bit.
        nodes = [node("at", names["u"], i=2), node(extract, len(names)),
                 node("mulS", len(names)+1, names["weight"]),
                 node("subS", names["zeroS"], len(names)+2),
                 node("outer", names["basis0"], names["basis1"]),
                 node("scaleM", len(names)+3, len(names)+4)]
        add("matrix-gated-"+extract, nodes, [len(names)+5, out0[1], out0[2]])
        nodes = []
        for i in range(3):
            nodes += [node("at", names["u"], i=i), node(extract, len(names)+len(nodes))]
        nodes += [node("mulS", len(names)+1, len(names)+3),
                  node("mulS", len(names)+6, len(names)+5),
                  node("mulS", len(names)+7, names["weight"])]
        add("body-estimate-"+extract, nodes, [out0[0], out0[1], len(names)+8])
    return result


def training_pool():
    strata = [(n, bits, radius, bits-offset, list(secret))
              for n in (3, 4) for bits in (12, 16) for radius in (0, 1, 3)
              for offset in (1, 2) for secret in itertools.product((0, 1), repeat=n)]
    random.Random(TRAIN_SEED).shuffle(strata)
    result = []
    for i in range(512):
        result.append(make_case(*strata[i % len(strata)], TRAIN_SEED+100003*i))
    return result


def screen(program, cases, witness_limit=32):
    strata, hist = defaultdict(lambda: [0, 0]), Counter()
    witnesses, worst = [], 0
    for case in cases:
        p, o = case["public"], case["oracle"]
        output = compile(p, p["indices"], p["weight"], program)
        error = residual(case, output)
        good = abs(error) <= test_bound(case)
        label = (f"n={p['n']},bits={p['bits']},E={o['radius']},"
                 f"level={p['weight'].bit_length()-1}")
        strata[label][0] += int(good)
        strata[label][1] += 1
        hist["pass" if good else "fail"] += 1
        worst = max(worst, abs(error))
        if not good and len(witnesses) < witness_limit:
            witnesses.append(dict(case=case, output=output, residual=error, bound=test_bound(case)))
    return dict(passed=hist["pass"], failed=hist["fail"], total=sum(hist.values()),
                worst_absolute_residual=worst, strata=dict(strata),
                finite_screen_pass=all(100*good >= 99*total for good, total in strata.values()),
                counterexamples=witnesses)


def values_flat(kind, value):
    return [value] if kind == "S" else (value if kind == "V" else sum(value, []))


def smt_search(active, size, solver_seconds, deadline, iteration, fixed_program=None, warm_program=None):
    """One finite grammar query. Interpret its concrete model independently."""
    import z3
    start = time.monotonic()
    solver = z3.Optimize()
    solver.set(timeout=1000*solver_seconds)
    public0 = active[0]["public"]
    registers0 = input_registers(public0)
    initial = len(registers0)
    kind = z3.Function("kind", z3.IntSort(), z3.IntSort())
    for index, (_, register_kind, _) in enumerate(registers0):
        solver.add(kind(index) == KINDS.index(register_kind))
    choices = []
    for index in range(size):
        variables = [z3.Int(f"{name}_{index}") for name in ("op", "a", "b", "i", "j", "grid")]
        choices.append(variables)
        op, a, b, ix, jx, grid = variables
        solver.add(op >= 0, op < len(OPNAMES), a >= 0, a < initial+index,
                   b >= 0, b < initial+index, ix >= 0, ix < 3, jx >= 0, jx < 3,
                   grid >= 0, grid < 3)
        for number, name in enumerate(OPNAMES):
            output_kind, operand_kinds = OPS[name]
            requirements = [kind(initial+index) == KINDS.index(output_kind)]
            requirements += [kind(arg) == KINDS.index(expected)
                             for arg, expected in zip((a, b), operand_kinds)]
            if len(operand_kinds) == 1:
                requirements.append(b == 0)
            solver.add(z3.Implies(op == number, z3.And(*requirements)))
    outputs = [z3.Int("output_"+k) for k in ("M", "V", "S")]
    for index, expected in zip(outputs, ("M", "V", "S")):
        solver.add(index >= 0, index < initial+size, kind(index) == KINDS.index(expected))
    if fixed_program is not None:
        check_program(fixed_program, public0)
        assert len(fixed_program["nodes"]) <= size
        padding = dict(op="addS", a=0, b=0, i=0, j=0, grid=0)
        for variables, node in zip(choices, fixed_program["nodes"]+
                                   [padding]*(size-len(fixed_program["nodes"]))):
            expected = [OPNAMES.index(node["op"])]+[node[key] for key in ("a", "b", "i", "j", "grid")]
            solver.add(*[variable == value for variable, value in zip(variables, expected)])
        solver.add(*[variable == value for variable, value in zip(outputs, fixed_program["outputs"])])
    elif warm_program is not None:
        check_program(warm_program, public0)
        assert len(warm_program["nodes"]) <= size
        padding = dict(op="addS", a=0, b=0, i=0, j=0, grid=0)
        for variables, node in zip(choices, warm_program["nodes"]+
                                   [padding]*(size-len(warm_program["nodes"]))):
            values = [OPNAMES.index(node["op"])]+[node[key] for key in ("a", "b", "i", "j", "grid")]
            for variable, value in zip(variables, values):
                solver.set_initial_value(variable, z3.IntVal(value))
        for variable, value in zip(outputs, warm_program["outputs"]):
            solver.set_initial_value(variable, z3.IntVal(value))
    functions = {}
    good_expressions = []
    for case_number, case in enumerate(active):
        if time.monotonic() > deadline:
            return None, dict(status="build_deadline", active_examples=len(active), nodes=size)
        p, o = case["public"], case["oracle"]
        n, bits, q = p["n"], p["bits"], p["q"]
        if bits not in functions:
            functions[bits] = z3.Function("register_"+str(bits), z3.IntSort(),
                                          z3.IntSort(), z3.IntSort(), z3.BitVecSort(bits))
        function = functions[bits]
        def reg(register, coordinate=0):
            return function(case_number, register, coordinate)
        concrete = input_registers(p)
        assert [(name, k) for name, k, _ in concrete] == [
            (name, k) for name, k, _ in registers0]
        for register, (_, register_kind, value) in enumerate(concrete):
            for coordinate, number in enumerate(values_flat(register_kind, value)):
                solver.add(reg(register, coordinate) == number)
        for index, (op, a, b, ix, jx, grid) in enumerate(choices):
            pi = z3.If(ix == 0, p["indices"][0],
                       z3.If(ix == 1, p["indices"][1], p["indices"][2]))
            pj = z3.If(jx == 0, p["indices"][0],
                       z3.If(jx == 1, p["indices"][1], p["indices"][2]))
            def ra(coordinate=0):
                return reg(a, coordinate)
            def rb(coordinate=0):
                return reg(b, coordinate)
            def transformed(name, value):
                if name.startswith("parity"):
                    return value & 1
                if name.startswith("high"):
                    return z3.LShR(value, bits-1)
                def rounded(shift):
                    h = 1 << shift
                    full = ((z3.SignExt(1, value)+h//2) >> shift)*h
                    return z3.Extract(bits-1, 0, full)
                return z3.If(grid == 0, rounded(bits-1),
                             z3.If(grid == 1, rounded(bits-2), rounded(bits-4)))
            for number, name in enumerate(OPNAMES):
                output_kind = OPS[name][0]
                length = {"S": 1, "V": n, "M": n*n}[output_kind]
                expressions = []
                for c in range(length):
                    i, j = divmod(c, n)
                    if name == "addS":
                        value = ra()+rb()
                    elif name == "subS":
                        value = ra()-rb()
                    elif name == "mulS":
                        value = ra()*rb()
                    elif name == "dot":
                        value = sum(ra(t)*rb(t) for t in range(n))
                    elif name == "at":
                        value = ra(pi)
                    elif name == "entry":
                        value = ra(pi*n+pj)
                    elif name == "trace":
                        value = sum(ra(t*n+t) for t in range(n))
                    elif name in ("addV", "addM"):
                        value = ra(c)+rb(c)
                    elif name in ("subV", "subM"):
                        value = ra(c)-rb(c)
                    elif name in ("hadV", "hadM"):
                        value = ra(c)*rb(c)
                    elif name in ("scaleV", "scaleM"):
                        value = ra()*rb(c)
                    elif name == "mv":
                        value = sum(ra(c*n+t)*rb(t) for t in range(n))
                    elif name == "mm":
                        value = sum(ra(i*n+t)*rb(t*n+j) for t in range(n))
                    elif name == "outer":
                        value = ra(i)*rb(j)
                    elif name == "transpose":
                        value = ra(j*n+i)
                    elif name == "row":
                        value = ra(pi*n+c)
                    elif name == "col":
                        value = ra(c*n+pi)
                    else:
                        value = transformed(name, ra(c))
                    expressions.append(reg(initial+index, c) == value)
                solver.add(z3.Implies(op == number, z3.And(*expressions)))
        secret_positions = [i for i, bit in enumerate(o["secret"]) if bit]
        zero_phase = phase(o["secret"], p["ciphertexts"]["zero"], q)
        error = reg(outputs[2])+zero_phase-o["target"]
        error += sum(reg(outputs[1], i) for i in secret_positions)
        error -= sum(reg(outputs[0], i*n+j) for i in secret_positions for j in secret_positions)
        bound = test_bound(case)
        good = z3.Or(z3.ULE(error, bound), z3.UGE(error, q-bound))
        good_expressions.append(good)
        solver.add_soft(good)
        if (case_number+1) % 8 == 0:
            print(json.dumps(dict(event="encoding", nodes=size, iteration=iteration,
                                  encoded=case_number+1, total=len(active))), flush=True)
    # The primary objective is the number of satisfied finite examples.
    # This secondary objective makes the representation reproducible/small.
    solver.minimize(sum(op for op, *_ in choices))
    print(json.dumps(dict(event="solve", nodes=size, iteration=iteration,
                          active_examples=len(active), build_seconds=round(time.monotonic()-start, 2))), flush=True)
    solver_start = time.monotonic()
    remaining_ms = int(1000*(deadline-solver_start))
    if remaining_ms <= 0:
        return None, dict(status="build_deadline", active_examples=len(active), nodes=size)
    solver.set(timeout=min(1000*solver_seconds, remaining_ms))
    status = solver.check()
    record = dict(nodes=size, iteration=iteration, active_examples=len(active), status=str(status),
                  build_seconds=round(solver_start-start, 3),
                  solve_seconds=round(time.monotonic()-solver_start, 3))
    if warm_program is not None:
        record["warm_start"] = warm_program["label"]
    if status == z3.unknown:
        record["reason"] = solver.reason_unknown()
    try:
        model = solver.model()
        def integer(value):
            return model.eval(value, model_completion=True).as_long()
        nodes = []
        for row in choices:
            number, a, b, i, j, grid = map(integer, row)
            nodes.append(dict(op=OPNAMES[number], a=a, b=b, i=i, j=j, grid=grid))
        program = dict(label=f"smt-{size}-{iteration}", nodes=nodes, outputs=list(map(integer, outputs)))
        for case_number, case in enumerate(active):
            p = case["public"]
            check_program(program, p)
            values = [value for _, _, value in input_registers(p)]
            kinds = [k for _, k, _ in input_registers(p)]
            for node in nodes:
                values.append(eval_op(node["op"], values[node["a"]], values[node["b"]],
                                      node["i"], node["j"], node["grid"], p))
                kinds.append(OPS[node["op"]][0])
            function = functions[p["bits"]]
            for register, (register_kind, value) in enumerate(zip(kinds, values)):
                assert integer(kind(register)) == KINDS.index(register_kind), (
                    f"case {case_number}, register {register}: type mismatch")
                for coordinate, expected in enumerate(values_flat(register_kind, value)):
                    observed = integer(function(case_number, register, coordinate))
                    assert observed == expected, (
                        f"case {case_number}, register {register}, coordinate {coordinate}: "
                        f"SMT={observed}, interpreter={expected}")
            actual_good = abs(residual(case, compile(p, p["indices"], p["weight"], program))) <= test_bound(case)
            assert z3.is_true(model.eval(good_expressions[case_number], model_completion=True)) == actual_good
        record["model_semantics_verified"] = True
        return trim_program(program, public0), record
    except (z3.Z3Exception, AssertionError, IndexError, ValueError, KeyError) as error:
        record["model_semantics_verified"] = False
        record["model_rejection"] = type(error).__name__+": "+str(error)[:250]
        return None, record


def independent_validation_many(programs, draws):
    """Held-out masks, dimensions, all gadget levels and whole source errors."""
    results = [dict(total=0, draws_per_stratum=draws, strata={}, finite_screen_pass=True,
                    counterexamples=[], seed=VALIDATE_SEED) for _ in programs]
    for n, bits, radius in itertools.product((3, 4, 6, 8), (12, 16, 20, 24), (0, 1, 3)):
        cases = []
        for i in range(draws):
            seed = VALIDATE_SEED+1000000*n+10000*bits+1000*radius+i
            rng = random.Random(seed ^ 0x91A73)
            # Cycle through every key at each dimension when draws >= 256.
            secret = [(i >> j) & 1 for j in range(n)]
            indices = rng.sample(range(n), 3)
            levels = list(range(bits))+[bits-1, bits-2]
            # Each complete block traverses every level; rotate subsequent
            # blocks to avoid a fixed key/level pairing.
            level = levels[(i+i//len(levels)) % len(levels)]
            cases.append(make_case(n, bits, radius, level, secret, seed, indices))
        covered_levels = sorted({case["public"]["weight"].bit_length()-1 for case in cases})
        if draws >= bits+2:
            assert covered_levels == list(range(bits)), (n, bits, radius, covered_levels)
        label = f"n={n},bits={bits},E={radius}"
        for program, saved in zip(programs, results):
            result = screen(program, cases, witness_limit=2)
            saved["strata"][label] = {key: value for key, value in result.items()
                                       if key not in ("strata", "counterexamples")}
            saved["strata"][label]["per_level_counts"] = result["strata"]
            saved["strata"][label]["covered_levels"] = covered_levels
            saved["finite_screen_pass"] &= result["finite_screen_pass"]
            saved["total"] += len(cases)
            saved["counterexamples"].extend(result["counterexamples"])
        print(json.dumps(dict(event="validation_stratum", stratum=label, samples=len(cases),
                              candidates=len(programs))), flush=True)
    return results


def paired_fixtures(pool):
    return [next(c for c in pool if c["public"]["n"] == n and c["oracle"]["radius"] == radius)
            for n, radius in itertools.product((3, 4), (1, 3))]


def perturbation_checks(program, cases):
    """Paired changes to raw and quadratic source errors with masks fixed."""
    records = []
    for fixture, case in enumerate(cases):
        p, o = case["public"], case["oracle"]
        if o["radius"] == 0:
            continue
        # Deep copy by JSON ensures none of the unperturbed fixtures changes.
        coordinates = [("raw", None, i) for i in range(p["n"])]
        coordinates += [("quadratic", name, i) for name in sorted(p["ciphertexts"])
                        for i in range(p["n"]+1)]
        for category, name, coordinate in coordinates:
            for sign in (-1, 1):
                changed = json.loads(json.dumps(case))
                pp, oo = changed["public"], changed["oracle"]
                if category == "raw":
                    delta = sign-oo["raw_errors"][coordinate]
                    oo["raw_errors"][coordinate] = sign
                    pp["y"][coordinate] = (pp["y"][coordinate]+delta) % pp["q"]
                    pp["u"] = matvec(pp["inverse_transpose"], pp["y"], pp["q"])
                else:
                    witness = oo["witnesses"][name]
                    delta = sign-witness["errors"][coordinate]
                    witness["errors"][coordinate] = sign
                    if coordinate == pp["n"]:
                        witness["body"] = (witness["body"]+delta) % pp["q"]
                        pp["ciphertexts"][name][2] = witness["body"]
                    else:
                        witness["outputs"][coordinate] = (witness["outputs"][coordinate]+delta) % pp["q"]
                        pp["ciphertexts"][name][1][coordinate] = (
                            pp["ciphertexts"][name][1][coordinate]+delta) % pp["q"]
                check_case(changed)
                output = compile(pp, pp["indices"], pp["weight"], program)
                records.append(dict(fixture=fixture, seed=case["seed"], category=category,
                                    name=name, coordinate=coordinate, sign=sign,
                                    output=output, residual=residual(changed, output),
                                    bound=test_bound(changed)))
    return dict(scope="Targeted sensitivity checks, not probability estimates", cases=records)


def algebra_checks():
    """Check the encoder's nonlinear rounding and source law independently."""
    import z3
    operation_checks = 0
    for bits in (2, 3, 4, 8):
        q = 1 << bits
        for x in range(q):
            for shift in sorted(set((bits-1, max(0, bits-2), max(0, bits-4)))):
                h = 1 << shift
                expression = ((z3.SignExt(1, z3.BitVecVal(x, bits))+h//2) >> shift)*h
                observed = z3.simplify(z3.Extract(bits-1, 0, expression)).as_long()
                expected = (centered(x, q)+h//2)//h*h % q
                assert observed == expected
                operation_checks += 1
    guard = []
    for n in (3, 4, 6, 8, 16, 32, 64, 128):
        probability = math.prod(Fraction(2**i-1, 2**i) for i in range(1, n+1))
        assert probability >= Fraction(1, 4)
        # Avoid turning huge fractions into low-precision floating claims.
        guard.append(dict(n=n, exact_probability=str(probability), lower_bound="1/4"))
    return dict(exact_bitvector_rounding_checks=operation_checks, guard_probabilities=guard)


def encoding_checks(pool):
    """Fix every operator in a known circuit before trusting synthesis results."""
    public = pool[0]["public"]
    names = {name: index for index, (name, _, _) in enumerate(input_registers(public))}
    operands = {"S": [names["weight"], names["minusOne"]],
                "V": [names["y"], names["u"]], "M": [names["A"], names["inverseT"]]}
    nodes = []
    for number, name in enumerate(OPNAMES):
        _, types = OPS[name]
        a = operands[types[0]][0]
        b = operands[types[1]][1] if len(types) == 2 else 0
        nodes.append(dict(op=name, a=a, b=b, i=number % 3, j=(number+1) % 3, grid=number % 3))
    initial = len(names)
    outputs = [initial+max(i for i, node in enumerate(nodes) if OPS[node["op"]][0] == kind)
               for kind in ("M", "V", "S")]
    program = dict(label="all-operator conformance fixture", nodes=nodes, outputs=outputs)
    cases = [next(c for c in pool if c["public"]["n"] == n and c["public"]["bits"] == bits)
             for n, bits in itertools.product((3, 4), (12, 16))]
    actual, record = smt_search(cases, len(nodes), 30, time.monotonic()+120, -1,
                                fixed_program=program)
    assert actual is not None and record["status"] == "sat" and record["model_semantics_verified"], record
    return dict(operators=len(nodes), samples=len(cases), status="sat",
                model_semantics_verified=True, register_coordinate_checks=sum(
                    sum(len(values_flat(kind, value)) for _, kind, value in input_registers(c["public"]))+
                    sum({"S": 1, "V": c["public"]["n"], "M": c["public"]["n"]**2}[OPS[node["op"]][0]]
                        for node in nodes) for c in cases))


def reference_checks(pool):
    checked = 0
    for case in pool:
        p, o = case["public"], case["oracle"]
        assert not ({"secret", "errors", "raw_errors", "oracle"} & set(p))
        output = json.loads(json.dumps(p["ciphertexts"]["zero"]))
        output[2] = (output[2]+o["target"]) % p["q"]
        assert abs(residual(case, output)) <= (p["n"]+1)*o["radius"]
        assert abs(residual(case, output)) <= test_bound(case)
        checked += 1
    return dict(secret_oracle_reference_cases=checked,
                reference_is_not_a_public_candidate=True,
                runtime_compiler_input_contains_no_secret_or_error_field=True)


def full_view_checks(programs):
    results = [[] for _ in programs]
    for n, bits in ((3, 12), (4, 16)):
        for key_bit in (0, 1):
            q = 1 << bits
            secret = [int(i % 2 == 0) for i in range(n)] if key_bit == 0 else [1]*n
            key_kind = "alternating" if key_bit == 0 else "ones"
            rng = random.Random(0x20261019+n*100+key_bit)
            columns = []
            p = (n*n+n+1)*bits+17
            for _ in range(p):
                column, _ = quadratic_source(secret, [0, 1, 2], (), 0, q,
                                             [rng.randint(-1, 1) for _ in range(n+1)], rng)
                assert abs(centered(phase(secret, column, q), q)) <= n+1
                columns.append(flatten(column))
            cases = []
            for indices in itertools.permutations(range(n), 3):
                for level in range(bits):
                    seed = 0x612019+n*100000+key_bit*10000+len(cases)
                    cases.append(make_case(n, bits, 1, level, secret, seed, list(indices)))
            saved_table = json.dumps(columns)
            for program, result in zip(programs, results):
                view = compile_view(columns, [c["public"] for c in cases], program)
                assert view["table"] is columns and json.dumps(view["table"]) == saved_table
                good, witnesses = 0, []
                for case, output in zip(cases, view["controls"]):
                    error = residual(case, output)
                    good += abs(error) <= test_bound(case)
                    if abs(error) > test_bound(case) and not witnesses:
                        witnesses.append(dict(case=case, output=output, residual=error, bound=test_bound(case)))
                result.append(dict(n=n, bits=bits, key_kind=key_kind, secret=secret, public_columns=p,
                                   complete_public_coordinates=(n*n+n+1)*p,
                                   controls=len(cases), passed=good, failed=len(cases)-good,
                                   retained_table_unchanged=True, counterexamples=witnesses))
    return results


def seed_obstruction_checks():
    """Exact checks supporting the seed-specific constant-failure derivation.

    These checks and the mathematical argument concern the six seed formulas,
    not the full timed-out grammar. Transfer to a nonuniform interval sampler
    requires its existing statistical approximation loss.
    """
    parity_checks = 0
    for radius in (1, 2, 3, 4, 8, 16, 256):
        size = 2*radius+1
        odd = sum(x & 1 for x in range(-radius, radius+1))
        even = size-odd
        lower = (Fraction(radius, size) if radius % 2 == 0 else
                 (1-Fraction(1, size*size))/2)
        assert lower >= Fraction(1, 3)
        even_count, odd_count = 1, 0
        for weight in range(1, 33):
            even_count, odd_count = (even_count*even+odd_count*odd,
                                     even_count*odd+odd_count*even)
            observed = Fraction(odd_count, size**weight)
            expected = (1-Fraction(even-odd, size)**weight)/2
            assert observed == expected and observed >= lower
            assert observed/4 >= Fraction(1, 12)
            parity_checks += 1
    parity_truth_checks = high_truth_checks = inverse_trials = 0
    points = list(itertools.product((0, 1), repeat=3))
    for delta in points:
        disagreements = 0
        for secret in points:
            disagreements += math.prod(secret) != math.prod(s ^ d for s, d in zip(secret, delta))
            parity_truth_checks += 1
        assert disagreements == (2 if any(delta) else 0)
    for q in (4, 8, 16):
        bits = q.bit_length()-1
        for delta in range(q):
            pattern = tuple(((delta+s) % q) >> (bits-1) for s in (0, 1))
            assert (pattern == (0, 1)) == (delta == q//2-1)
        for delta in itertools.product(range(q), repeat=3):
            disagreements = 0
            for secret in points:
                prediction = math.prod(((s+d) % q) >> (bits-1) for s, d in zip(secret, delta))
                disagreements += prediction != math.prod(secret)
                high_truth_checks += 1
            assert disagreements == 0 if all(d == q//2-1 for d in delta) else disagreements >= 1
        for radius in (1, 3):
            if 2*radius+1 > q:
                continue
            assert Fraction(1-Fraction(1, 2*radius+1), 8) >= Fraction(1, 12)
            for coefficient in range(1, q, 2):
                for offset in range(q):
                    count = 0
                    for error in range(-radius, radius+1):
                        count += (coefficient*error+offset) % q == q//2-1
                        inverse_trials += 1
                    assert count <= 1
    return dict(scope="Seed-specific exact checks; not a general compiler impossibility result",
                parity_weight_checks=parity_checks, parity_truth_assignments=parity_truth_checks,
                high_bit_truth_assignments=high_truth_checks, odd_inverse_error_trials=inverse_trials,
                uniform_interval_seed_failure_lower_bound="1/12",
                required_margin="H + (n+1)*E < q/4, E>=1, 2*E+1<=q",
                sampler_transfer="Subtract n times the scalar error sampler TV approximation loss")


def verify_existing(path):
    result = json.loads(path.read_text())
    assert result["validation_schedule_version"] == 2
    pool = training_pool()
    for case in pool:
        check_case(case)
    assert result["algebra_checks"] == algebra_checks()
    assert result["encoding_checks"] == encoding_checks(pool)
    assert result["reference_checks"] == reference_checks(pool)
    validation_draws = {c["validation"]["draws_per_stratum"] for c in result["candidates"]}
    assert len(validation_draws) == 1
    validations = independent_validation_many(
        [c["program"] for c in result["candidates"]], validation_draws.pop())
    full_views = full_view_checks([c["program"] for c in result["candidates"]])
    training_count = validation_count = perturbation_count = 0
    for candidate, validation, views in zip(result["candidates"], validations, full_views):
        program = candidate["program"]
        assert candidate["digest"] == program_digest(program)
        assert candidate["training"] == screen(program, pool)
        training_count += len(pool)
        if "validation" in candidate:
            assert candidate["validation"] == validation
            validation_count += candidate["validation"]["total"]
        assert candidate["perturbations"] == perturbation_checks(program, paired_fixtures(pool))
        assert candidate["full_views"] == views
        for group in ("training", "validation"):
            if group not in candidate:
                continue
            for witness in candidate[group]["counterexamples"]:
                case = witness["case"]
                check_case(case)
                output = compile(case["public"], case["public"]["indices"],
                                 case["public"]["weight"], program)
                assert output == witness["output"]
                assert residual(case, output) == witness["residual"]
                assert test_bound(case) == witness["bound"]
        perturbation_count += len(candidate["perturbations"]["cases"])
    assert result["production_Lean_changed"] is False
    assert result["asymptotic_noise_or_security_theorem"] is False
    print(json.dumps(dict(replayed_training_cases=training_count, replayed_validation_cases=validation_count,
                          replayed_paired_perturbations=perturbation_count)), flush=True)


def refresh_validation(path):
    """Regenerate changed validation cases without repeating solver timeouts."""
    result = json.loads(path.read_text())
    start = time.monotonic()
    pool = training_pool()
    for case in pool:
        check_case(case)
    candidates = result["candidates"]
    for candidate in candidates:
        assert candidate["digest"] == program_digest(candidate["program"])
        assert candidate["training"] == screen(candidate["program"], pool)
    draws = {c["validation"]["draws_per_stratum"] for c in candidates}
    assert len(draws) == 1
    programs = [c["program"] for c in candidates]
    validations = independent_validation_many(programs, draws.pop())
    views = full_view_checks(programs)
    for candidate, validation, full_views in zip(candidates, validations, views):
        candidate["validation"] = validation
        candidate["full_views"] = full_views
    passed = [c["digest"] for c in candidates if c["training"]["finite_screen_pass"] and
              c["validation"]["finite_screen_pass"]]
    result["finite_screen_candidates"] = passed
    assert not passed, "A new passing candidate requires the mathematical gate, not a silent refresh"
    result["validation_schedule_version"] = 2
    result.setdefault("validation_refreshes", []).append(dict(
        reason="Ensure every gadget level is covered; include mixed-key complete-view fixtures",
        reused_solver_queries=len(result["queries"]),
        elapsed_seconds=round(time.monotonic()-start, 3)))
    result["settings"]["verify_seed_obstructions"] = False
    result["settings"]["refresh_validation"] = None
    result["elapsed_seconds"] += result["validation_refreshes"][-1]["elapsed_seconds"]
    temporary = path.with_suffix(path.suffix+".tmp")
    temporary.write_text(json.dumps(result, indent=2)+"\n")
    temporary.replace(path)
    print(json.dumps(dict(outcome=result["outcome"], refreshed_candidates=len(candidates),
                          reused_solver_queries=len(result["queries"]),
                          elapsed_seconds=result["validation_refreshes"][-1]["elapsed_seconds"])), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    mode.add_argument("--verify-seed-obstructions", action="store_true")
    mode.add_argument("--refresh-validation", type=Path)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--solver-seconds", type=int, default=60)
    parser.add_argument("--iterations", type=int, default=30)
    parser.add_argument("--search-seconds", type=int, default=7200)
    parser.add_argument("--validation-draws", type=int, default=4096)
    args = parser.parse_args()
    import z3
    assert z3.get_version_string() == "4.13.3"
    if args.verify_seed_obstructions:
        print(json.dumps(seed_obstruction_checks(), indent=2), flush=True)
        return
    if args.refresh_validation:
        refresh_validation(args.refresh_validation)
        return
    if args.verify_existing:
        verify_existing(args.verify_existing)
        return
    if args.quick:
        args.solver_seconds, args.iterations, args.validation_draws = 3, 2, 16
    assert 0 < args.solver_seconds <= 60 and 0 < args.iterations <= 30
    assert 0 < args.search_seconds <= 7200 and args.validation_draws > 0
    started = time.monotonic()
    deadline = started+args.search_seconds
    z3.set_param("smt.random_seed", TRAIN_SEED)
    pool = training_pool()
    for case in pool:
        check_case(case)
    conformance = encoding_checks(pool)
    reference = reference_checks(pool)
    candidates = {}
    def retain(program):
        digest = program_digest(program)
        if digest not in candidates:
            candidates[digest] = dict(digest=digest, program=program, training=screen(program, pool))
        return candidates[digest]
    for program in seed_programs(pool[0]["public"]):
        retain(program)
    queries = []
    for size in (12, 24):
        active_indices = list(range(32))
        seen = set()
        size_deadline = min(deadline, time.monotonic()+1800)
        for iteration in range(args.iterations):
            if time.monotonic() >= size_deadline:
                queries.append(dict(nodes=size, status="size_deadline", iteration=iteration))
                break
            warm = max(candidates.values(), key=lambda c: c["training"]["passed"])["program"]
            try:
                program, query = smt_search([pool[i] for i in active_indices], size,
                                            args.solver_seconds, size_deadline, iteration, warm_program=warm)
            except (z3.Z3Exception, MemoryError) as error:
                program = None
                query = dict(nodes=size, iteration=iteration, status="solver_exception",
                             reason=type(error).__name__+": "+str(error)[:250])
            queries.append(query)
            print(json.dumps(dict(event="query_result", **query)), flush=True)
            if program is None:
                # Do not repeat an unchanged timed-out/failed query.
                break
            candidate = retain(program)
            if candidate["digest"] in seen:
                query["stop"] = "repeated_formula"
                break
            seen.add(candidate["digest"])
            failing = [i for i, case in enumerate(pool) if i not in active_indices and
                       abs(residual(case, compile(case["public"], case["public"]["indices"],
                                                  case["public"]["weight"], program))) > test_bound(case)]
            if not failing:
                query["stop"] = "no_further_pool_counterexample"
                break
            active_indices += failing[:16]
    ranked = sorted(candidates.values(), key=lambda c: (-c["training"]["passed"],
                    len(c["program"]["nodes"]), c["digest"]))[:8]
    validations = independent_validation_many([c["program"] for c in ranked], args.validation_draws)
    views = full_view_checks([c["program"] for c in ranked])
    for candidate, validation, full_views in zip(ranked, validations, views):
        candidate["validation"] = validation
        candidate["perturbations"] = perturbation_checks(candidate["program"], paired_fixtures(pool))
        candidate["full_views"] = full_views
    passed = [c for c in ranked if c["training"]["finite_screen_pass"] and
              c["validation"]["finite_screen_pass"]]
    result = dict(version=VERSION, validation_schedule_version=2,
                  scope="Bounded dimension-independent positive compiler search; finite screens are not security proofs",
                  solver_version=z3.get_version_string(), quick=args.quick,
                  settings=vars(args) | {"output": str(args.output), "verify_existing": None},
                  grammar=dict(operations=OPS, node_caps=[12, 24], input_registers=[
                      [name, kind] for name, kind, _ in input_registers(pool[0]["public"])],
                      constants=["0", "1", "-1", "weight", "q/2"],
                      public_guard="A is invertible modulo two",
                      output="zero ciphertext plus a typed (matrix, vector, body) correction",
                      limitations="Bounded DAG family; compiler does not read the retained encryption table"),
                  source=dict(training_seed=TRAIN_SEED, validation_seed=VALIDATE_SEED,
                              training_cases=len(pool), fixed_secret=True, source_errors_used_by_compiler=False,
                              input_message_degree_at_most=2,
                              witness_distribution="Uniform integer interval diagnostics; targeted perturbations separately labeled"),
                  algebra_checks=algebra_checks(), encoding_checks=conformance, reference_checks=reference,
                  queries=queries, candidates=ranked,
                  finite_screen_candidates=[c["digest"] for c in passed],
                  outcome=("finite_candidate_needs_mathematical_gate" if passed else
                           "inconclusive_bounded_search" if any(q["status"] in (
                               "unknown", "build_deadline", "size_deadline", "solver_exception") for q in queries) else
                           "no_candidate_in_executed_search"),
                  production_Lean_changed=False, asymptotic_noise_or_security_theorem=False,
                  elapsed_seconds=round(time.monotonic()-started, 3))
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(outcome=result["outcome"], candidates=len(ranked),
                          screen_pass=len(passed), elapsed_seconds=result["elapsed_seconds"])), flush=True)


if __name__ == "__main__":
    main()
