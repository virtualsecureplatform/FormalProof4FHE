#!/usr/bin/env python3
"""Exact filters for fixed globally commuting idempotent GSW factors.

The public spectral enumeration uses only the factors. Its width is at most
the matrix width over Z/(2^L); no key, diagonalizing basis, or error enters.
The generated families and native-gadget witness are algebraic diagnostics,
not secure samplers or an impossibility result for general refresh methods.
"""
import argparse
import itertools
import json
from pathlib import Path
import random


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def zero(rows, columns):
    return [[0] * columns for _ in range(rows)]


def product(a, b, q):
    columns = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) % q for col in columns]
            for row in a]


def difference(a, b, q):
    return [[(x - y) % q for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def nonzero(a):
    return any(any(row) for row in a)


def public_patterns(factors, q):
    """Split nonzero prefix projectors, using only public ring arithmetic."""
    width = len(factors[0])
    states = [((), identity(width))]
    counts = [1]
    for p in factors:
        following = []
        for label, e in states:
            e1 = product(e, p, q)
            e0 = difference(e, e1, q)
            for bit, branch in enumerate((e0, e1)):
                if nonzero(branch):
                    # A nonzero idempotent cannot vanish modulo two.
                    assert any(x % 2 for row in branch for x in row)
                    assert product(branch, branch, q) == branch
                    following.append((label + (bit,), branch))
        states = following
        counts.append(len(states))
        assert 1 <= len(states) <= width
    total = zero(width, width)
    for _, e in states:
        total = [[(x + y) % q for x, y in zip(ar, br)]
                 for ar, br in zip(total, e)]
    assert total == identity(width)
    for i, (_, e) in enumerate(states):
        for j, (_, f) in enumerate(states):
            if i != j:
                assert not nonzero(product(e, f, q))
    return states, counts


def complement_tree(patterns, factors, gadget, q, depth=0):
    """Right-CMux decision trie for the complement of the public list.

    Leaves are G for true and zero for false. The returned ciphertext is
    evaluated with the same fixed original-key control factors at all nodes.
    """
    if not patterns:
        return gadget, 1
    if depth == len(factors):
        return zero(len(gadget), len(gadget[0])), 1
    low, ln = complement_tree([b for b in patterns if not b[depth]],
                              factors, gadget, q, depth + 1)
    high, hn = complement_tree([b for b in patterns if b[depth]],
                               factors, gadget, q, depth + 1)
    shifted = product(difference(high, low, q), factors[depth], q)
    result = [[(x + y) % q for x, y in zip(ar, br)]
              for ar, br in zip(low, shifted)]
    return result, ln + hn + 1


def conjugated_family(n, width, q, rng):
    basis, inverse = identity(width), identity(width)
    for _ in range(3 * width):
        i, j = rng.sample(range(width), 2)
        coefficient = rng.randrange(q)
        basis[i] = [(x + coefficient * y) % q
                    for x, y in zip(basis[i], basis[j])]
        for row in inverse:
            row[j] = (row[j] - coefficient * row[i]) % q
    assert product(basis, inverse, q) == identity(width)
    labels = [tuple(rng.randrange(2) for _ in range(n)) for _ in range(width)]
    factors = []
    for i in range(n):
        diagonal_basis = [[labels[j][i] * x for x in row]
                          for j, row in enumerate(basis)]
        factors.append(product(inverse, diagonal_basis, q))
    return factors, set(labels)


def spectral_trials():
    rng = random.Random(20261015)
    records = []
    for n, width, levels in itertools.product((2, 4, 6, 64), (3, 6), (2, 4, 8)):
        q = 1 << levels
        factors, expected = conjugated_family(n, width, q, rng)
        for p in factors:
            assert product(p, p, q) == p
            for r in factors:
                assert product(p, r, q) == product(r, p, q)
        states, counts = public_patterns(factors, q)
        patterns = [label for label, _ in states]
        assert set(patterns) == expected
        exhaustive = 0
        if n <= 6:
            for bits in itertools.product((0, 1), repeat=n):
                e = identity(width)
                for bit, p in zip(bits, factors):
                    e = product(e, p if bit else difference(identity(width), p, q), q)
                assert nonzero(e) == (bits in expected)
                exhaustive += 1
        g = [[rng.randrange(q) for _ in range(width)] for _ in range(2)]
        result, nodes = complement_tree(patterns, factors, g, q)
        assert not nonzero(result)
        assert nodes <= 2 * n * width + 1
        records.append(dict(key_bits=n, factor_width=width, modulus=q,
                            public_patterns=[list(b) for b in patterns],
                            maximum_prefix_states=max(counts),
                            complement_tree_nodes=nodes,
                            exhaustive_pattern_checks=exhaustive))
    return records


def native_witness(levels):
    q, width = 1 << levels, 3 * levels
    g = [[(1 << (j % levels)) if j // levels == i else 0
          for j in range(width)] for i in range(3)]
    secret = [1, -1, -1]  # GSWOperations.extendedSecret of the key (1,1).
    phase_g = product([secret], g, q)[0]
    vectors, duals = [], []
    for index in (1, 2):
        v = phase_g.copy()
        v[index] = (v[index] + 1) % q
        vectors.append(v)
    a1, a2 = [0] * width, [0] * width
    a1[0], a1[2] = 5, -1
    a2[0], a2[1] = 3, -1
    duals.extend((a1, a2))
    factors = [[[x * y % q for y in v] for x in a]
               for a, v in zip(duals, vectors)]
    controls = [product(g, p, q) for p in factors]
    errors = []
    for c, p in zip(controls, factors):
        assert product(p, p, q) == p
        assert product(c, p, q) == c
        phase = product([secret], c, q)[0]
        error = [(x - y + q // 2) % q - q // 2 for x, y in zip(phase, phase_g)]
        assert max(map(abs, error)) == 1
        assert phase[levels - 1] == q // 2
        errors.append(error)
    assert not nonzero(product(factors[0], factors[1], q))
    assert not nonzero(product(factors[1], factors[0], q))
    assert not nonzero(product(controls[0], factors[1], q))
    nand = difference(g, product(controls[0], factors[1], q), q)
    assert nand == g
    states, counts = public_patterns(factors, q)
    patterns = [label for label, _ in states]
    assert set(patterns) == {(0, 0), (0, 1), (1, 0)}
    assert (1, 1) not in patterns
    complement, nodes = complement_tree(patterns, factors, g, q)
    assert not nonzero(complement)
    return dict(modulus=q, levels=levels, key=[1, 1], gadget=g, factors=factors,
                controls=controls, control_errors=errors,
                control_noise_bounds=[1, 1], control_selected_bits=[1, 1],
                mixed_product_selected_bit=0, expected_product_bit=1,
                nand_selected_bit=1, expected_nand_bit=0,
                public_patterns=[list(b) for b in patterns],
                maximum_prefix_states=max(counts), complement_tree_nodes=nodes,
                complement_ciphertext_zero=True, expected_complement_bit=1,
                limitations='Algebraic witness only; factors are not canonical digits, '
                            'not short, and not sampled by a secure control generator.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    families = spectral_trials()
    witnesses = [native_witness(levels) for levels in (4, 8, 16)]
    totals = dict(families=len(families),
                  exhaustive_pattern_checks=sum(x['exhaustive_pattern_checks'] for x in families),
                  complement_trees=len(families) + len(witnesses),
                  native_witnesses=len(witnesses),
                  maximum_key_bits=max(x['key_bits'] for x in families))
    result = dict(scope='Fixed globally commuting idempotent factors; public spectral list '
                        'and polynomial-size key-selected decision-tree correctness filter.',
                  limitations='Not an attack on arbitrary GSW bootstrapping. The semantic '
                              'list implication requires correctness for the constructed '
                              'public-list-dependent right-CMux tree; correctness only on '
                              'a narrower refresh family does not imply that premise.',
                  families=families, native_witnesses=witnesses, totals=totals)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(totals, sort_keys=True))


if __name__ == '__main__':
    main()
