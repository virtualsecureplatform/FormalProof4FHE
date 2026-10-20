#!/usr/bin/env python3
"""Exact full-ciphertext feasibility gate for public signed-kernel smoothing.

The secret is unchanged. Every retained public column is an actual recursive
zero ciphertext (T,c,b), with phase b+s*c-s*T*s. We convolve the local cubic
signed compiler kernel with L independent binary subset sums of that table.
All probabilities are integer masses over the full 13-coordinate ciphertext.
No projected marginal certifies positivity, and finite positivity is not a
production-family security or efficient-sampling theorem.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import importlib.util
import itertools
import json
from pathlib import Path
import random
import time

import numpy as np

_spec = importlib.util.spec_from_file_location(
    "signed_source", Path(__file__).with_name("check-gsw-signed-source-cancellation.py"))
_signed_source = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_signed_source)


class CipherGroup:
    """Packed coordinatewise addition, with no cross-coordinate carries."""
    def __init__(self, q):
        assert q in (2, 4, 8)
        self.q = q
        self.bits = q.bit_length()-1
        self.low = sum(1 << (self.bits*i) for i in range(13))
        self.carry_mask = ((1 << (13*self.bits))-1) ^ self.low

    def pack(self, coordinates):
        assert len(coordinates) == 13
        return sum((int(value) % self.q) << (self.bits*i) for i, value in enumerate(coordinates))

    def unpack(self, word):
        return tuple((int(word) >> (self.bits*i)) & (self.q-1) for i in range(13))

    def add(self, first, second):
        if self.q == 2:
            return first ^ second
        for _ in range(self.bits):
            first, second = first ^ second, ((first & second) << 1) & self.carry_mask
        assert second == 0
        return first

    def phase_function(self, key):
        positive = (1 << (12*self.bits)) | sum(1 << ((9+i)*self.bits) for i in range(3) if key[i])
        negative = sum(1 << ((3*i+j)*self.bits) for i in range(3) for j in range(3) if key[i]*key[j])
        if self.q == 2:
            return lambda word: (int(word) & (positive | negative)).bit_count() & 1
        return lambda word: sum((1 << bit)*(((int(word) >> bit) & positive).bit_count()-
                                           ((int(word) >> bit) & negative).bit_count())
                                for bit in range(self.bits)) % self.q

    def neg(self, word):
        return self.add(((1 << (13*self.bits))-1) ^ word, self.low)


def centered(value, q):
    return (value+q//2) % q-q//2


def phase(key, coordinates, q):
    return (coordinates[12] + sum(key[i]*coordinates[9+i] for i in range(3)) -
            sum(key[i]*coordinates[3*i+j]*key[j] for i in range(3) for j in range(3))) % q


def fresh_zero(key, q, radius, rng):
    matrix = [rng.randrange(q) for _ in range(9)]
    inner = [rng.randrange(q) for _ in range(3)]
    errors = [rng.randint(-radius, radius) for _ in range(3)]
    body_error = rng.randint(-radius, radius)
    vector = [(sum(key[i]*matrix[3*i+j] for i in range(3))-inner[j]+errors[j]) % q
              for j in range(3)]
    body = (sum(key[i]*inner[i] for i in range(3))+body_error) % q
    coordinates = tuple(matrix+vector+[body])
    unwrapped_phase = body_error+sum(key[i]*errors[i] for i in range(3))
    assert phase(key, coordinates, q) == unwrapped_phase % q
    assert abs(unwrapped_phase) <= 4*radius
    return coordinates, unwrapped_phase


def binary_basis(vectors):
    basis = {}
    for vector in vectors:
        while vector:
            pivot = vector.bit_length()-1
            if pivot not in basis:
                basis[pivot] = vector
                break
            vector ^= basis[pivot]
    return basis


def reduce_binary(vector, basis):
    for pivot in sorted(basis, reverse=True):
        if (vector >> pivot) & 1:
            vector ^= basis[pivot]
    return vector


def binary_solve(rows, right):
    basis = {}
    for row, value in zip(rows, right):
        while row:
            pivot = row.bit_length()-1
            if pivot not in basis:
                basis[pivot] = (row, value)
                break
            row ^= basis[pivot][0]
            value ^= basis[pivot][1]
        if row == 0 and value:
            return None
    solution = 0
    for pivot in sorted(basis):
        row, value = basis[pivot]
        solution |= (value ^ ((row & solution).bit_count() & 1)) << pivot
    assert all((row & solution).bit_count() % 2 == value for row, value in zip(rows, right))
    return solution


def parity_word(group, word):
    return sum(((int(word) >> (group.bits*i)) & 1) << i for i in range(13))


def anchor_obstruction(table, group):
    """Exact modulo-two certificate, valid for any positive round count.

    In the quotient by the table's binary span, two distinct surviving
    anchor characters have unit expectations but their product has zero
    expectation. Their simultaneous opposite-sign event has mass -1/4.
    """
    reduced_table = [parity_word(group, word) for word in table]
    rows = [word & 511 for word in reduced_table]
    candidates = []
    extensions = []
    for anchor in range(8):
        fixed = (anchor << 9) | (1 << 12)
        right = [(fixed & word).bit_count() % 2 for word in reduced_table]
        solution = binary_solve(rows, right)
        if solution is not None:
            normal = fixed | solution
            assert all((normal & word).bit_count() % 2 == 0 for word in reduced_table)
            candidates.append(anchor)
            extensions.append(normal)
    return dict(anchor_count=len(candidates), anchors=candidates,
                public_character_extensions=extensions,
                necessary_positivity_condition=len(candidates) <= 1,
                negative_event_mass="-1/4" if len(candidates) >= 2 else None,
                negative_event_description="both of the first two surviving anchor characters have the opposite target sign",
                scope="modulo-two necessary condition for every q=2^k and every L>=1")


def binary_key_recovery(table, group, key):
    """A polynomial Gaussian attack certificate for the noiseless baseline."""
    basis = binary_basis(table)
    if len(basis) != 12:
        return dict(rank=len(basis), uniquely_recovered=False)
    free = next(i for i in range(13) if i not in basis)
    normal = 1 << free
    for pivot in sorted(basis):
        normal |= ((basis[pivot] & normal).bit_count() & 1) << pivot
    assert all((normal & column).bit_count() % 2 == 0 for column in table)
    guessed = tuple((normal >> (9+i)) & 1 for i in range(3))
    expected = group.pack(tuple(guessed[i]*guessed[j] for i in range(3) for j in range(3)) +
                          guessed + (1,))
    recovered = normal == expected
    if recovered:
        assert guessed == key or all(phase(guessed, group.unpack(column), 2) == 0 for column in table)
    return dict(rank=len(basis), uniquely_recovered=recovered,
                recovered_actual_key=recovered and guessed == key,
                normal_vector=normal, guessed_key=list(guessed) if recovered else None)


@lru_cache(maxsize=None)
def initial_kernel(q, weight):
    group = CipherGroup(q)
    masses = _signed_source.local_affine_stencil(group.q, weight)
    result = {}
    for (constant, *linear), mass in masses.items():
        result[group.pack((0,)*9+tuple(linear)+(constant,))] = mass
    return result


def convolve_binary_walk(kernel, table, rounds, group):
    operations = 0
    if group.q == 2:
        values = np.zeros(1 << 13, dtype=np.int64)
        for word, mass in kernel.items():
            values[word] = mass
        indices = np.arange(1 << 13)
        for _ in range(rounds):
            for column in table:
                operations += len(values)
                values = values+values[indices ^ column]
        return {int(i): int(values[i]) for i in np.flatnonzero(values)}, operations
    values = kernel
    for _ in range(rounds):
        for column in table:
            next_values = values.copy()
            operations += len(values)
            for word, mass in values.items():
                shifted = group.add(word, column)
                next_values[shifted] = next_values.get(shifted, 0)+mass
            values = {word: mass for word, mass in next_values.items() if mass}
    return values, operations


def noise_distribution(errors, rounds):
    values = Counter({0: 1})
    for _ in range(rounds):
        for error in errors:
            shifted = Counter()
            for value, count in values.items():
                shifted[value] += count
                shifted[value+error] += count
            values = shifted
    return values


def mask_fibers(table, rounds, group):
    """Full matrix-mask fibers, not a substitute for full-law positivity."""
    mask = (1 << (9*group.bits))-1
    values = Counter({0: 1})
    for _ in range(rounds):
        for column in table:
            shifted = Counter()
            for word, count in values.items():
                shifted[word] += count
                shifted[group.add(word, column & mask)] += count
            values = shifted
    return values


def binary_coset_sampler_certificate(kernel, table, smoothed):
    """Constructive sampler when all coset masses are nonnegative.

    Four random bits select a coset from 16 integer tickets. Independent
    basis bits sample its uniform span. This uses only public Gaussian
    elimination and the constant-size q=2 local stencil.
    """
    basis = binary_basis(table)
    masses = Counter()
    for word, mass in kernel.items():
        masses[reduce_binary(word, basis)] += mass
    assert sum(masses.values()) == 16
    if any(mass < 0 for mass in masses.values()):
        assert any(mass < 0 for mass in smoothed.values())
        return dict(available=False, reason="negative public quotient-coset mass")
    assert all(mass >= 0 for mass in smoothed.values())
    tickets = [word for word, mass in sorted(masses.items()) for _ in range(mass)]
    assert len(tickets) == 16
    # Verify the entire output law by exhaustive basis choices, rather than
    # relying on sampled frequencies.
    span = [0]
    for value in basis.values():
        span += [word ^ value for word in span]
    actual = Counter(word ^ offset for word in tickets for offset in span)
    expected_denominator = 16*(1 << len(table))
    actual_denominator = 16*len(span)
    assert all(actual.get(word, 0)*expected_denominator == mass*actual_denominator
               for word, mass in smoothed.items())
    assert len(actual) == len(smoothed)
    rng = random.Random(913)
    assert all(binary_coset_sample(kernel, table, rng) in smoothed for _ in range(16))
    return dict(available=True, basis_rank=len(basis), coin_bound=4+len(basis),
                ticket_count=16, exact_output_atoms_checked=len(actual),
                algorithm="public GF(2) elimination, 16 coset tickets, uniform basis bits",
                production_scope="q=2 only; not polynomial in log(q) for larger moduli by enumeration")


def binary_coset_sample(kernel, table, rng):
    """Executable public sampler; raises if the signed quotient is negative.

    Only use with q=2. It reads no secret and uses 4+rank(table) random bits.
    Enumeration here is the fixed 16-coefficient local stencil, not keys,
    ciphertext outputs, table subsets, or a modulus-dependent state space.
    """
    basis = binary_basis(table)
    masses = Counter()
    for word, mass in kernel.items():
        masses[reduce_binary(word, basis)] += mass
    if any(mass < 0 for mass in masses.values()):
        raise ValueError("signed quotient is not a probability distribution")
    tickets = [word for word, mass in sorted(masses.items()) for _ in range(mass)]
    assert len(tickets) == 16
    word = tickets[rng.getrandbits(4)]
    for vector in basis.values():
        if rng.getrandbits(1):
            word ^= vector
    return word


def run_table(q, samples, key_index, radius, seed):
    key = tuple((key_index >> i) & 1 for i in range(3))
    group = CipherGroup(q)
    phase_word = group.phase_function(key)
    rng = random.Random(20261018+q*100000+samples*1000+key_index*20+radius*10+seed)
    generated = [fresh_zero(key, q, radius, rng) for _ in range(samples)]
    table = [group.pack(column) for column, _ in generated]
    errors = [error for _, error in generated]
    recovery = binary_key_recovery(table, group, key) if q == 2 else None
    obstruction = anchor_obstruction(table, group)
    records = []
    for rounds in ((1,) if q == 2 else (1, 2)):
        fibers = mask_fibers(table, rounds, group)
        noises = noise_distribution(errors, rounds)
        assert sum(noises.values()) == sum(fibers.values()) == 1 << (samples*rounds)
        noise_max = max(map(abs, noises))
        column_bound = 4*radius
        bound = (1+rounds*samples)*column_bound
        assert noise_max <= rounds*samples*column_bound
        for level in range(group.bits):
            weight = 1 << level
            kernel = initial_kernel(q, weight)
            values, operations = convolve_binary_walk(kernel, table, rounds, group)
            denominator = q**4 * (1 << (samples*rounds))
            assert sum(values.values()) == denominator
            negative = sum(-mass for mass in values.values() if mass < 0)
            initial_negative = Fraction(sum(-mass for mass in kernel.values() if mass < 0), q**4)
            assert Fraction(negative, denominator) <= initial_negative
            if not obstruction["necessary_positivity_condition"]:
                assert Fraction(negative, denominator) >= Fraction(1, 4)
            if q == 2:
                # Over F2 this condition is sufficient as well: the quotient
                # kernel has only its constant and at most one sign mode.
                assert (negative == 0) == obstruction["necessary_positivity_condition"]
            # Decryption marginal of the full signed law is exactly the
            # target cubic plus the REAL subset-error law, with no hidden
            # re-randomized key or replacement of the retained table.
            marginal = Counter()
            for word, mass in values.items():
                marginal[phase_word(word)] += mass
            target = weight*key[0]*key[1]*key[2]
            expected = Counter()
            for noise, count in noises.items():
                expected[(target+noise) % q] += q**4*count
            assert all(marginal[value] == expected[value] for value in range(q))
            event_check = None
            if (not obstruction["necessary_positivity_condition"] and seed == 0 and key_index == 0 and
                    radius == 0 and samples == (4 if q == 2 else 1)):
                first, second = obstruction["public_character_extensions"][:2]
                first_anchor, second_anchor = obstruction["anchors"][:2]
                first_wrong = 1 ^ ((weight * int(first_anchor == 7)) & 1)
                second_wrong = 1 ^ ((weight * int(second_anchor == 7)) & 1)
                event_sum = sum(mass for word, mass in values.items()
                                if (parity_word(group, word) & first).bit_count() % 2 == first_wrong
                                and (parity_word(group, word) & second).bit_count() % 2 == second_wrong)
                assert Fraction(event_sum, denominator) == Fraction(-1, 4)
                event_check = "-1/4"
            witness = None
            if negative:
                word = min((word for word in values if values[word] < 0), key=lambda word: (values[word], word))
                witness = dict(ciphertext=list(group.unpack(word)),
                               signed_numerator=values[word], denominator=denominator,
                               signed_probability=str(Fraction(values[word], denominator)),
                               phase=phase_word(word))
            sampler = binary_coset_sampler_certificate(kernel, table, values) if q == 2 else dict(
                available=False, reason="no constructive sampler for the nonbinary bounded-selector kernel")
            erased = None
            if q == 2 and negative == 0:
                if all(error % 2 == 0 for error in errors):
                    assert obstruction["anchors"] == [key_index]
                    recovered_key = tuple((obstruction["anchors"][0] >> i) & 1 for i in range(3))
                    assert recovered_key == key
                    erased = dict(outcome="public Gaussian tests recover the actual three secret bits",
                                  recovered_key=list(recovered_key), rerandomization_bit_error="0")
                else:
                    assert sum(count for noise, count in noises.items() if noise % 2 == 0)*2 == sum(noises.values())
                    erased = dict(outcome="subset-error parity is uniform and erases the control bit",
                                  rerandomization_bit_error="1/2")
            records.append(dict(rounds=rounds, gadget_level=level, weight=weight,
                                full_ciphertext_coordinates=13, nonzero_atoms=len(values),
                                negative_atoms=sum(mass < 0 for mass in values.values()),
                                negative_mass=str(Fraction(negative, denominator)),
                                initial_negative_mass=str(initial_negative), exact_positive=negative == 0,
                                negative_witness=witness, signed_denominator=denominator,
                                convolution_additions=operations, full_mask_fibers=len(fibers),
                                negative_event_full_law_check=event_check,
                                zero_mask_coin_preimages=fibers[0],
                                walk_unwrapped_noise_max=noise_max,
                                control_noise_bound=bound, actual_table_noise_bound=column_bound,
                                strict_half_modulus_decoding_margin=4*bound < q,
                                positive_sampler=sampler, binary_positive_outcome=erased))
    return dict(q=q, samples=samples, key=list(key), error_radius=radius, seed=seed,
                retained_table=[list(column) for column, _ in generated],
                public_column_unwrapped_errors=errors, binary_key_recovery=recovery,
                modulo_two_obstruction=obstruction, cases=records)


def verify_packed_arithmetic():
    rng = random.Random(450)
    cases = 0
    for q in (2, 4, 8):
        group = CipherGroup(q)
        for _ in range(512):
            first = tuple(rng.randrange(q) for _ in range(13))
            second = tuple(rng.randrange(q) for _ in range(13))
            assert group.unpack(group.add(group.pack(first), group.pack(second))) == tuple(
                (x+y) % q for x, y in zip(first, second))
            key = tuple(rng.randrange(2) for _ in range(3))
            assert group.phase_function(key)(group.pack(first)) == phase(key, first, q)
            cases += 1
    return cases


def independent_convolution_checks():
    """Compare packed convolution to direct full-tuple coin enumeration."""
    result = []
    for q, samples in ((2, 2), (4, 1), (8, 1)):
        group = CipherGroup(q)
        weight = q//2
        rng = random.Random(870+q)
        key = (1, 0, 1)
        generated = [fresh_zero(key, q, 1, rng)[0] for _ in range(samples)]
        table = [group.pack(column) for column in generated]
        kernel = initial_kernel(q, weight)
        # Reconstruct the signed numerator from the two actual samplers,
        # without using the match-count formula of local_affine_stencil.
        anchor_counts = Counter({coefficients: -7 for coefficients in itertools.product(range(q), repeat=4)})
        for anchor in itertools.product((0, 1), repeat=3):
            for linear in itertools.product(range(q), repeat=3):
                constant = (weight*anchor[0]*anchor[1]*anchor[2]-
                            sum(a*x for a, x in zip(linear, anchor))) % q
                anchor_counts[(constant, *linear)] += q
        assert anchor_counts == _signed_source.local_affine_stencil(q, weight)
        observed, _ = convolve_binary_walk(kernel, table, 2, group)
        expected = Counter()
        oracle_terms = 0
        for selectors in itertools.product((0, 1), repeat=2*samples):
            translated = tuple(sum(selectors[i]*generated[i % samples][coordinate]
                                   for i in range(2*samples)) % q for coordinate in range(13))
            for (constant, *linear), mass in anchor_counts.items():
                coefficient_tuple = (0,)*9+tuple(linear)+(constant,)
                output = tuple((x+y) % q for x, y in zip(translated, coefficient_tuple))
                expected[output] += mass
                oracle_terms += 1
        expected = {group.pack(coordinates): mass for coordinates, mass in expected.items() if mass}
        assert expected == observed
        result.append(dict(q=q, public_samples=samples, rounds=2, direct_full_tuple_terms=oracle_terms,
                           exact_output_atoms=len(observed)))
    return result


def production_noise_envelopes():
    """Evaluate the original bootstrap budget with the enlarged key bound.

    These exact integers demonstrate noise feasibility at listed parameters;
    they are neither a new Lean eventual theorem nor a sampler certificate.
    """
    result = []
    for parameter in (16, 32, 64, 128):
        a = parameter+1
        n = 2*a**5
        rows = n*n+n+1
        levels = a*a
        samples = rows*levels+2*parameter+1
        lookup = 1 << (8*rows-1).bit_length()
        modulus = 1 << levels
        for rounds in (1, 2):
            key_bound = (1+rounds*samples)*(n+1)*(1 << a)
            growth = rows*levels
            output_bound = lookup*rows*growth*(growth+1)*key_bound
            post_nand = (growth+1)*output_bound
            result.append(dict(parameter=parameter, rounds=rounds, dimension=n,
                               public_samples=str(samples), control_noise_bound=str(key_bound),
                               lookup_exponent=lookup.bit_length()-1, modulus_exponent=levels,
                               scaled_post_nand_bound=str(lookup*post_nand),
                               bootstrap_budget_satisfied=lookup*post_nand < modulus))
    return result


def summarize_tables(tables):
    cases = [case for table in tables for case in table["cases"]]
    return dict(tables=len(tables), full_law_cases=len(cases),
                exact_positive_cases=sum(c["exact_positive"] for c in cases),
                negative_cases=sum(not c["exact_positive"] for c in cases),
                nonbinary_negative_cases=sum(t["q"] > 2 and not c["exact_positive"] for t in tables for c in t["cases"]),
                positive_with_decoding_margin=sum(c["exact_positive"] and c["strict_half_modulus_decoding_margin"] for c in cases),
                certified_sampler_cases=sum(c["positive_sampler"]["available"] for c in cases),
                certified_sampler_with_margin=sum(c["positive_sampler"]["available"] and c["strict_half_modulus_decoding_margin"] for c in cases),
                positive_sampler_reveals_actual_key_cases=sum(c["binary_positive_outcome"] is not None and
                    c["binary_positive_outcome"]["rerandomization_bit_error"] == "0" for c in cases),
                positive_sampler_erases_control_bit_cases=sum(c["binary_positive_outcome"] is not None and
                    c["binary_positive_outcome"]["rerandomization_bit_error"] == "1/2" for c in cases),
                parity_negative_certificate_cases=sum(not t["modulo_two_obstruction"]["necessary_positivity_condition"]
                    for t in tables for _ in t["cases"]),
                explicit_negative_event_full_law_checks=sum(c["negative_event_full_law_check"] is not None for c in cases),
                noiseless_public_key_recovery_tables=sum(t["error_radius"] == 0 and bool(t["binary_key_recovery"] and
                    t["binary_key_recovery"]["uniquely_recovered"]) for t in tables))


def verify_artifact(path):
    """Replay every negative atom using independently enumerated walk coins.

    Binary cases additionally admit an independent quotient-space computation
    of the complete negative mass, support size, and positive sampler law.
    """
    result = json.loads(path.read_text())
    witnessed = binary_laws = positive_samplers = 0
    for table_record in result["tables"]:
        q = table_record["q"]
        group = CipherGroup(q)
        key = tuple(table_record["key"])
        table = [group.pack(column) for column in table_record["retained_table"]]
        errors = table_record["public_column_unwrapped_errors"]
        assert all(phase(key, column, q) == error % q
                   for column, error in zip(table_record["retained_table"], errors))
        assert anchor_obstruction(table, group) == table_record["modulo_two_obstruction"]
        walks = {}
        if q > 2:
            for rounds in (1, 2):
                counts = Counter({(0,)*13: 1})
                # Direct tuples supply a second implementation of the walk.
                for _ in range(rounds):
                    for column in table_record["retained_table"]:
                        updated = counts.copy()
                        for coordinates, count in counts.items():
                            shifted = tuple((x+y) % q for x, y in zip(coordinates, column))
                            updated[shifted] += count
                        counts = updated
                walks[rounds] = [(group.pack(tuple(-x % q for x in coordinates)), count)
                                 for coordinates, count in counts.items()]
        for case in table_record["cases"]:
            kernel = initial_kernel(q, case["weight"])
            denominator = q**4*(1 << (table_record["samples"]*case["rounds"]))
            assert denominator == case["signed_denominator"]
            if q == 2:
                basis = binary_basis(table)
                cosets = Counter()
                for word, count in kernel.items():
                    cosets[reduce_binary(word, basis)] += count
                negative = Fraction(sum(-count for count in cosets.values() if count < 0), 16)
                assert negative == Fraction(case["negative_mass"])
                assert sum(count != 0 for count in cosets.values())*(1 << len(basis)) == case["nonzero_atoms"]
                assert sum(count < 0 for count in cosets.values())*(1 << len(basis)) == case["negative_atoms"]
                binary_laws += 1
                if case["exact_positive"]:
                    assert case["positive_sampler"]["available"]
                    rng = random.Random(419)
                    for _ in range(32):
                        output = binary_coset_sample(kernel, table, rng)
                        assert cosets[reduce_binary(output, basis)] > 0
                    positive_samplers += 1
            witness = case["negative_witness"]
            if witness is not None:
                word = group.pack(witness["ciphertext"])
                if q == 2:
                    mass = cosets[reduce_binary(word, basis)]*(1 << (len(table)-len(basis)))
                else:
                    mass = sum(count*kernel.get(group.add(word, negative_word), 0)
                               for negative_word, count in walks[case["rounds"]])
                assert mass == witness["signed_numerator"] < 0
                assert Fraction(mass, denominator) == Fraction(witness["signed_probability"])
                witnessed += 1
    assert summarize_tables(result["tables"]) == result["summary"]
    print(json.dumps(dict(negative_atoms_replayed=witnessed, binary_full_laws_checked=binary_laws,
                          constructive_samplers_checked=positive_samplers, artifact=str(path))), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-existing", type=Path, help="Independently replay saved witnesses and binary sampler certificates")
    parser.add_argument("--quick", action="store_true", help="One seed instead of the full accepted seed grid")
    args = parser.parse_args()
    if args.verify_existing is not None:
        verify_artifact(args.verify_existing)
        return
    if args.output is None:
        parser.error("--output is required unless --verify-existing is used")
    started = time.monotonic()
    arithmetic_cases = verify_packed_arithmetic()
    oracle_checks = independent_convolution_checks()
    seeds = range(1 if args.quick else 8)
    tables = []
    for q, samples_set in ((2, (4, 8, 12, 16)), (4, (1, 2, 4)), (8, (1, 2))):
        for samples, key, radius, seed in itertools.product(samples_set, range(8), (0, 1), seeds):
            tables.append(run_table(q, samples, key, radius, seed))
        print(json.dumps(dict(completed_modulus=q, tables=len(tables))), flush=True)
    result = dict(scope="Exact public-rerandomization feasibility gate, not full security",
                  gate_outcome="No tested candidate passes constructive sampling, retained secrecy, and correct control decoding together",
                  gate_scope="Stops this tested candidate; does not exclude larger-table nonbinary smoothing or a different simulator",
                  key_dimension=3, full_ciphertext_coordinates=13,
                  kernel="8*paired-local-affine-anchor-law - 7*uniform-affine-law",
                  selectors="independent uniform binary selectors, reused retained table, fresh each round/control",
                  coordinate_order="T row-major (9), c (3), b (1)",
                  sampling_work_note="Exact enumeration is diagnostic; only the GF(2) coset sampler has a polynomial algorithm certificate",
                  arithmetic_checks=arithmetic_cases, direct_convolution_oracles=oracle_checks, tables=tables,
                  production_noise_envelopes=production_noise_envelopes(),
                  summary=summarize_tables(tables))
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(**result["summary"], elapsed_seconds=round(time.monotonic()-started, 2), output=str(args.output))), flush=True)


if __name__ == "__main__":
    main()
