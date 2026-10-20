#!/usr/bin/env python3
"""Exact two-phase certificates beyond the sparse-table parity obstruction.

Projects the full signed kernel onto two decryption phases. A negative
projected atom certifies a negative full-law event; positivity of this
projection is never used to certify positivity of the full ciphertext law.
No efficient attack or completed ordinary-LWE reduction is claimed.
"""
import argparse
from collections import Counter
from fractions import Fraction
import importlib.util
import itertools
import json
from pathlib import Path
import random
import time

import numpy as np

_spec = importlib.util.spec_from_file_location(
    "rerandomization", Path(__file__).with_name("check-gsw-public-rerandomization.py"))
_gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gate)


def subset_counts(residues, q, rounds):
    counts = np.zeros(q, dtype=object)
    counts[0] = 1
    for _ in range(rounds):
        for residue in residues:
            counts = counts+np.roll(counts, residue)
    assert sum(counts) == 1 << (len(residues)*rounds)
    return counts


def verify_pair_marginals():
    """Check every projected atom for every distinct pair of three-bit keys."""
    checks = []
    points = list(itertools.product((0, 1), repeat=3))
    for q in (2, 4, 8):
        for level in range(q.bit_length()-1):
            weight = 1 << level
            masses = _gate._signed_source.local_affine_stencil(q, weight)
            entries = 0
            for first, second in itertools.combinations(points, 2):
                marginal = Counter()
                for (constant, *linear), mass in masses.items():
                    x = (constant+sum(a*s for a, s in zip(linear, first))) % q
                    y = (constant+sum(a*s for a, s in zip(linear, second))) % q
                    marginal[x, y] += mass
                first_target = weight*first[0]*first[1]*first[2]
                second_target = weight*second[0]*second[1]*second[2]
                for x, y in itertools.product(range(q), repeat=2):
                    expected = q*int(x == first_target % q)+q*int(y == second_target % q)-1
                    assert marginal[x, y] == expected*q**2
                    entries += 1
            checks.append(dict(q=q, weight=weight, exact_pair_atoms=entries))
    # An independent direct coin convolution checks the projected formula
    # after rerandomization, rather than only before adding the public walk.
    rng = random.Random(912)
    walk_entries = 0
    for q in (4, 8):
        first, second = (0, 1, 0), (1, 1, 1)
        table = [_gate.fresh_zero(first, q, 1, rng)[0] for _ in range(3)]
        residues_first = [_gate.phase(first, column, q) for column in table]
        residues_second = [_gate.phase(second, column, q) for column in table]
        first_counts = subset_counts(residues_first, q, 1)
        second_counts = subset_counts(residues_second, q, 1)
        masses = _gate._signed_source.local_affine_stencil(q, q//2)
        observed = Counter()
        for selectors in itertools.product((0, 1), repeat=3):
            rfirst = sum(x*y for x, y in zip(selectors, residues_first)) % q
            rsecond = sum(x*y for x, y in zip(selectors, residues_second)) % q
            for (constant, *linear), mass in masses.items():
                x = (rfirst+constant+sum(a*s for a, s in zip(linear, first))) % q
                y = (rsecond+constant+sum(a*s for a, s in zip(linear, second))) % q
                observed[x, y] += mass
        for x, y in itertools.product(range(q), repeat=2):
            numerator = (q*first_counts[x] + q*second_counts[(y-q//2) % q]-8)
            assert observed[x, y] == numerator*q**2
            walk_entries += 1
    return dict(kernel_checks=checks, directly_convolved_pair_atoms=walk_entries)


def large_table_case(q, key, radius, seed):
    samples = 13*(q.bit_length()-1)+17
    rng = random.Random(5510+q+100*sum(key)+seed)
    generated = [_gate.fresh_zero(key, q, radius, rng) for _ in range(samples)]
    table = [column for column, _ in generated]
    errors = [error for _, error in generated]
    wrong_key = (1-key[0], key[1], key[2])
    wrong_residues = [_gate.phase(wrong_key, column, q) for column in table]
    full_group = 13
    reduced_table = [sum((coordinate & 1) << i for i, coordinate in enumerate(column)) for column in table]
    parity_certificate = _gate.anchor_obstruction(reduced_table, _gate.CipherGroup(2))
    records = []
    for rounds in (1, 2):
        real_counts = subset_counts([e % q for e in errors], q, rounds)
        wrong_counts = subset_counts(wrong_residues, q, rounds)
        denominator = 1 << (samples*rounds)
        half_turns = wrong_residues.count(q//2)
        missing = int(sum(count == 0 for count in real_counts))
        minimum = min(wrong_counts)
        nonuniform = q*minimum < denominator
        # No factor 1+exp(2*pi*i*v/q) vanishes at frequency one.
        # Its product is nonzero, so the subset law cannot be uniform,
        # regardless of the finite number of rerandomization rounds.
        if half_turns == 0:
            assert nonuniform
        width = rounds*sum(abs(e) for e in errors)
        if width+1 < q:
            assert missing > 0
        witness = None
        if missing and nonuniform:
            x = next(i for i, count in enumerate(real_counts) if count == 0)
            y = next(i for i, count in enumerate(wrong_counts) if count == minimum)
            numerator = q*minimum-denominator
            assert numerator < 0
            witnesses = []
            for level in range(q.bit_length()-1):
                weight = 1 << level
                target = weight*key[0]*key[1]*key[2]
                wrong_target = weight*wrong_key[0]*wrong_key[1]*wrong_key[2]
                witnesses.append(dict(weight=weight, real_phase=(target+x) % q,
                                      wrong_phase=(wrong_target+y) % q))
            witness = dict(two_phase_negative_numerator=str(numerator),
                           denominator=str(q*q*denominator),
                           signed_event_mass=str(Fraction(numerator, q*q*denominator)),
                           unshifted_real_phase=x, unshifted_wrong_phase=y,
                           all_gadget_levels=witnesses)
        below = sum(max(denominator-q*int(count), 0) for count in wrong_counts)
        tv = Fraction(below, q*denominator)
        negative_lower = Fraction(missing, q)*tv
        records.append(dict(rounds=rounds, samples=samples, error_support_width=width,
                            real_phase_support=q-missing, wrong_phase_min_count=str(minimum),
                            walk_denominator=str(denominator), wrong_phase_exactly_uniform=not nonuniform,
                            wrong_phase_TV_from_uniform=str(tv),
                            full_law_negative_mass_lower_bound=str(negative_lower),
                            wrong_half_turn_columns=half_turns,
                            no_half_turn_obstruction=half_turns == 0,
                            strict_control_decoding_bound=4*(1+rounds*samples)*4*radius < q,
                            exact_negative_event=witness))
    return dict(q=q, samples=samples, key=list(key), wrong_key=list(wrong_key), error_radius=radius,
                seed=seed, full_ciphertext_coordinates=full_group,
                retained_table=[list(column) for column in table],
                unwrapped_public_errors=errors, wrong_phase_residues=wrong_residues,
                modulo_two_obstruction=parity_certificate,
                probability_bad_half_turn_union_bound=str(Fraction(samples, q)), cases=records)


def family_envelopes():
    result = []
    for parameter in (16, 32, 64, 128):
        a = parameter+1
        n = 2*a**5
        d = n*n+n+1
        q_exponent = a*a
        samples = d*q_exponent+2*parameter+1
        radius = 1 << a
        for rounds in (1, 2):
            width = rounds*samples*(n+1)*radius
            control_bound = (1+rounds*samples)*(n+1)*radius
            allowed_phase_count = min(1 << q_exponent, 2*control_bound+1)
            # Conditional subset-error leakage has at most width+1 values.
            leakage = min(1 << q_exponent, width+1)
            # Conservative strong-LHL smoothing bound uses leakage <= q:
            # delta^2 <= q^(d-1)*q/(4*2^p) = 2^(-2*parameter-3).
            delta_squared = Fraction(1, 1 << (2*parameter+3))
            result.append(dict(parameter=parameter, rounds=rounds, dimension=n,
                               modulus_exponent=q_exponent, public_samples=str(samples),
                               subset_error_range_size_upper_bound=str(leakage),
                               real_phase_gap_guaranteed=width+1 < 1 << q_exponent,
                               no_half_turn_failure_probability_upper_bound=dict(
                                   numerator=str(samples), denominator_power_of_two=q_exponent),
                               wrong_anchor_noise_window_probability_upper_bound=dict(
                                   numerator=str(allowed_phase_count), denominator_power_of_two=q_exponent),
                               derived_smoothing_bound_squared=str(delta_squared),
                               derived_single_kernel_positive_approximation_bound_squared=str(225*delta_squared),
                               scope="Mathematical strong-LHL bound, not an instantiated efficient simulator or Lean theorem"))
    return result


def verify_noise_aware_leftover_hash():
    """Exhaust all retained tables, preserving subset-error side information.

    The group coordinates model the uniform coordinates of a zero-phase
    hyperplane. The error coordinate is never thrown away or randomized.
    This checks a statistical bound, not an efficient positive sampler.
    """
    records = []
    for q, dimensions, errors in (
            (2, 1, (-1, 0, 1, 1, 0, -1)),
            (2, 2, (-1, 0, 1, 1)),
            (4, 1, (-1, 0, 1, 1)),
            (8, 1, (-1, 0, 1, 1)),
            (4, 1, (-1, 0, 1, 1, 0, -1))):
        group = list(itertools.product(range(q), repeat=dimensions))
        selectors = list(itertools.product((0, 1), repeat=len(errors)))
        fiber = Counter(sum(bit*error for bit, error in zip(bits, errors)) % q
                        for bits in selectors)
        size, coins = len(group), len(selectors)
        tv_sum = Fraction()
        tv_squared_sum = Fraction()
        chi_sum = Fraction()
        tables = 0
        for table in itertools.product(group, repeat=len(errors)):
            joint = Counter()
            for bits in selectors:
                error = sum(bit*value for bit, value in zip(bits, errors)) % q
                hashed = tuple(sum(bit*column[i] for bit, column in zip(bits, table)) % q
                               for i in range(dimensions))
                joint[error, hashed] += 1
            # Compare (error, hash_B(bits)) to (error, independent uniform).
            # Averaging TV over retained B is exactly joint TV with B retained.
            tv = Fraction(sum(abs(size*joint[error, output]-count)
                              for error, count in fiber.items() for output in group),
                          2*coins*size)
            chi = sum(Fraction(size*sum(joint[error, output]**2 for output in group),
                               coins*count) for error, count in fiber.items())-1
            assert 4*tv*tv <= chi
            tv_sum += tv
            tv_squared_sum += tv*tv
            chi_sum += chi
            tables += 1
        average_tv = tv_sum/tables
        average_tv_squared = tv_squared_sum/tables
        average_chi = chi_sum/tables
        # Distinct binary selectors collide with probability exactly 1/|G|,
        # including within each fixed-error fiber.
        assert average_chi == Fraction((size-1)*len(fiber), coins)
        assert 4*average_tv*average_tv <= 4*average_tv_squared <= average_chi
        records.append(dict(modulus=q, hyperplane_dimensions=dimensions,
                            fixed_column_errors=list(errors), public_tables=tables,
                            coins_per_table=coins, subset_error_fibers=len(fiber),
                            retained_table_and_error_TV=str(average_tv),
                            mean_conditional_TV_squared=str(average_tv_squared),
                            exact_mean_chi_squared=str(average_chi),
                            strong_LHL_bound_squared=str(Fraction(size*len(fiber), 4*coins))))
    return dict(scope="Exhaustive statistical finite checks; no sampling algorithm or Lean theorem",
                cases=records)


def verify_public_rejection_obstruction():
    """Keep the proposal's anchor label instead of hiding it in the mixture.

    A wrong anchor gives a uniform true phase, even after an independent
    public walk. A public rejection filter returning one of T proposals
    can therefore return a correctly phased wrong-anchor proposal with
    probability at most T*|allowed_phases|/q. This covers this proposal
    and filter class, not arbitrary positive/source-dependent simulators.
    """
    points = list(itertools.product((0, 1), repeat=3))
    records = []
    for q in (2, 4, 8):
        for level in range(q.bit_length()-1):
            weight = 1 << level
            checks = proposals = 0
            for secret, anchor in itertools.product(points, repeat=2):
                phases = Counter()
                for linear in itertools.product(range(q), repeat=3):
                    # The shift can be any fixed walk output. Independence
                    # of the affine coefficients permits averaging over it.
                    walk_shift = q//2-1
                    constant = weight*anchor[0]*anchor[1]*anchor[2]
                    phase = (constant+sum(a*(s-r) for a, s, r in zip(linear, secret, anchor))+
                             walk_shift) % q
                    phases[phase] += 1
                    proposals += 1
                target = (weight*secret[0]*secret[1]*secret[2]+walk_shift) % q
                for value in range(q):
                    expected = q**3*int(value == target) if anchor == secret else q**2
                    assert phases[value] == expected
                    checks += 1
            records.append(dict(modulus=q, gadget_weight=weight,
                                labeled_anchor_proposals=proposals,
                                exact_anchor_phase_atoms=checks,
                                wrong_anchor_uniform_cases=56))
    # This is the direct signed-branch estimator, with a fair independent
    # observer output. Smoothing does not change its internal sign weights.
    variances = []
    for controls in (1, 2, 4, 8, 16, 32):
        tickets = 15**controls
        positive, negative = (tickets+1)//2, (tickets-1)//2
        assert positive+negative == tickets and positive-negative == 1
        mean = Fraction(tickets*(positive-negative), 2*tickets)
        second_moment = Fraction(tickets*tickets, 2)
        variance = second_moment-mean*mean
        assert mean == Fraction(1, 2)
        assert variance == Fraction(2*225**controls-1, 4)
        variances.append(dict(controls=controls, absolute_branch_weight=str(tickets),
                              signed_score_mean=str(mean), signed_score_variance=str(variance)))
    return dict(scope="Candidate-specific labeled-proposal and direct-estimator checks; no general impossibility theorem",
                retained_anchor_checks=records, direct_branch_estimator=variances)


def verify_existing(path):
    """Replay saved events with a separate pure-Python modular recurrence."""
    result = json.loads(path.read_text())
    assert result["pair_checks"] == verify_pair_marginals()
    assert result["noise_aware_leftover_hash_checks"] == verify_noise_aware_leftover_hash()
    assert result["public_rejection_obstruction_checks"] == verify_public_rejection_obstruction()
    assert result["family_envelopes"] == family_envelopes()
    expected_grid = set(itertools.product((512, 2048, 8192, 32768),
                                         ((0, 0, 0), (1, 0, 1), (1, 1, 1)), range(2)))
    observed_grid = set()
    events = 0

    def counts_direct(residues, modulus, rounds):
        counts = [1]+[0]*(modulus-1)
        for _ in range(rounds):
            for residue in residues:
                counts = [count+counts[(index-residue) % modulus]
                          for index, count in enumerate(counts)]
        return counts

    for table_record in result["tables"]:
        q, key = table_record["q"], tuple(table_record["key"])
        seed, radius = table_record["seed"], table_record["error_radius"]
        grid_entry = q, key, seed
        assert grid_entry not in observed_grid
        observed_grid.add(grid_entry)
        table = table_record["retained_table"]
        errors = table_record["unwrapped_public_errors"]
        wrong_key = tuple(table_record["wrong_key"])
        samples = len(table)
        rng = random.Random(5510+q+100*sum(key)+seed)
        replay = [_gate.fresh_zero(key, q, radius, rng) for _ in range(samples)]
        assert [list(column) for column, _ in replay] == table
        assert [error for _, error in replay] == errors
        assert samples == 13*(q.bit_length()-1)+17 == table_record["samples"]
        assert table_record["full_ciphertext_coordinates"] == 13

        def projected(column, secret):
            return (column[-1]+sum(secret[j]*column[9+j] for j in range(3))-
                    sum(secret[i]*secret[j]*column[3*i+j]
                        for i, j in itertools.product(range(3), repeat=2))) % q

        assert all(len(column) == 13 and all(0 <= value < q for value in column) for column in table)
        assert all(projected(column, key) == error % q and abs(error) <= 4*radius
                   for column, error in zip(table, errors))
        wrong_residues = [projected(column, wrong_key) for column in table]
        assert wrong_residues == table_record["wrong_phase_residues"]
        reduced = [sum((coordinate % 2) << i for i, coordinate in enumerate(column)) for column in table]
        assert table_record["modulo_two_obstruction"] == _gate.anchor_obstruction(reduced, _gate.CipherGroup(2))
        assert table_record["probability_bad_half_turn_union_bound"] == str(Fraction(samples, q))
        assert [case["rounds"] for case in table_record["cases"]] == [1, 2]
        for case in table_record["cases"]:
            rounds = case["rounds"]
            first = counts_direct([error % q for error in errors], q, rounds)
            second = counts_direct(wrong_residues, q, rounds)
            denominator = 1 << (samples*rounds)
            assert sum(first) == sum(second) == denominator
            missing = first.count(0)
            minimum = min(second)
            tv = Fraction(sum(max(denominator-q*count, 0) for count in second), q*denominator)
            assert case["walk_denominator"] == str(denominator)
            assert case["real_phase_support"] == q-missing
            assert case["wrong_phase_min_count"] == str(minimum)
            assert case["wrong_phase_exactly_uniform"] == (q*minimum == denominator)
            assert case["wrong_phase_TV_from_uniform"] == str(tv)
            assert case["full_law_negative_mass_lower_bound"] == str(Fraction(missing, q)*tv)
            assert case["wrong_half_turn_columns"] == wrong_residues.count(q//2)
            assert case["no_half_turn_obstruction"] == (q//2 not in wrong_residues)
            assert case["error_support_width"] == rounds*sum(abs(error) for error in errors)
            assert case["strict_control_decoding_bound"] == (16*(1+rounds*samples)*radius < q)
            witness = case["exact_negative_event"]
            assert witness is not None
            x, y = witness["unshifted_real_phase"], witness["unshifted_wrong_phase"]
            numerator = q*(first[x]+second[y])-denominator
            assert numerator < 0 and first[x] == 0 and second[y] == minimum
            assert witness["two_phase_negative_numerator"] == str(numerator)
            assert witness["denominator"] == str(q*q*denominator)
            assert witness["signed_event_mass"] == str(Fraction(numerator, q*q*denominator))
            assert witness["all_gadget_levels"] == [dict(
                weight=1 << level,
                real_phase=(x+(1 << level)*key[0]*key[1]*key[2]) % q,
                wrong_phase=(y+(1 << level)*wrong_key[0]*wrong_key[1]*wrong_key[2]) % q)
                for level in range(q.bit_length()-1)]
            events += 1
    assert observed_grid == expected_grid
    assert events == result["summary"]["exact_negative_events"] == 48
    assert result["summary"] == dict(
        tables=len(observed_grid), cases=events,
        without_previous_parity_obstruction=sum(
            table["modulo_two_obstruction"]["necessary_positivity_condition"]
            for table in result["tables"]),
        exact_negative_events=events,
        negative_events_with_decoding_margin=sum(
            case["strict_control_decoding_bound"]
            for table in result["tables"] for case in table["cases"]))
    print(json.dumps(dict(independently_replayed_tables=len(observed_grid),
                          independently_replayed_negative_events=events)), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--verify-existing", type=Path)
    args = parser.parse_args()
    if args.verify_existing:
        verify_existing(args.verify_existing)
        return
    start = time.monotonic()
    checks = verify_pair_marginals()
    tables = []
    for q in (512, 2048, 8192, 32768):
        for key, seed in itertools.product(((0, 0, 0), (1, 0, 1), (1, 1, 1)), range(2)):
            tables.append(large_table_case(q, key, 1, seed))
        print(json.dumps(dict(completed_modulus=q, tables=len(tables))), flush=True)
    records = [record for table in tables for record in table["cases"]]
    result = dict(scope="Exact larger-table projected negative-event certificates, not a security attack",
                  argument="phase gap + nonuniform wrong-key subset law implies negative two-phase atom",
                  pair_checks=checks, tables=tables, family_envelopes=family_envelopes(),
                  noise_aware_leftover_hash_checks=verify_noise_aware_leftover_hash(),
                  public_rejection_obstruction_checks=verify_public_rejection_obstruction(),
                  summary=dict(tables=len(tables), cases=len(records),
                               without_previous_parity_obstruction=sum(table["modulo_two_obstruction"]["necessary_positivity_condition"]
                                   for table in tables),
                               exact_negative_events=sum(record["exact_negative_event"] is not None for record in records),
                               negative_events_with_decoding_margin=sum(record["exact_negative_event"] is not None and
                                   record["strict_control_decoding_bound"] for record in records)))
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(dict(**result["summary"], elapsed_seconds=round(time.monotonic()-start, 2))), flush=True)


if __name__ == "__main__":
    main()
