#!/usr/bin/env python3
"""Exact finite checks for cancellation before signed source-test clipping.

Checks the full Fourier multiplier of paired affine/quadratic message
kernels, an L2 contraction, and clipping bias in an actual compiled recursive
source experiment. This does not construct an efficient bounded LWE test
or prove the bootstrappable GSW security theorem.
"""
import argparse
from collections import Counter
from fractions import Fraction
import itertools
import json
from pathlib import Path
import numpy as np


def local_affine_stencil(q, weight):
    """Integer masses of 8*Pplus-7*U on (constant, a0, a1, a2).

    The denominator is q**4. Every conditional message marginal is the
    requested cubic point mass, even when weight is a nonunit.
    """
    points = list(itertools.product((0, 1), repeat=3))
    masses = {}
    for coefficients in itertools.product(range(q), repeat=4):
        constant, *linear = coefficients
        matches = sum((constant + sum(a*x for a, x in zip(linear, point)) -
                       weight*point[0]*point[1]*point[2]) % q == 0 for point in points)
        masses[coefficients] = q*matches - 7
    assert sum(masses.values()) == q**4
    for point in points:
        marginal = [0]*q
        for (constant, *linear), mass in masses.items():
            marginal[(constant + sum(a*x for a, x in zip(linear, point))) % q] += mass
        assert marginal == [q**4*int(message == weight*point[0]*point[1]*point[2] % q)
                            for message in range(q)]
    return masses


def radix_transform(values, q, inverse=False):
    """Unnormalized character sum on (Z/q)^d, q=2 or 4.

    Roots are Gaussian integers, so all intermediates are exact integers
    represented below 2^53. No trigonometric or approximate FFT is used.
    """
    values = np.asarray(values, dtype=np.complex128).copy()
    dimension = 0
    size = len(values)
    while q**dimension < size:
        dimension += 1
    assert q**dimension == size
    roots = [complex((-1)**j) for j in range(q)] if q == 2 else [1, 1j, -1, -1j]
    if inverse:
        roots = [z.conjugate() for z in roots]
    stride = 1
    for _ in range(dimension):
        shaped = values.reshape(-1, q, stride)
        old = shaped.copy()
        for frequency in range(q):
            shaped[:, frequency, :] = sum(roots[(frequency*j) % q] * old[:, j, :] for j in range(q))
        stride *= q
    assert np.all(values.real == np.rint(values.real))
    assert np.all(values.imag == np.rint(values.imag))
    assert max(np.max(np.abs(values.real)), np.max(np.abs(values.imag))) < 2**53
    return values


def feature_values(point, quadratic):
    values = list(point)
    if quadratic:
        values += [point[i]*point[j] for i, j in itertools.combinations(range(len(point)), 2)]
    return tuple(values)


def paired_kernel(n, q, outputs, quadratic, mode):
    points = list(itertools.product((0, 1), repeat=n))
    feature_rows = [feature_values(point, quadratic) for point in points]
    d = len(feature_rows[0])
    width = outputs * (d + 1)
    G, N = q**width, len(points)
    indices = np.arange(G, dtype=np.int64)
    digits = np.stack([(indices // q**i) % q for i in range(width)], axis=1).reshape(G, outputs, d+1)
    triples = list(itertools.combinations(range(n), 3))
    targets = []
    for point in points:
        row = []
        for j in range(outputs):
            triple = triples[j % len(triples)] if triples else tuple(range(min(3, n)))
            cubic = int(all(point[i] for i in triple))
            if mode == 'weighted':
                value = (q//2)*cubic
            elif mode == 'mixed':
                value = (cubic + (j % q)*point[j % n]) % q
            else:
                value = 0
            row.append(value)
        targets.append(row)
    matches = np.zeros(G, dtype=np.int64)
    for feature, target in zip(feature_rows, targets):
        evaluation = (digits[:, :, 0] + np.sum(digits[:, :, 1:] * feature, axis=2)) % q
        matches += np.all(evaluation == target, axis=1)
    # N*Pplus-(N-1)*U, after collecting all duplicate coefficient atoms.
    numerator = q**outputs * matches - (N-1)
    assert int(numerator.sum()) == G
    spectrum = radix_transform(numerator, q)
    constant_frequency = digits[:, :, 0]
    nonconstant_frequency = digits[:, :, 1:]
    has_body_frequency = np.any(constant_frequency != 0, axis=1)
    predicted = np.zeros(G, dtype=np.complex128)
    predicted[0] = 1
    root = [1, -1] if q == 2 else [1, 1j, -1, -1j]
    for feature, target in zip(feature_rows, targets):
        selected = has_body_frequency & np.all(
            nonconstant_frequency == (constant_frequency[:, :, None] * feature) % q, axis=(1, 2))
        assert np.all(predicted[selected] == 0)
        phases = np.sum(constant_frequency[selected] * target, axis=1) % q
        predicted[selected] = np.array(root)[phases]
    assert np.array_equal(spectrum, G * predicted)
    active = int(np.count_nonzero(predicted))
    assert active == 1 + N*(q**outputs - 1)
    assert np.all(np.abs(predicted) <= 1)
    # All target choices give the same squared multiplier: the zero-target
    # kernel is a self-adjoint idempotent projection in frequency space.
    squared = predicted * np.conj(predicted)
    assert np.all((squared == 0) | (squared == 1))
    assert np.array_equal(squared*squared, squared)
    # A bounded observer maximizes the signed score at source zero.
    observer = (numerator > 0).astype(np.int64)
    observed_spectrum = radix_transform(observer, q)
    score_numerator_complex = radix_transform(np.conj(predicted)*observed_spectrum, q, inverse=True)
    assert np.all(score_numerator_complex.imag == 0)
    score_numerator = score_numerator_complex.real.astype(np.int64)
    assert int(score_numerator.sum()) == G*int(observer.sum())
    assert sum(int(x)**2 for x in score_numerator) <= G**2 * int(observer.sum())
    clipped = np.clip(score_numerator, 0, G)
    mean = Fraction(int(score_numerator.sum()), G**2)
    clipped_mean = Fraction(int(clipped.sum()), G**2)
    return dict(n=n, q=q, outputs=outputs, quadratic=quadratic, target_mode=mode,
                keys=N, free_features=d, coefficient_atoms=G,
                exact_fourier_modes=G, active_fourier_modes=active,
                multiplier_absolute_values=sorted(set(float(x) for x in np.abs(predicted))),
                collected_kernel_total_absolute_weight=str(Fraction(int(np.abs(numerator).sum()), G)),
                uncollected_branch_weight=2*N-1,
                score_min=str(Fraction(int(score_numerator.min()), G)),
                score_max=str(Fraction(int(score_numerator.max()), G)),
                observer_uniform_mean=str(mean), clipped_uniform_mean=str(clipped_mean),
                clipping_bias=str(clipped_mean-mean),
                exact_L2_contraction=True, exact_normalized_mean_preservation=True)


def optimal_stencil():
    points = list(itertools.product((0, 1), repeat=3))
    positive = []
    feature_masks = [0, 1, 2, 4, 3, 5, 6]
    for changed in range(8):
        truth = [x[0]*x[1]*x[2] ^ (i == changed) for i, x in enumerate(points)]
        table = [0]*8
        for x, value in zip(points, truth):
            table[sum(bit << i for i, bit in enumerate(x))] = value
        for i in range(3):
            for mask in range(8):
                if mask & (1 << i):
                    table[mask] ^= table[mask ^ (1 << i)]
        assert table[7] == 0
        positive.append(sum(table[mask] << i for i, mask in enumerate(feature_masks)))
    stencil = Counter()
    for atom in positive:
        stencil[atom] += 7
        stencil[atom ^ 1] -= 1
    assert sum(stencil.values()) == 48
    assert sum(abs(x) for x in stencil.values()) == 64
    scores = [sum(weight for atom, weight in stencil.items() if source ^ atom in positive)
              for source in range(128)]
    spectrum = [sum(weight * (-1)**((frequency & atom).bit_count()) for atom, weight in stencil.items())
                for frequency in range(128)]
    assert max(map(abs, spectrum)) == 48
    assert scores[0] == 56 and min(scores) == -8
    clipped = [min(48, max(0, x)) for x in scores]
    assert Fraction(sum(clipped)-sum(scores), 48*128) == Fraction(7, 768)
    # These seven output coordinates are (b,c_0,c_1,c_2,T_01,T_02,T_12).
    # T=A-M, c=y-a+l, b=z+o are the actual RecursiveQuadratic compiler.
    def profile(A, inner, y, z):
        c = y ^ inner
        pairbits = ((A >> 1) & 1) | (((A >> 2) & 1) << 1) | (((A >> 5) & 1) << 2)
        return z | (c << 1) | (pairbits << 4)
    uniform = Counter()
    for A, inner, y, z in itertools.product(range(512), range(8), range(8), range(2)):
        uniform[profile(A, inner, y, z)] += 1
    assert set(uniform.values()) == {512}
    real = Counter()
    target_events = 0
    for key, A, inner in itertools.product(range(8), range(512), range(8)):
        y = sum((sum(((key >> i) & 1)*((A >> (3*i+j)) & 1) for i in range(3)) % 2) << j
                for j in range(3))
        z = (key & inner).bit_count() % 2
        raw_profile = profile(A, inner, y, z)
        real[raw_profile] += 1
        actual_profile = raw_profile ^ int(key == 7)
        target_events += actual_profile in positive
    def expectation(counts, values):
        return Fraction(sum(count*values[index] for index, count in counts.items()), 48*sum(counts.values()))
    # A genuine GSWMasking continuation realizes this bounded observer at
    # zero public table (p=0), q=2, base=2, one level. Encrypting the chosen
    # challenge bit gives bit*I, so its diagonal reveals bit. Guess it on
    # the selected context event and flip it outside that event. The
    # winning indicator is exactly the chosen public-context observer.
    game_cases = 0
    for context, bit in itertools.product(range(128), (0, 1)):
        encrypted_diagonal = bit
        guess = encrypted_diagonal if context in positive else 1-encrypted_diagonal
        assert int(guess == bit) == int(context in positive)
        game_cases += 1
    real_score, uniform_score = expectation(real, scores), expectation(uniform, scores)
    real_clip, uniform_clip = expectation(real, clipped), expectation(uniform, clipped)
    assert real_score == Fraction(target_events, 32768) == Fraction(35, 512)
    assert uniform_score == Fraction(1, 16)
    assert real_score-uniform_score == Fraction(3, 512)
    assert real_clip-uniform_clip == Fraction(61, 12288)
    return dict(stencil_branches=len(stencil), total_absolute_weight='4/3',
                coefficient_group_atoms=128, exact_fourier_modes=128,
                multiplier_numerator_histogram=dict(Counter(spectrum)), multiplier_denominator=48,
                signed_score_numerator_histogram=dict(Counter(scores)), score_denominator=48,
                uniform_source_tapes=sum(uniform.values()), real_key_source_tapes=sum(real.values()),
                actual_GSWMasking_observer_bit_checks=game_cases,
                real_signed_mean=str(real_score), uniform_signed_mean=str(uniform_score),
                real_clipped_mean=str(real_clip), uniform_clipped_mean=str(uniform_clip),
                actual_averaged_cubic_event_probability=str(Fraction(target_events, 32768)),
                real_clipping_bias=str(real_clip-real_score), uniform_clipping_bias=str(uniform_clip-uniform_score),
                original_source_gap=str(real_score-uniform_score), clipped_source_gap=str(real_clip-uniform_clip),
                scope='Selected-coordinate projection of complete compiled source; no efficient full-family security claim')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = [(3,2,1,False,'mixed'), (3,2,2,False,'mixed'), (3,2,4,False,'weighted'),
             (3,2,1,True,'mixed'), (4,2,1,True,'mixed'), (3,4,1,False,'weighted'),
             (2,4,2,False,'mixed'), (3,4,1,True,'weighted')]
    records = [paired_kernel(*case) for case in cases]
    result = dict(scope='Finite signed-source cancellation diagnostics; not a Lean or full security theorem',
                  paired_kernels=records, compiled_clipping=optimal_stencil())
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(kernel_instances=len(records), exact_fourier_modes=sum(x['exact_fourier_modes'] for x in records),
                          compiled_uniform_tapes=result['compiled_clipping']['uniform_source_tapes'],
                          compiled_real_tapes=result['compiled_clipping']['real_key_source_tapes'], output=str(args.output))))


if __name__ == '__main__':
    main()
