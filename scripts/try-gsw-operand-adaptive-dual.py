#!/usr/bin/env python3
"""Try public idempotent factors with a CMux-operand-dependent right inverse.

Solve GH=CH=I and set P=HC. Optionally choose H using the actual branch
difference, preserving its action on the public lowest-column compression
R (GR=I) as a heuristic. This is an exact-certified finite construction
experiment, not a closed noise invariant or a security proof.
"""
import argparse
import importlib.util
import json
from pathlib import Path

import numpy as np
from fpylll import GSO, IntegerMatrix, LLL

spec = importlib.util.spec_from_file_location(
    'adaptive_dual_body', Path(__file__).with_name('try-gsw-body-adaptive-projection.py'))
body = importlib.util.module_from_spec(spec)
spec.loader.exec_module(body)
t = body.t


class PublicDual:
    """No secret, noise, selected bit, or diagnostic plaintext is an input."""
    def __init__(self, g, control, q, levels):
        self.g, self.control, self.q = g, control, q
        self.rows, self.width = g.shape
        self.system = np.vstack((g, control))
        self.targets = np.vstack((np.eye(self.rows, dtype=np.int64),) * 2)
        self.base = body.public_short_preimages(self.system, self.targets, q)
        self.kernel = t.remaining.lattice_solver(self.system.tolist(), q).kernel_basis()
        assert all(all(sum(int(a) * int(b) for a, b in zip(row, v)) % q == 0
                       for row in self.system) for v in self.kernel)
        self.reference = np.zeros((self.width, self.rows), dtype=np.int64)
        for i in range(self.rows):
            self.reference[i * levels, i] = 1
        assert np.array_equal(g @ self.reference % q, np.eye(self.rows, dtype=np.int64))
        self.cache = {}
        self.certified_builds = self.closest_vector_calls = 0
        self.changed_operand_factors = self.improved_metric_columns = 0
        self.rejected_metric_columns = 0
        self.metric_cost_before = self.metric_cost_after = 0
        self.maximum_dual_entry = self.maximum_factor_entry = 0
        self.base_factor = self.certify(self.base)

    def certify(self, h):
        q = self.q
        assert np.array_equal(self.system @ h % q, self.targets)
        p = h @ self.control % q
        assert np.array_equal(self.g @ p % q, self.control)
        assert np.array_equal(self.control @ p % q, self.control)
        assert np.array_equal(p @ p % q, p)
        self.maximum_dual_entry = max(self.maximum_dual_entry, int(np.max(np.abs(h))))
        self.maximum_factor_entry = max(self.maximum_factor_entry,
                                       max(abs(t.centered(int(x), q)) for x in p.flat))
        self.certified_builds += 1
        return p

    def adaptive_factor(self, difference):
        delta = np.asarray(difference, dtype=np.int64) % self.q
        key = tuple(map(int, delta.flat))
        if key in self.cache:
            return self.cache[key]
        # Here the objective is constant under the prescribed constraints.
        if any(np.array_equal(delta, known % self.q)
               for known in (np.zeros_like(self.g), self.g, -self.g,
                             self.control, -self.control)):
            self.cache[key] = self.base_factor
            return self.base_factor
        q, n, r = self.q, self.width, self.rows
        target = delta @ self.reference % q
        # The lattice contains exactly [v, delta*v-q*z] for v in ker(system).
        # Free q*z lifts make the output-agreement objective modular.
        embedded = []
        for v in self.kernel:
            image = delta @ np.asarray(v, dtype=np.int64)
            embedded.append([*map(int, v), *[t.centered(int(x), q) for x in image]])
        for i in range(r):
            embedded.append([0] * n + [q * int(i == j) for j in range(r)])
        lattice = IntegerMatrix.from_matrix(embedded)
        LLL.reduction(lattice)
        basis = [[int(lattice[i, j]) for j in range(n + r)] for i in range(n + r)]
        # Certify the reduced basis rather than trust floating CVP output.
        for v in basis:
            assert all(sum(int(a) * b for a, b in zip(row, v[:n])) % q == 0
                       for row in self.system)
            assert all((sum(int(a) * b for a, b in zip(row, v[:n])) - z) % q == 0
                       for row, z in zip(delta, v[n:]))
        gso = GSO.Mat(lattice, update=True)
        columns = []
        for j in range(r):
            particular = self.base[:, j]
            image = delta @ particular - target[:, j]
            goal = [*map(int, particular), *[t.centered(int(x), q) for x in image]]
            coefficients = gso.babai(goal)
            nearby = [sum(int(coefficients[i]) * basis[i][k] for i in range(n + r))
                      for k in range(n + r)]
            candidate = [int(x) - y for x, y in zip(particular, nearby[:n])]
            def objective(h):
                residual = delta @ np.asarray(h, dtype=np.int64) - target[:, j]
                return sum(int(x) ** 2 for x in h) + sum(
                    t.centered(int(x), q) ** 2 for x in residual)
            before, after = objective(particular), objective(candidate)
            if after > before:
                candidate, after = list(map(int, particular)), before
                self.rejected_metric_columns += 1
            self.metric_cost_before += before
            self.metric_cost_after += after
            self.improved_metric_columns += after < before
            columns.append(candidate)
            self.closest_vector_calls += 1
        h = np.asarray(columns, dtype=np.int64).T
        p = self.certify(h)
        self.changed_operand_factors += not np.array_equal(p, self.base_factor)
        self.cache[key] = p
        return p


def refresh(ciphertext, controls, builders, levels, q, lookup, policy, stats):
    g = t.gadget(len(controls), levels)
    switched = [(int(x) // (q // lookup)) % lookup for x in ciphertext[:, levels - 1]]
    state = np.zeros((lookup, *g.shape), dtype=np.int64)
    state[switched[0]] = g
    for i in reversed(range(len(controls))):
        old, output = state, []
        builder = builders[i]
        fallback = body.redundant.signed_quarter_digits(controls[i], levels)
        for position in range(lookup):
            difference = (old[(position + switched[i + 1]) % lookup] - old[position]) % q
            if builder is None:
                factor = fallback
                stats['fallback_gate_calls'] += 1
            elif policy == 'fixed_dual':
                factor = builder.base_factor
            else:
                factor = builder.adaptive_factor(difference)
            output.append((old[position] + difference @ factor) % q)
            stats['cmux_gate_calls'] += 1
        state = np.array(output, dtype=np.int64)
    selected = [position for position in range(lookup)
                if abs(t.centered(position - lookup // 2, lookup))
                < abs(t.centered(position, lookup))]
    return np.sum(state[selected], axis=0) % q


def experiment(n, levels, seed, variant):
    q, lookup = 1 << levels, 1 << (4 * (n + 1)).bit_length()
    secret, controls, initial = body.draw(n, levels, 1, seed, variant)
    g = t.gadget(n, levels)
    builders, failures = [], []
    for i, control in enumerate(controls):
        try:
            builders.append(PublicDual(g, control, q, levels))
        except ValueError as error:
            builders.append(None)
            failures.append(dict(control=i, reason=str(error)))
    policies = []
    for policy in ('fixed_dual', 'operand_adaptive_dual'):
        current = [c.copy() for c in initial]
        trials, stats = [], dict(cmux_gate_calls=0, fallback_gate_calls=0)
        for cycle in range(3):
            output = []
            for branch in (0, 1):
                before = current[branch] if cycle == 0 else (
                    g - current[branch] @ body.redundant.signed_quarter_digits(initial[0], levels)) % q
                expected = branch if cycle == 0 else 1
                # Diagnostic only: distinguish erroneous matrix evaluation
                # from a later input that already exceeds the refresh margin.
                switched = [(int(x) // (q // lookup)) % lookup
                            for x in before[:, levels - 1]]
                rounded_phase = (switched[0] - sum(int(bit) * x
                                 for bit, x in zip(secret, switched[1:]))) % lookup
                rounded_bit = int(abs(t.centered(rounded_phase - lookup // 2, lookup))
                                  < abs(t.centered(rounded_phase, lookup)))
                after = refresh(before, controls, builders, levels, q, lookup, policy, stats)
                phase = int(t.phase(after, secret, q)[levels - 1])
                decoded = int(abs(t.centered(phase - q // 2, q)) < abs(t.centered(phase, q)))
                bound = max(map(abs, t.noise(after, expected, secret, g, q)))
                trials.append(dict(cycle=cycle, branch=branch, expected=expected,
                                   rounded_input_bit=rounded_bit,
                                   input_rounding_matches_expected=rounded_bit == expected,
                                   evaluation_matches_rounded_input=decoded == rounded_bit,
                                   selected_correct=decoded == expected, output_noise=bound,
                                   output_margin=4 * bound < q,
                                   next_nand_margin=2 * ((g.shape[1] + 1) * bound +
                                       (n + 1) * (q // lookup - 1)) < q // 2))
                output.append(after)
            current = output
        policies.append(dict(policy=policy, refresh_trials=trials, **stats))
    result = dict(n=n, levels=levels, modulus=q, seed=seed, variant=variant,
                  source_resampled=False, secret_for_diagnostic=secret.tolist(),
                  actual_control_noise_bounds=[max(map(abs, t.noise(c, int(bit), secret, g, q)))
                                               for c, bit in zip(controls, secret)],
                  builder_failures=failures, policies=policies,
                  certified_idempotent_factors=sum(b.certified_builds for b in builders if b),
                  closest_vector_columns=sum(b.closest_vector_calls for b in builders if b),
                  improved_metric_columns=sum(b.improved_metric_columns for b in builders if b),
                  rejected_metric_columns=sum(b.rejected_metric_columns for b in builders if b),
                  metric_cost_before=sum(b.metric_cost_before for b in builders if b),
                  metric_cost_after=sum(b.metric_cost_after for b in builders if b),
                  changed_operand_factors=sum(b.changed_operand_factors for b in builders if b),
                  maximum_dual_entry=max((b.maximum_dual_entry for b in builders if b), default=0),
                  maximum_centered_factor_entry=max((b.maximum_factor_entry for b in builders if b), default=0),
                  distinct_operand_cache_entries=sum(len(b.cache) for b in builders if b),
                  base_noncommuting_pairs=sum(not np.array_equal(a.base_factor @ b.base_factor % q,
                                                                b.base_factor @ a.base_factor % q)
                                              for i, a in enumerate(builders) if a
                                              for b in builders[i + 1:] if b))
    print(json.dumps(dict(n=n, levels=levels, variant=variant, failures=len(failures),
                          correct=[sum(t['selected_correct'] for t in p['refresh_trials'])
                                   for p in policies],
                          factors=result['certified_idempotent_factors'])), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = [experiment(n, levels, seed, variant)
             for n, levels, seed in ((2, 8, 15000), (2, 16, 15010), (3, 8, 15020))
             for variant in ('exact_diagonal', 'full_signed_outer_product')]
    summaries = []
    for policy in ('fixed_dual', 'operand_adaptive_dual'):
        trials = [t for c in cases for p in c['policies'] if p['policy'] == policy
                  for t in p['refresh_trials']]
        summaries.append(dict(policy=policy, refresh_calls=len(trials),
                              selected_correct=sum(t['selected_correct'] for t in trials),
                              evaluation_matches_rounded_input=sum(t['evaluation_matches_rounded_input'] for t in trials),
                              input_rounding_matches_expected=sum(t['input_rounding_matches_expected'] for t in trials),
                              first_cycle_calls=sum(t['cycle'] == 0 for t in trials),
                              first_cycle_selected_correct=sum(t['selected_correct'] for t in trials if t['cycle'] == 0),
                              first_cycle_input_rounding_correct=sum(t['input_rounding_matches_expected'] for t in trials if t['cycle'] == 0),
                              output_margins=sum(t['output_margin'] for t in trials),
                              next_nand_margins=sum(t['next_nand_margin'] for t in trials)))
    totals = dict(cases=len(cases), controls=sum(c['n'] for c in cases),
                  builder_failures=sum(len(c['builder_failures']) for c in cases),
                  certified_idempotent_factors=sum(c['certified_idempotent_factors'] for c in cases),
                  closest_vector_columns=sum(c['closest_vector_columns'] for c in cases),
                  improved_metric_columns=sum(c['improved_metric_columns'] for c in cases),
                  rejected_metric_columns=sum(c['rejected_metric_columns'] for c in cases),
                  metric_cost_before=sum(c['metric_cost_before'] for c in cases),
                  metric_cost_after=sum(c['metric_cost_after'] for c in cases),
                  changed_operand_factors=sum(c['changed_operand_factors'] for c in cases),
                  distinct_operand_cache_entries=sum(c['distinct_operand_cache_entries'] for c in cases),
                  base_noncommuting_pairs=sum(c['base_noncommuting_pairs'] for c in cases))
    result = dict(scope='Public right-inverse projection factors, including actual CMux-operand '
                        'dependence, without global commutation.',
                  limitations='The operand metric is heuristic, not a phase/noise certificate. '
                              'Builder failures are retained with signed-digit fallback; '
                              'no cryptographic parameter, runtime or security theorem is claimed.',
                  cases=cases, summaries=summaries, totals=totals)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(summaries=summaries, totals=totals), sort_keys=True))


if __name__ == '__main__':
    main()
