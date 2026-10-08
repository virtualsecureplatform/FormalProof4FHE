#!/usr/bin/env python3
"""Reproduce public-link disclosure under a receiver-known key.

Uses the WHT26 matrix dimensions and public GSW pad-encryption/link equations.
This is a correctness diagnostic at small dimension, not a security parameter
instantiation or a formalization of the entire multi-key protocol. The attack
requires the receiver's key. It does not attack the one-key specialization
against an adversary who has no decryption key.

Requires NumPy. Run from the repository: python3 scripts/research/wht26_link_audit.py
"""
from __future__ import annotations

import json
import numpy as np


def centered(value: int, modulus: int) -> int:
    residue = value % modulus
    return residue if 2 * residue <= modulus else residue - modulus


def recover_residue(samples: list[int]) -> int:
    """Read only the noisy gadget multiples; one observation per recovered bit."""
    levels = len(samples)
    modulus = 1 << levels
    half = modulus // 2
    prefix = 0
    for steps in range(levels):
        level = levels - steps - 1
        residual = (samples[level] - prefix * (1 << level)) % modulus
        bit = abs(centered(residual - half, modulus)) < abs(centered(residual, modulus))
        prefix += int(bit) << steps
    return prefix


def recover_sender(public_hint: np.ndarray, public_link: np.ndarray,
                   receiver_key: list[int], unit_row: int, levels: int) -> list[int]:
    """Attack inputs contain no sender secret, subset bits, or encryption coins."""
    modulus = 1 << levels
    rows = len(receiver_key)
    assert receiver_key[unit_row] % modulus == 1
    phases = [sum(receiver_key[row] *
                  (int(public_hint[row, column]) - int(public_link[row, column]))
                  for row in range(rows)) % modulus
              for column in range(rows * rows * levels)]
    return [recover_residue(phases[(unit_row * rows + coordinate) * levels:
                                  (unit_row * rows + coordinate + 1) * levels])
            for coordinate in range(rows)]


def run_audit() -> dict[str, object]:
    rows, levels = 2, 40
    modulus, mask = 1 << levels, (1 << levels) - 1
    samples = 2 * rows * levels
    width, columns = rows * levels, rows * rows * levels
    rng = np.random.default_rng(41007)
    sender_key, receiver_key = [-5, 1], [-7, 1]
    selector_errors = np.array([1 if i % 2 == 0 else mask
                                for i in range(samples)], dtype=np.uint64)

    def public_key(secret: list[int]) -> np.ndarray:
        challenge = rng.integers(0, modulus, size=samples, dtype=np.uint64)
        body = ((-secret[0]) * challenge + selector_errors) & np.uint64(mask)
        return np.stack((challenge, body))

    receiver_public_key = public_key(receiver_key)
    sender_public_key = public_key(sender_key)
    seed = rng.integers(0, modulus, size=(rows, samples), dtype=np.uint64)
    subset_bits = rng.integers(0, 2, size=(samples, columns), dtype=np.uint64)
    core = (seed @ subset_bits) & np.uint64(mask)
    hint = np.zeros((rows, columns), dtype=np.uint64)
    gadget = np.zeros((rows, width), dtype=np.uint64)
    for row in range(rows):
        for level in range(levels):
            gadget[row, row * levels + level] = 1 << level
        for coordinate in range(rows):
            for level in range(levels):
                hint[row, (row * rows + coordinate) * levels + level] = (
                    sender_key[coordinate] * (1 << level)) % modulus
    public_hint = (core + hint) & np.uint64(mask)
    digits = np.stack([(seed[row] >> np.uint64(level)) & np.uint64(1)
                       for row in range(rows) for level in range(levels)], axis=1)
    public_link = np.zeros_like(public_hint)
    for column in range(columns):
        # Fresh public GSW encryptions of all subset bits in this column.
        coins = rng.integers(0, 2, size=(samples, samples, width), dtype=np.uint64)
        pad_ciphertexts = np.einsum('rs,usc->urc', receiver_public_key, coins,
                                   optimize=False)
        pad_ciphertexts = (pad_ciphertexts +
                           subset_bits[:, column, None, None] * gadget[None, :, :]) & np.uint64(mask)
        # Sparse L_{u,v} has D[:,u] in column v and zero in every other column.
        # This is the corresponding column of sum V_{u,v} * G^{-1}(L_{u,v}).
        public_link[:, column] = np.einsum('urc,uc->r', pad_ciphertexts, digits,
                                          optimize=False) & np.uint64(mask)

    observed_noise = max(abs(centered(sum(receiver_key[row] *
                         (int(public_link[row, column]) - int(core[row, column]))
                         for row in range(rows)), modulus)) for column in range(columns))
    fresh_bound = samples  # All public-key errors have centered magnitude one.
    sharp_link_bound = samples * rows * levels * fresh_bound
    paper_link_bound = samples * rows ** 3 * levels ** 2 * fresh_bound
    assert observed_noise <= sharp_link_bound <= paper_link_bound
    assert 4 * paper_link_bound < modulus
    recovered = recover_sender(public_hint, public_link, receiver_key, rows - 1, levels)
    assert recovered == [value % modulus for value in sender_key]

    challenge_results: list[bool] = []
    for message in [0, 1]:
        coins = rng.integers(0, 2, size=(samples, width), dtype=np.uint64)
        challenge_ciphertext = (sender_public_key @ coins + message * gadget) & np.uint64(mask)
        column = (rows - 1) * levels + levels - 1
        phase = sum(recovered[row] * int(challenge_ciphertext[row, column])
                    for row in range(rows)) % modulus
        decoded = abs(centered(phase - modulus // 2, modulus)) < abs(centered(phase, modulus))
        challenge_results.append(int(decoded) == message)
    assert all(challenge_results)
    return {"rows": rows, "gadget_levels": levels, "modulus_bits": levels,
            "public_key_samples": samples, "hint_columns": columns,
            "observed_link_noise": observed_noise, "sharp_link_bound": sharp_link_bound,
            "paper_link_bound": paper_link_bound,
            "recovered_signed_sender": [centered(value, modulus) for value in recovered],
            "fresh_challenge_decryptions": challenge_results,
            "scope": "public P,Z plus receiver-owned key; no attack claimed on unknown one-key view"}


if __name__ == "__main__":
    print(json.dumps(run_audit(), indent=2))
