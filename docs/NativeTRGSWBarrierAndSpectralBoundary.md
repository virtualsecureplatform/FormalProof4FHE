# Native TRGSW barrier and spectral boundary

`FormalProof4FHE.TFHE.NativeTRGSWBarrierAndSpectralBoundary` formalizes the finite and algebraic
claims in `sketch/native_trgsw_barrier_and_spectral_boundary.tex`.  It deliberately separates
checked identities from the remaining cryptographic estimate.

## Checked native-row facts

For a split secret `s = E(p) + O(z)`, the body contribution is an explicit public linear
combination of the binary prefix bits.  In contrast, eliminating the hidden raw mask from a nonce
row gives

```text
(A - h p_i) (E(p) + O(z)).
```

The Lean development proves both obstructions from the note:

- suffix variation forces the coefficient of `O(z)` to depend on `p_i`; and
- the mixed Boolean derivative in coordinates `i,j` is exactly `-h E_j`.

Thus no row-local suffix-only plus public-affine-prefix decomposition exists when either
nondegeneracy condition holds.  The unit-embedding corollary uses unit cancellation and therefore
does not incorrectly assume that the quotient ring is an integral domain.  The displayed mask is
also proved exactly uniform and independent of the control bit.  Consequently, for a uniform
control bit and nonzero gadget, every estimator using only the displayed mask recovers the raw
mask with probability at most one half.  Private phase cancellation is proved as a separate
correctness identity.

## Checked normalization and Fourier facts

Negation-symmetric error sampling gives an exact public action on a complete native TGSW
ciphertext.  The action toggles its encrypted bit and applies simultaneously to the mask and body
blocks.  The result is lifted pointwise to a complete independently generated BRK family.

Binary frequencies are proved equivalent to finite subsets.  The development then proves:

- Walsh orthogonality and completeness;
- the exact diagonal Fourier identity;
- exact extraction of one diagonal coefficient by the xor orbit filter;
- the low/high-degree partition;
- the identity
  `N_d = sum_{k=1}^d choose(t,k)` for the number of nonempty low-degree frequencies; and
- the finite-range leakage loss `sqrt(2^(d+1) delta)` from the existing squared-bias theorem.

## Complete-channel certificate

For any finite complete channel `W(v | p,m)`, the module constructs the uniform-input view mass,
the diagonal-parity numerator, and the totalized posterior parity.  It proves the exact finite
quotient formula for the posterior energy, including zero-mass fibers, and proves for every
bounded response `D` that

```text
|Fourier_D(S,S)| <= theta_S.
```

Here the view type can contain the complete BRK, KSK, auxiliary data, and all retained shared
state; the theorem makes no row-independence or marginal-law approximation.  A one-bit point-oracle
witness also proves that public xor normalization plus a nonzero circular gap cannot, as a generic
black-box principle, imply secret prediction.

## Exact remaining premise

The final theorem is conditional on three inputs:

1. the low-degree normalized complete affine-source bound;
2. a bound on the sum of the complete-channel posterior radii above degree `d`; and
3. the random-message/zero-message endpoint bound.

Under those inputs it proves

```text
Adv <= (sum_{k=1}^d choose(t,k)) * sqrt(2^(d+1) delta_d)
       + spectralTail_d + endpointError.
```

The predicate `NativeDiagonalSpectralDecay` records item 2; it is not introduced as an axiom or
asserted for TFHE parameters. `FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel` now instantiates
the finite channel with the actual shared-prefix/suffix BRK plus retained KSK sampler. It proves
that conditioning on a known BRK message gives an affine direct-row normal form, lifts this to an
exact whole-view affine BRK plus retained-KSK distribution, and derives the support-leakage
cardinality automatically. Completing item 1 still requires a hardness reduction for that joint
affine source, recorded as a low-degree affine-source certificate.
`NativeTRGSWSpectralInfeasibility.lean` subsequently proves that this statistical posterior tail
has an exact binomial lower bound whenever the native KSK and BRK are exhaustively decodable with
small error. Thus the remaining high-degree research target is an aggregate computational
replacement, not a negligible unbounded-posterior tail. See
`docs/NativeTRGSWCompleteChannel.md` and `docs/NativeTRGSWSpectralInfeasibility.md`.
