# MP all-but-one hash trapdoor layer

`FormalProof4FHE.TFHE.MPAllButOneHashTrapdoor` formalizes the finite algebraic part of applying
Micciancio--Peikert-style tagged trapdoors to the hash-CMUX route.  It separates that reusable
part from the distributional and implementation claims that still need a concrete construction.

## Full-rank-difference tags

`FullRankDifferenceEncoding R Digest Target` contains a linear encoding `F` such that

```text
y != yStar  implies  F(y) - F(yStar) is bijective.
```

The encoding is explicitly injective.  Therefore `tagDifference_eq_zero_iff` proves that the
programmed digest is exactly the unique zero tag, while `differenceEquiv` packages every wrong
candidate's tag as a linear equivalence.

`MatrixFullRankDifferenceEncoding` exposes the usual determinant criterion.  The theorem
`toLinear` turns a square matrix family whose nonzero differences have unit determinant into the
abstract linear interface.  `ofLocalMap` also proves the useful lifting step: if reduction along a
local ring homomorphism sends every difference determinant to a unit, it was already a unit over
the source ring.  This is the algebraic bridge needed to validate a matrix tag family over a
residue field and use it over a local power-of-two coefficient ring.

This module does not select a particular digest encoding or claim that an arbitrary production
coefficient ring admits one of the desired digest size.  That remains a concrete construction
obligation.

## Programmed and injective modes

For source map `A`, gadget map `G`, trapdoor `R`, and programmed digest `yStar`, the candidate mask
is defined literally by

```text
B_y = (F(y) - F(yStar)) G - R A.
```

Lean proves the complete linear-map identity

```text
B_y + R A = (F(y) - F(yStar)) G.
```

At `y = yStar`, `programmedCandidate_kernelRelation` specializes it to

```text
B_yStar + R A = 0,
```

and `programmedCandidate_phase` removes the gadget message exactly.  For every `y != yStar`, the
inverse difference tag normalizes both the mask and its phase.  The checked theorems are

```text
D_y^(-1) B_y + (D_y^(-1) R) A = G

D_y^(-1) phase_y
  = -G(s) + D_y^(-1)(correction - R(sourceError)).
```

Thus the zero/injective branch distinction and all associated signs are no longer informal
proof steps.

## Security accounting

`allButOneHashCMUXSecurity_le` composes a supplied tagged-mode defect with the existing
candidate-based hash-CMUX theorem.  The tagged defect is charged once, outside the balanced-hash
square-root coefficient.  `allButOneDirectProjectedSecurity_le` does the same for the direct
projected route, which has no additional candidate-guessing multiplier.

These are accounting theorems, not a construction of the mode switch.  In particular, the
following obligations remain explicit:

- a concrete full-rank-difference matrix family for the selected digest and coefficient ring;
- regularity or pseudorandomness of the trapdoor-generated public matrix;
- a short preimage sampler with a proved finite CBD or discrete-Gaussian output law and noise
  bound;
- a source-aligned compiler from the tagged complete view to every native TFHE nonce row; and
- the encrypted hash/equality and CMUX endpoint certificates already exposed by the hash-CMUX
  module.

The workspace references `../refs/2011-501.pdf` and `../refs/trapdoor/` (paths relative to this
repository root) motivate the MP and ring/module trapdoor interfaces.  They do not by themselves
prove the above native-TFHE compiler or its joint distributional claims.
