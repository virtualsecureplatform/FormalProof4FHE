# Binary-NTT finite-field root backend

`BinaryNTTRootBackend.lean` closes the concrete backend obligations of the
regular quadratic-hint to Binary-NTT reduction.

The module provides:

- a deterministic exhaustive square-root selector over every finite decidable
  linearly ordered commutative ring;
- proof that the selected value squares to the input whenever the input is a
  square;
- a certified `ZMod q` coordinate-root implementation;
- an exact equivalence between functions into coordinate units and units of
  the product ring;
- independent uniform coordinate-unit sampling with the exact canonical
  uniform product-ring-unit law; and
- the complete normalized signed-root distribution theorem instantiated with
  the exhaustive backend.

The exhaustive algorithm is suitable as a specification and executable test
backend. A production implementation should use Tonelli--Shanks or another
finite-field square-root algorithm and prove the same `root(value)^2=value`
certificate. No security theorem depends on which deterministic root is
selected because independent sign bits erase its orientation exactly.

This closes the deferred discriminant-root theorem. It does not reduce
Binary-NTT RLWE to conventional RLWE; that remains a separate cryptographic
research problem.

Principal declarations:

- `squareCandidates`
- `exhaustiveSquareRoot`
- `exhaustiveSquareRoot_sq_of_isSquare`
- `exhaustiveCoordinateSquareRoot`
- `zmodCoordinateSquareRoot`
- `coordinateUnitsEquiv`
- `coordinateUnitSampler`
- `coordinateUnitSampler_uniform_evalDist`
- `exhaustive_normalizedSignedRootSampler_uniform_evalDist`
