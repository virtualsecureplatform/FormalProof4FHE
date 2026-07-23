/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CoefficientAffineCircularRLWE
import FormalProof4FHE.TFHE.RingSquareUnitGuessCheck

/-!
# Obstruction to the Direct Coefficient-Guess Action in Rank-One RLWE

The ordinary vector-LWE search-to-decision reduction guesses one secret coordinate.  For a
rank-one ring sample, its exact analogue would choose a uniform ring pad `u`, add a public
perturbation `L(u)` to the ring challenge, and add `u * V` to the body, where `V` is the
candidate value of a secret-dependent ring message `M(S)`.  The correct branch requires

`S * L(u) = u * M(S)`

for every supported secret and every pad.  A wrong branch with unit `V-M(S)` would then be
exactly uniform by the same tape bijection as the whole-secret test.

This file proves a sharp algebraic obstruction to the correct branch.  Substituting `u=1`
shows that any such public action forces `M(S)` to be multiplication of `S` by the single fixed
ring element `L(1)`.  The previously proved coefficient-affine diagonal theorem shows that the
first Boolean coefficient projector is not of this form in degree at least two.  Therefore the
direct vector-LWE coordinate trick cannot be transplanted to production rank-one RLWE, even
before considering noise.  The theorem concerns this natural exact pad-action class; it does
not rule out approximate/noise-changing reductions or reductions using a larger public
representation.
-/

namespace FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.GuessCheckObstruction

noncomputable section

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE

/-- An exact rank-one ring-pad action for a secret-dependent ring message.  The perturbation is
public and may be an arbitrary function of the pad; no linearity assumption is needed. -/
def ExactRingPadAction
    (q degree : ℕ)
    (message : (Fin degree → Bool) → RLWE.Rq q degree) : Prop :=
  ∃ perturbation : RLWE.Rq q degree → RLWE.Rq q degree,
    ∀ (secret : Fin degree → Bool) (pad : RLWE.Rq q degree),
      embedBinaryPolynomial q degree secret * perturbation pad =
        pad * message secret

/-- Executable left multiplication by one, including the degenerate degree-zero carrier where
the available operation dictionaries are only extensionally equal. -/
private theorem rq_one_mul (q degree : ℕ) (value : RLWE.Rq q degree) :
    (1 : RLWE.Rq q degree) * value = value := by
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree => exact one_mul value

/-- Any exact ring-pad action collapses at pad one to an ordinary fixed ring
multiplication. -/
theorem ringMultiplicationOnBinary_of_exactRingPadAction
    (q degree : ℕ)
    (message : (Fin degree → Bool) → RLWE.Rq q degree)
    (haction : ExactRingPadAction q degree message) :
    RingMultiplicationOnBinary q degree message := by
  rcases haction with ⟨perturbation, hcorrect⟩
  refine ⟨perturbation 1, fun secret ↦ ?_⟩
  have hone := hcorrect secret 1
  rw [rq_one_mul] at hone
  exact hone.symm

/-- Equivalence form: an exact ring-pad action is possible only if its message is already in
the ring-linear class absorbed by ordinary rank-one RLWE challenge translation. -/
theorem exactRingPadAction_implies_ringLinear
    (q degree : ℕ)
    (message : (Fin degree → Bool) → RLWE.Rq q degree) :
    ExactRingPadAction q degree message →
      RingMultiplicationOnBinary q degree message :=
  ringMultiplicationOnBinary_of_exactRingPadAction q degree message

/-- **No exact coordinate-guess action.**  For every nontrivial coefficient modulus and ring
degree at least two, the first Boolean coefficient projector admits no public pad action
`L` satisfying `S*L(u)=u*(S_0)` on all binary secrets. -/
theorem firstDiagonal_no_exactRingPadAction
    (q extra : ℕ) [NeZero q] (hq : (1 : ZMod q) ≠ 0) :
    ¬ ExactRingPadAction q (extra + 2)
      (selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)) := by
  intro haction
  exact firstDiagonal_not_ringMultiplicationOnBinary q extra hq
    (ringMultiplicationOnBinary_of_exactRingPadAction q (extra + 2)
      (selectedCoefficientPolynomial q (extra + 2)
        (firstCoordinate extra) (firstCoordinate extra)) haction)

/-- The same obstruction stated for the actual rank-one native diagonal-cross message. -/
theorem nativeFirstDiagonalCross_no_exactRingPadAction
    (q extra : ℕ) [NeZero q] (hq : (1 : ZMod q) ≠ 0) :
    ¬ ExactRingPadAction q (extra + 2)
      (fun secret ↦
        FormalProof4FHE.TFHE.Native.FullBRKQuadraticSpan.diagonalCrossAtDegree
          q (extra + 2) 1
          (fun _ ↦ secret) 0 (firstCoordinate extra) 0) := by
  intro haction
  exact nativeFirstDiagonalCross_not_ringMultiplicationOnBinary q extra hq
    (ringMultiplicationOnBinary_of_exactRingPadAction q (extra + 2)
      (fun secret ↦
        FormalProof4FHE.TFHE.Native.FullBRKQuadraticSpan.diagonalCrossAtDegree
          q (extra + 2) 1
          (fun _ ↦ secret) 0 (firstCoordinate extra) 0) haction)

end

end FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.GuessCheckObstruction
