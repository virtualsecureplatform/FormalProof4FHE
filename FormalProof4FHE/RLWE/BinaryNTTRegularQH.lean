/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BinaryNTTSecurity
import Mathlib.Algebra.Group.Pi.Units

/-!
# Regular quadratic-hint RLWE

This module repairs the conditioning problem in Jain--Lin--Liu--Saha (2026/1730) by changing
the quadratic-hint distribution.  A **regular** quadratic hint is sampled from a secret `s` and a
uniform unit gap `d` by

`u = 2*s + d`, `v = s^2 - u*s`.

Thus `u - 2*s = d` is a unit by construction.  This removes the information-theoretic `N/q`
bad-discriminant mass rather than attempting to bound it.  The low-depth construction only uses
the public equation `s^2 = u*s + v`, so this repair does not change its algebraic interface.

The module checks that all affine transformations in the paper preserve regularity.  It also gives
the exact finite hardness-transfer interfaces for the repaired assumption family.  Instantiating
the reverse QH-to-Binary-NTT direction still requires an executable sampler that selects all
coordinatewise square-root signs uniformly.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.Regular

noncomputable section

/-! ## Direct regular-hint sampler -/

/-- Public `u` generated from a secret and a unit discriminant gap. -/
def hintU {R : Type} [Ring R] (secret : R) (gap : Rˣ) : R :=
  2 * secret + (gap : R)

/-- Public `v` generated from the same data. -/
def hintV {R : Type} [Ring R] (secret : R) (gap : Rˣ) : R :=
  BinaryNTTSecurity.quadraticHint (hintU secret gap) secret

/-- Hidden witness for a regular quadratic hint. -/
structure Witness (R : Type) [Ring R] where
  secret : R
  gap : Rˣ

/-- Project a regular witness to the public hint `(u,v)`. -/
def publicHint {R : Type} [Ring R] (witness : Witness R) : R × R :=
  (hintU witness.secret witness.gap, hintV witness.secret witness.gap)

/-- The direct sampler: sample the desired secret and an independent uniform unit gap. -/
def witnessSampler {R : Type} [Ring R] [SampleableType Rˣ]
    (secretSampler : ProbComp R) : ProbComp (Witness R) := do
  let secret ← secretSampler
  let gap ← $ᵗ Rˣ
  return ⟨secret, gap⟩

/-- The generated hint has the required quadratic equation. -/
theorem hint_equation {R : Type} [CommRing R] (secret : R) (gap : Rˣ) :
    secret ^ 2 = hintU secret gap * secret + hintV secret gap := by
  simp [hintV, BinaryNTTSecurity.quadraticHint]

/-- Its discriminant gap is literally the sampled unit. -/
@[simp]
theorem hint_gap {R : Type} [CommRing R] (secret : R) (gap : Rˣ) :
    hintU secret gap - 2 * secret = (gap : R) := by
  simp [hintU]

theorem hint_gap_isUnit {R : Type} [CommRing R] (secret : R) (gap : Rˣ) :
    IsUnit (hintU secret gap - 2 * secret) := by
  rw [hint_gap]
  exact gap.isUnit

/-- The public discriminant is the square of the sampled unit gap. -/
theorem hint_discriminant {R : Type} [CommRing R] (secret : R) (gap : Rˣ) :
    hintU secret gap ^ 2 + 4 * hintV secret gap = (gap : R) ^ 2 := by
  simp [hintU, hintV, BinaryNTTSecurity.quadraticHint]
  ring

/-- Every square root of a regular discriminant is invertible.  This removes the abort event in
the repaired Theorem 10 independently of how the square root is sampled. -/
theorem discriminantRoot_isUnit {R : Type} [CommRing R]
    (u v secret root : R)
    (hhint : v = BinaryNTTSecurity.quadraticHint u secret)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : root ^ 2 = 4 * v + u ^ 2) : IsUnit root := by
  have hgap : IsUnit (2 * secret - u) := by
    rw [show 2 * secret - u = -(u - 2 * secret) by ring]
    exact hregular.neg
  have hrootUnit : IsUnit (root ^ 2) := by
    rw [hroot, hhint, BinaryNTTSecurity.quadraticHint_discriminant u secret]
    exact hgap.pow 2
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp hrootUnit

/-! ## Executable uniform square-root-sign sampling in split NTT coordinates -/

/-- A deterministic coordinate square-root routine.  The algorithm may choose either root; the
random sign sampler below removes this choice from the resulting secret distribution. -/
structure CoordinateSquareRoot (K : Type) [CommRing K] where
  root : K → K
  square : ∀ value candidate, value = candidate ^ 2 → root value ^ 2 = value

/-- Independently negate a chosen square root in every NTT coordinate. -/
def signedRoot {Slot K : Type} [Neg K]
    (canonical : Slot → K) (signs : Slot → Bool) : Slot → K :=
  fun slot ↦ if signs slot then -canonical slot else canonical slot

/-- Executable probabilistic sampler: one uniform sign bit per NTT coordinate. -/
def signedRootSampler {Slot K : Type} [Neg K]
    [SampleableType (Slot → Bool)] (canonical : Slot → K) : ProbComp (Slot → K) :=
  signedRoot canonical <$> ($ᵗ (Slot → Bool))

/-- Apply a deterministic coordinate square-root routine to an NTT vector. -/
def canonicalRoots {Slot K : Type} [CommRing K]
    (squareRoot : CoordinateSquareRoot K) (values : Slot → K) : Slot → K :=
  fun slot ↦ squareRoot.root (values slot)

/-- Coordinatewise quadratic discriminant. -/
def discriminantCoordinates {Slot K : Type} [CommRing K]
    (u v : Slot → K) : Slot → K :=
  fun slot ↦ u slot ^ 2 + 4 * v slot

/-- Fully public signed-root sampler for a quadratic hint. -/
def regularSignedRootSampler {Slot K : Type} [CommRing K]
    [SampleableType (Slot → Bool)]
    (squareRoot : CoordinateSquareRoot K) (u v : Slot → K) : ProbComp (Slot → K) :=
  signedRootSampler (canonicalRoots squareRoot (discriminantCoordinates u v))

/-- The deterministic roots computed from an honest hint satisfy the required coordinate square
equations. -/
theorem canonicalRoots_regular_square {Slot K : Type} [CommRing K]
    (squareRoot : CoordinateSquareRoot K) (u v secret : Slot → K)
    (hhint : v = BinaryNTTSecurity.quadraticHint u secret) (slot : Slot) :
    canonicalRoots squareRoot (discriminantCoordinates u v) slot ^ 2 =
      (2 * secret slot - u slot) ^ 2 := by
  have hvalue : discriminantCoordinates u v slot = (2 * secret slot - u slot) ^ 2 := by
    simp only [discriminantCoordinates]
    rw [hhint]
    change u slot ^ 2 + 4 * BinaryNTTSecurity.quadraticHint u secret slot = _
    rw [show BinaryNTTSecurity.quadraticHint u secret slot =
        BinaryNTTSecurity.quadraticHint (u slot) (secret slot) by
      simp [BinaryNTTSecurity.quadraticHint]]
    rw [add_comm, BinaryNTTSecurity.quadraticHint_discriminant]
  unfold canonicalRoots
  exact (squareRoot.square _ _ hvalue).trans hvalue

theorem signedRoot_sq {Slot K : Type} [CommRing K]
    (canonical : Slot → K) (signs : Slot → Bool) (slot : Slot) :
    signedRoot canonical signs slot ^ 2 = canonical slot ^ 2 := by
  by_cases hsign : signs slot <;> simp [signedRoot, hsign]

/-- A regular coordinate gap is nonzero. -/
theorem regularGap_coordinate_ne_zero {Slot K : Type} [Field K]
    (u secret : Slot → K) (hregular : IsUnit (u - 2 * secret)) (slot : Slot) :
    2 * secret slot - u slot ≠ 0 := by
  have hcoordinate : IsUnit ((u - 2 * secret) slot) :=
    (Pi.isUnit_iff.mp hregular) slot
  have hne : u slot - 2 * secret slot ≠ 0 := isUnit_iff_ne_zero.mp hcoordinate
  intro hzero
  apply hne
  linear_combination -hzero

/-- Every chosen coordinate root of a regular discriminant is nonzero. -/
theorem canonicalRoot_coordinate_ne_zero {Slot K : Type} [Field K]
    (u secret canonical : Slot → K)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2)
    (slot : Slot) : canonical slot ≠ 0 := by
  intro hzero
  have hsquare := hroot slot
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hsquare
  have : 2 * secret slot - u slot = 0 := by
    exact (sq_eq_zero_iff).mp hsquare.symm
  exact regularGap_coordinate_ne_zero u secret hregular slot this

/-- Consequently every signed root is nonzero. -/
theorem signedRoot_coordinate_ne_zero {Slot K : Type} [Field K]
    (u secret canonical : Slot → K) (signs : Slot → Bool)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2)
    (slot : Slot) : signedRoot canonical signs slot ≠ 0 := by
  by_cases hsign : signs slot
  · simp only [signedRoot, hsign, if_true, neg_ne_zero]
    exact canonicalRoot_coordinate_ne_zero u secret canonical hregular hroot slot
  · simp only [signedRoot, hsign]
    exact canonicalRoot_coordinate_ne_zero u secret canonical hregular hroot slot

/-- The complete signed root is a unit of the split NTT product ring. -/
theorem signedRoot_isUnit {Slot K : Type} [Field K]
    (u secret canonical : Slot → K) (signs : Slot → Bool)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2) :
    IsUnit (signedRoot canonical signs) := by
  rw [Pi.isUnit_iff]
  intro slot
  exact isUnit_iff_ne_zero.mpr
    (signedRoot_coordinate_ne_zero u secret canonical signs hregular hroot slot)

/-- Turn the signed root into the unit consumed by `inverseTransformSecret`. -/
noncomputable def signedRootUnit {Slot K : Type} [Field K]
    (u secret canonical : Slot → K) (signs : Slot → Bool)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2) :
    (Slot → K)ˣ :=
  (signedRoot_isUnit u secret canonical signs hregular hroot).unit

@[simp]
theorem signedRootUnit_val {Slot K : Type} [Field K]
    (u secret canonical : Slot → K) (signs : Slot → Bool)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2) :
    (signedRootUnit u secret canonical signs hregular hroot : Slot → K) =
      signedRoot canonical signs := by
  exact (signedRoot_isUnit u secret canonical signs hregular hroot).unit_spec

/-- Whether the deterministic root routine selected the negative root in one coordinate. -/
def rootOrientation {Slot K : Type} [Ring K] [DecidableEq K]
    (u secret canonical : Slot → K) : Slot → Bool :=
  fun slot ↦ decide (canonical slot ≠ 2 * secret slot - u slot)

/-- Every deterministic root of a square over a field is one of the two signed roots. -/
theorem canonicalRoot_eq_oriented {Slot K : Type} [Field K] [DecidableEq K]
    (u secret canonical : Slot → K)
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2)
    (slot : Slot) :
    canonical slot =
      if rootOrientation u secret canonical slot then
        -(2 * secret slot - u slot)
      else 2 * secret slot - u slot := by
  by_cases heq : canonical slot = 2 * secret slot - u slot
  · simp [rootOrientation, heq]
  · have hneg : canonical slot = -(2 * secret slot - u slot) :=
      ((sq_eq_sq_iff_eq_or_eq_neg).mp (hroot slot)).resolve_left heq
    simp [rootOrientation, hneg]

/-- One-coordinate secret normalization used by Figure 2. -/
def normalizeCoordinate {K : Type} [Field K] (u secret root : K) : K :=
  (secret + (root - u) / 2) / root

/-- Normalize the public signed root coordinatewise as in Figure 2. -/
def normalizedSignedRootSampler {Slot K : Type} [Field K]
    [SampleableType (Slot → Bool)]
    (squareRoot : CoordinateSquareRoot K) (u v secret : Slot → K) :
    ProbComp (Slot → K) := do
  let root ← regularSignedRootSampler squareRoot u v
  return fun slot ↦ normalizeCoordinate (u slot) (secret slot) (root slot)

theorem normalizeCoordinate_eq_one {K : Type} [Field K]
    (u secret root : K) (htwo : (2 : K) ≠ 0)
    (hroot : root = 2 * secret - u) (hrootNe : root ≠ 0) :
    normalizeCoordinate u secret root = 1 := by
  subst root
  unfold normalizeCoordinate
  rw [div_eq_iff hrootNe]
  field_simp [htwo]
  ring

theorem normalizeCoordinate_eq_zero {K : Type} [Field K]
    (u secret root : K) (htwo : (2 : K) ≠ 0)
    (hroot : root = -(2 * secret - u)) (hrootNe : root ≠ 0) :
    normalizeCoordinate u secret root = 0 := by
  subst root
  unfold normalizeCoordinate
  rw [div_eq_zero_iff]
  left
  field_simp [htwo]
  ring

/-- Coordinate representation of the normalized secret produced from sampled signs. -/
def normalizedSignedSecret {Slot K : Type} [Field K]
    (u secret canonical : Slot → K) (signs : Slot → Bool) : Slot → K :=
  fun slot ↦ normalizeCoordinate (u slot) (secret slot) (signedRoot canonical signs slot)

/-- Boolean-vector embedding matching the two possible normalized roots. -/
def binaryFromSigns {Slot K : Type} [Zero K] [One K]
    (orientation signs : Slot → Bool) : Slot → K :=
  fun slot ↦ if xor (orientation slot) (signs slot) then 0 else 1

/-- Pointwise normalization is exactly a Boolean vector.  The deterministic square-root choice
only XORs a fixed orientation into the fresh uniform signs. -/
theorem normalizedSignedSecret_eq_binaryFromSigns
    {Slot K : Type} [Field K] [DecidableEq K]
    (u secret canonical : Slot → K) (signs : Slot → Bool)
    (htwo : (2 : K) ≠ 0)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2) :
    normalizedSignedSecret u secret canonical signs =
      binaryFromSigns (rootOrientation u secret canonical) signs := by
  funext slot
  have hcanonical := canonicalRoot_eq_oriented u secret canonical hroot slot
  have hcanonicalNe := canonicalRoot_coordinate_ne_zero
    u secret canonical hregular hroot slot
  by_cases horientation : rootOrientation u secret canonical slot <;>
    by_cases hsign : signs slot
  · simp only [normalizedSignedSecret, signedRoot, hsign, if_true,
      binaryFromSigns, horientation, Bool.true_xor, Bool.not_true]
    rw [if_pos horientation] at hcanonical
    apply normalizeCoordinate_eq_one _ _ _ htwo
    · simpa using congrArg Neg.neg hcanonical
    · exact neg_ne_zero.mpr hcanonicalNe
  · simp only [normalizedSignedSecret, signedRoot, hsign,
      binaryFromSigns, horientation, Bool.true_xor, Bool.not_false, if_true]
    rw [if_pos horientation] at hcanonical
    apply normalizeCoordinate_eq_zero _ _ _ htwo hcanonical hcanonicalNe
  · simp only [normalizedSignedSecret, signedRoot, hsign, if_true,
      binaryFromSigns, horientation, Bool.false_xor, if_true]
    rw [if_neg horientation] at hcanonical
    apply normalizeCoordinate_eq_zero _ _ _ htwo
    · simpa using congrArg Neg.neg hcanonical
    · exact neg_ne_zero.mpr hcanonicalNe
  · simp only [normalizedSignedSecret, signedRoot, hsign,
      binaryFromSigns, horientation, Bool.false_xor]
    rw [if_neg horientation] at hcanonical
    apply normalizeCoordinate_eq_one _ _ _ htwo hcanonical hcanonicalNe

/-- The executable signed-root sampler produces exactly the uniform Binary-NTT secret law. -/
theorem normalizedSignedSecret_uniform_evalDist
    {Slot K : Type} [Fintype Slot] [DecidableEq Slot]
    [Field K] [Finite K] [DecidableEq K] [SampleableType K]
    (u secret canonical : Slot → K)
    (htwo : (2 : K) ≠ 0)
    (hregular : IsUnit (u - 2 * secret))
    (hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2) :
    evalDist (($ᵗ (Slot → Bool)) >>= fun signs ↦
        pure (normalizedSignedSecret u secret canonical signs)) =
      evalDist (($ᵗ (Slot → Bool)) >>= fun signs ↦
        pure (binaryFromSigns (fun _ : Slot ↦ false) signs)) := by
  rw [show (fun signs ↦ pure (normalizedSignedSecret u secret canonical signs)) =
      (fun signs ↦ pure (binaryFromSigns (rootOrientation u secret canonical) signs)) by
    funext signs
    rw [normalizedSignedSecret_eq_binaryFromSigns u secret canonical signs
      htwo hregular hroot]]
  let finish := fun bits : Slot → Bool ↦
    (pure (binaryFromSigns (K := K) (fun _ : Slot ↦ false) bits) : ProbComp (Slot → K))
  calc
    _ = evalDist (($ᵗ (Slot → Bool)) >>= fun signs ↦
        pure (BinaryNTTSecurity.binaryVectorXor
          (rootOrientation u secret canonical) signs) >>= finish) := by
      apply evalDist_bind_congr' ($ᵗ (Slot → Bool))
      intro signs
      dsimp only [finish]
      simp only [pure_bind]
      apply congrArg evalDist
      apply congrArg (fun value : Slot → K ↦ (pure value : ProbComp (Slot → K)))
      funext slot
      cases horientation : rootOrientation u secret canonical slot <;>
        cases hsign : signs slot <;>
        simp [binaryFromSigns, BinaryNTTSecurity.binaryVectorXor,
          horientation, hsign]
    _ = evalDist (($ᵗ (Slot → Bool)) >>= finish) := by
      rw [← bind_assoc, evalDist_bind,
        BinaryNTTSecurity.binaryVectorXor_uniform_evalDist
          (rootOrientation u secret canonical), ← evalDist_bind]
    _ = _ := by rfl

/-- End-to-end executable sign-sampling theorem.  Starting from any deterministic certified
coordinate square-root routine, the public sampler in `regularSignedRootSampler` yields exactly
the Binary-NTT secret distribution after Figure 2 normalization. -/
theorem normalizedSignedRootSampler_uniform_evalDist
    {Slot K : Type} [Fintype Slot] [DecidableEq Slot]
    [Field K] [Finite K] [DecidableEq K] [SampleableType K]
    (squareRoot : CoordinateSquareRoot K) (u v secret : Slot → K)
    (htwo : (2 : K) ≠ 0)
    (hhint : v = BinaryNTTSecurity.quadraticHint u secret)
    (hregular : IsUnit (u - 2 * secret)) :
    evalDist (normalizedSignedRootSampler squareRoot u v secret) =
      evalDist (($ᵗ (Slot → Bool)) >>= fun signs ↦
        pure (binaryFromSigns (fun _ : Slot ↦ false) signs)) := by
  let canonical := canonicalRoots squareRoot (discriminantCoordinates u v)
  have hroot : ∀ slot, canonical slot ^ 2 = (2 * secret slot - u slot) ^ 2 :=
    fun slot ↦ canonicalRoots_regular_square squareRoot u v secret hhint slot
  have hdirect := normalizedSignedSecret_uniform_evalDist
    u secret canonical htwo hregular hroot
  unfold normalizedSignedSecret at hdirect
  simpa only [normalizedSignedRootSampler, regularSignedRootSampler, signedRootSampler,
    discriminantCoordinates, canonical, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind] using hdirect

/-- Public affine batch map used by the reverse reduction for a fixed signed root. -/
def inverseBatchMap {R Row : Type} [CommRing R]
    (root : Rˣ) (beta : R) :
    BinaryNTTSecurity.RLWEView R Row → BinaryNTTSecurity.RLWEView R Row :=
  fun view ↦
    ⟨fun i ↦ view.mask i * (root : R),
     fun i ↦ view.body i + view.mask i * beta⟩

/-- Explicit inverse of `inverseBatchMap`. -/
def inverseBatchMapInv {R Row : Type} [CommRing R]
    (root : Rˣ) (beta : R) :
    BinaryNTTSecurity.RLWEView R Row → BinaryNTTSecurity.RLWEView R Row :=
  fun view ↦
    let sourceMask := fun i ↦ view.mask i * (root⁻¹ : Rˣ)
    ⟨sourceMask, fun i ↦ view.body i - sourceMask i * beta⟩

theorem inverseBatchMap_bijective {R Row : Type} [CommRing R]
    (root : Rˣ) (beta : R) :
    Function.Bijective (inverseBatchMap (Row := Row) root beta) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨inverseBatchMapInv root beta, ?_, ?_⟩
  · intro view
    apply BinaryNTTSecurity.RLWEView.ext <;> funext i
    · simp [inverseBatchMapInv, inverseBatchMap, mul_assoc]
    · simp [inverseBatchMapInv, inverseBatchMap, mul_assoc]
  · intro view
    apply BinaryNTTSecurity.RLWEView.ext <;> funext i
    · simp [inverseBatchMapInv, inverseBatchMap, mul_assoc]
    · simp [inverseBatchMapInv, inverseBatchMap, mul_assoc]

/-- A uniform QH batch remains exactly uniform after the signed-root normalization map. -/
theorem inverseBatchMap_uniform_evalDist {R Row : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    [Finite Row] [DecidableEq Row]
    [SampleableType (BinaryNTTSecurity.RLWEView R Row)]
    (root : Rˣ) (beta : R) :
    evalDist (($ᵗ (BinaryNTTSecurity.RLWEView R Row)) >>= fun view ↦
        pure (inverseBatchMap root beta view)) =
      evalDist ($ᵗ (BinaryNTTSecurity.RLWEView R Row)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := BinaryNTTSecurity.RLWEView R Row)
      (β := BinaryNTTSecurity.RLWEView R Row)
      (inverseBatchMap root beta) (inverseBatchMap_bijective root beta)
      (fun value ↦ pure value) output)

/-! ## Exact Binary-NTT-to-regular-QH coin transport -/

/-- The involutory unit corresponding to an idempotent Binary-NTT secret. -/
def idempotentSignUnit {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) : Rˣ :=
  Units.mkOfMulEqOne (1 - 2 * secret) (1 - 2 * secret)
    (BinaryNTTSecurity.one_sub_two_mul_sq secret hidempotent)

@[simp]
theorem idempotentSignUnit_val {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) :
    (idempotentSignUnit secret hidempotent : R) = 1 - 2 * secret := by
  rfl

@[simp]
theorem idempotentSignUnit_sq {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) :
    idempotentSignUnit secret hidempotent * idempotentSignUnit secret hidempotent = 1 := by
  ext
  exact BinaryNTTSecurity.one_sub_two_mul_sq secret hidempotent

/-- Map the paper's unit multiplier and offset to the regular gap and transformed secret. -/
def forwardCoinsMap {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) : Rˣ × R → Rˣ × R :=
  fun coins ↦
    (coins.1 * idempotentSignUnit secret hidempotent,
      (coins.1 : R) * secret + coins.2)

/-- Explicit inverse of `forwardCoinsMap`. -/
def forwardCoinsMapInv {R : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) : Rˣ × R → Rˣ × R :=
  fun output ↦
    let multiplier := output.1 * idempotentSignUnit secret hidempotent
    (multiplier, output.2 - (multiplier : R) * secret)

@[simp]
theorem forwardCoinsMapInv_forwardCoinsMap {R : Type} [CommRing R]
    (secret : R) (hidempotent : secret ^ 2 = secret) (coins : Rˣ × R) :
    forwardCoinsMapInv secret hidempotent (forwardCoinsMap secret hidempotent coins) = coins := by
  rcases coins with ⟨multiplier, offset⟩
  apply Prod.ext
  · simp [forwardCoinsMapInv, forwardCoinsMap, mul_assoc]
  · have hsign := BinaryNTTSecurity.one_sub_two_mul_sq secret hidempotent
    simp only [forwardCoinsMapInv, forwardCoinsMap, idempotentSignUnit_val,
      Units.val_mul]
    linear_combination -((multiplier : R) * secret) * hsign

@[simp]
theorem forwardCoinsMap_forwardCoinsMapInv {R : Type} [CommRing R]
    (secret : R) (hidempotent : secret ^ 2 = secret) (output : Rˣ × R) :
    forwardCoinsMap secret hidempotent (forwardCoinsMapInv secret hidempotent output) = output := by
  rcases output with ⟨gap, shiftedSecret⟩
  apply Prod.ext
  · simp [forwardCoinsMapInv, forwardCoinsMap, mul_assoc]
  · simp [forwardCoinsMapInv, forwardCoinsMap]

theorem forwardCoinsMap_bijective {R : Type} [CommRing R]
    (secret : R) (hidempotent : secret ^ 2 = secret) :
    Function.Bijective (forwardCoinsMap secret hidempotent) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨forwardCoinsMapInv secret hidempotent,
      forwardCoinsMapInv_forwardCoinsMap secret hidempotent,
      forwardCoinsMap_forwardCoinsMapInv secret hidempotent⟩

/-- For every fixed Binary-NTT secret, the transformed regular gap and transformed secret are
independent uniforms over `Rˣ × R`. -/
theorem forwardCoinsMap_uniform_evalDist {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    [Finite Rˣ] [DecidableEq Rˣ] [SampleableType Rˣ]
    (secret : R) (hidempotent : secret ^ 2 = secret) :
    evalDist (($ᵗ (Rˣ × R)) >>= fun coins ↦
        pure (forwardCoinsMap secret hidempotent coins)) =
      evalDist ($ᵗ (Rˣ × R)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := Rˣ × R) (β := Rˣ × R)
      (forwardCoinsMap secret hidempotent)
      (forwardCoinsMap_bijective secret hidempotent)
      (fun value ↦ pure value) output)

/-- The gap generated by Figure 1 is exactly the regular gap in `forwardCoinsMap`. -/
theorem forward_gap_eq {R : Type} [CommRing R]
    (multiplier : Rˣ) (offset secret : R) (hidempotent : secret ^ 2 = secret) :
    BinaryNTTSecurity.forwardHintU (multiplier : R) offset -
        2 * BinaryNTTSecurity.forwardSecret (multiplier : R) offset secret =
      ((forwardCoinsMap secret hidempotent (multiplier, offset)).1 : R) := by
  rw [BinaryNTTSecurity.forward_hint_secret_gap]
  rfl

/-- The transformed secret is exactly the second regular coin. -/
theorem forward_secret_eq {R : Type} [CommRing R]
    (multiplier : Rˣ) (offset secret : R) (hidempotent : secret ^ 2 = secret) :
    BinaryNTTSecurity.forwardSecret (multiplier : R) offset secret =
      (forwardCoinsMap secret hidempotent (multiplier, offset)).2 := by
  rfl

/-! ### Complete public-uniform transports for repaired Theorem 5 -/

/-- Real-branch public coins: regular `(gap,secret')` together with the divided mask batch. -/
def forwardRealPublicMap {R Row : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) :
    (Rˣ × R) × (Row → R) → (Rˣ × R) × (Row → R) :=
  fun input ↦
    (forwardCoinsMap secret hidempotent input.1,
      fun i ↦ input.2 i * (input.1.1⁻¹ : Rˣ))

/-- Inverse of `forwardRealPublicMap`. -/
def forwardRealPublicMapInv {R Row : Type} [CommRing R] (secret : R)
    (hidempotent : secret ^ 2 = secret) :
    (Rˣ × R) × (Row → R) → (Rˣ × R) × (Row → R) :=
  fun output ↦
    let sourceCoins := forwardCoinsMapInv secret hidempotent output.1
    (sourceCoins, fun i ↦ output.2 i * (sourceCoins.1 : R))

theorem forwardRealPublicMap_bijective {R Row : Type} [CommRing R]
    (secret : R) (hidempotent : secret ^ 2 = secret) :
    Function.Bijective (forwardRealPublicMap (Row := Row) secret hidempotent) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨forwardRealPublicMapInv secret hidempotent, ?_, ?_⟩
  · rintro ⟨⟨multiplier, offset⟩, mask⟩
    apply Prod.ext
    · exact forwardCoinsMapInv_forwardCoinsMap secret hidempotent (multiplier, offset)
    · funext i
      simp [forwardRealPublicMapInv, forwardRealPublicMap, mul_assoc]
  · rintro ⟨⟨gap, shiftedSecret⟩, mask⟩
    apply Prod.ext
    · exact forwardCoinsMap_forwardCoinsMapInv secret hidempotent (gap, shiftedSecret)
    · funext i
      simp [forwardRealPublicMapInv, forwardRealPublicMap, mul_assoc]

theorem forwardRealPublicMap_uniform_evalDist {R Row : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    [Finite Rˣ] [DecidableEq Rˣ] [SampleableType Rˣ]
    [Finite Row] [DecidableEq Row] [FinEnum Row]
    (secret : R) (hidempotent : secret ^ 2 = secret) :
    evalDist (($ᵗ ((Rˣ × R) × (Row → R))) >>= fun coins ↦
        pure (forwardRealPublicMap secret hidempotent coins)) =
      evalDist ($ᵗ ((Rˣ × R) × (Row → R))) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := (Rˣ × R) × (Row → R)) (β := (Rˣ × R) × (Row → R))
      (forwardRealPublicMap secret hidempotent)
      (forwardRealPublicMap_bijective secret hidempotent)
      (fun value ↦ pure value) output)

/-- Complete random-branch map.  Here the regular hint witness is the sampled offset itself. -/
def forwardRandomPublicMap {R Row : Type} [CommRing R] :
    (Rˣ × R) × BinaryNTTSecurity.RLWEView R Row →
      (Rˣ × R) × BinaryNTTSecurity.RLWEView R Row :=
  fun input ↦
    let multiplier := input.1.1
    let offset := input.1.2
    let dividedMask := fun i ↦ input.2.mask i * (multiplier⁻¹ : Rˣ)
    ((multiplier, offset),
      ⟨dividedMask, fun i ↦ input.2.body i + dividedMask i * offset⟩)

/-- Inverse of `forwardRandomPublicMap`. -/
def forwardRandomPublicMapInv {R Row : Type} [CommRing R] :
    (Rˣ × R) × BinaryNTTSecurity.RLWEView R Row →
      (Rˣ × R) × BinaryNTTSecurity.RLWEView R Row :=
  fun output ↦
    let multiplier := output.1.1
    let offset := output.1.2
    ((multiplier, offset),
      ⟨fun i ↦ output.2.mask i * (multiplier : R),
       fun i ↦ output.2.body i - output.2.mask i * offset⟩)

theorem forwardRandomPublicMap_bijective {R Row : Type} [CommRing R] :
    Function.Bijective (forwardRandomPublicMap (R := R) (Row := Row)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨forwardRandomPublicMapInv, ?_, ?_⟩
  · rintro ⟨⟨multiplier, offset⟩, view⟩
    apply Prod.ext
    · rfl
    · apply BinaryNTTSecurity.RLWEView.ext <;> funext i
      · simp [forwardRandomPublicMapInv, forwardRandomPublicMap, mul_assoc]
      · simp [forwardRandomPublicMapInv, forwardRandomPublicMap, mul_assoc]
  · rintro ⟨⟨gap, witness⟩, view⟩
    apply Prod.ext
    · rfl
    · apply BinaryNTTSecurity.RLWEView.ext <;> funext i
      · simp [forwardRandomPublicMapInv, forwardRandomPublicMap, mul_assoc]
      · simp [forwardRandomPublicMapInv, forwardRandomPublicMap, mul_assoc]

/-- Figure 1 maps a fully uniform Binary-NTT random branch exactly to a uniform regular hint
witness and uniform RLWE batch. -/
theorem forwardRandomPublicMap_uniform_evalDist {R Row : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    [Finite Rˣ] [DecidableEq Rˣ] [SampleableType Rˣ]
    [Finite Row] [DecidableEq Row]
    [SampleableType (BinaryNTTSecurity.RLWEView R Row)] :
    evalDist (($ᵗ ((Rˣ × R) × BinaryNTTSecurity.RLWEView R Row)) >>= fun coins ↦
        pure (forwardRandomPublicMap coins)) =
      evalDist ($ᵗ ((Rˣ × R) × BinaryNTTSecurity.RLWEView R Row)) := by
  apply evalDist_ext
  intro output
  simpa [monad_norm] using
    (probOutput_bind_bijective_uniform_cross
      (α := (Rˣ × R) × BinaryNTTSecurity.RLWEView R Row)
      (β := (Rˣ × R) × BinaryNTTSecurity.RLWEView R Row)
      forwardRandomPublicMap (forwardRandomPublicMap_bijective (R := R) (Row := Row))
      (fun value ↦ pure value) output)

/-! ## Preservation by the remaining reductions -/

/-- Additive secret randomization preserves the regular gap literally. -/
theorem shift_preserves_gap {R Row : Type} [CommRing R]
    (shift : R) (view : BinaryNTTSecurity.QuadraticHintView R Row) (secret : R) :
    (BinaryNTTSecurity.shiftQuadraticHintView shift view).u - 2 * (secret + shift) =
      view.u - 2 * secret := by
  simp [BinaryNTTSecurity.shiftQuadraticHintView]
  ring

theorem shift_preserves_regular {R Row : Type} [CommRing R]
    (shift : R) (view : BinaryNTTSecurity.QuadraticHintView R Row) (secret : R)
    (hregular : IsUnit (view.u - 2 * secret)) :
    IsUnit ((BinaryNTTSecurity.shiftQuadraticHintView shift view).u -
      2 * (secret + shift)) := by
  rw [shift_preserves_gap]
  exact hregular

/-- In the error-to-small-secret reduction, the new gap is the old gap multiplied by the negative
anchor mask. -/
theorem smallSecretTransform_gap {R : Type} [CommRing R]
    (anchorMask : Rˣ) (oldU oldSecret anchorError : R) :
    let anchorBody := (anchorMask : R) * oldSecret + anchorError
    (BinaryNTTSecurity.smallSecretTransform (Row := Fin 0) anchorMask anchorBody oldU
        (BinaryNTTSecurity.quadraticHint oldU oldSecret) Fin.elim0 Fin.elim0).u -
      2 * anchorError =
        -(anchorMask : R) * (oldU - 2 * oldSecret) := by
  dsimp [BinaryNTTSecurity.smallSecretTransform]
  ring

theorem smallSecretTransform_preserves_regular {R : Type} [CommRing R]
    (anchorMask : Rˣ) (oldU oldSecret anchorError : R)
    (hregular : IsUnit (oldU - 2 * oldSecret)) :
    let anchorBody := (anchorMask : R) * oldSecret + anchorError
    IsUnit
      ((BinaryNTTSecurity.smallSecretTransform (Row := Fin 0) anchorMask anchorBody oldU
          (BinaryNTTSecurity.quadraticHint oldU oldSecret) Fin.elim0 Fin.elim0).u -
        2 * anchorError) := by
  dsimp only
  rw [smallSecretTransform_gap]
  exact (anchorMask.isUnit.neg.mul hregular)

/-! ## Repaired security implications -/

/-- A zero-error probabilistic reduction. -/
structure ExactProbReduction {SourceView TargetView : Type}
    (source : BinaryNTTSecurity.DecisionProblem SourceView)
    (target : BinaryNTTSecurity.DecisionProblem TargetView) where
  transform : SourceView → ProbComp TargetView
  realLaw : evalDist (source.real >>= transform) = evalDist target.real
  randomLaw : evalDist (source.random >>= transform) = evalDist target.random

def ExactProbReduction.toApproximate {SourceView TargetView : Type}
    {source : BinaryNTTSecurity.DecisionProblem SourceView}
    {target : BinaryNTTSecurity.DecisionProblem TargetView}
    (reduction : ExactProbReduction source target) :
    BinaryNTTSecurity.ApproximateReduction source target where
  transform := reduction.transform
  realError := 0
  randomError := 0
  realError_nonneg := le_rfl
  randomError_nonneg := le_rfl
  realLaw := by
    unfold tvDist
    rw [reduction.realLaw]
    simp
  randomLaw := by
    unfold tvDist
    rw [reduction.randomLaw]
    simp

theorem ExactProbReduction.advantage_le {SourceView TargetView : Type}
    {source : BinaryNTTSecurity.DecisionProblem SourceView}
    {target : BinaryNTTSecurity.DecisionProblem TargetView}
    (reduction : ExactProbReduction source target)
    (distinguisher : BinaryNTTSecurity.Distinguisher TargetView) :
    BinaryNTTSecurity.advantage target distinguisher ≤
      BinaryNTTSecurity.advantage source
        (reduction.toApproximate.pullback distinguisher) := by
  have h := reduction.toApproximate.advantage_le distinguisher
  simpa [ExactProbReduction.toApproximate] using h

/-- Exact repaired Theorem 5: Binary-NTT hardness implies regular-QH hardness with no `N/q`
term once the concrete coin transport is assembled into the endpoint laws. -/
theorem theorem5_regular_hardAgainst {SourceView TargetView : Type}
    {binaryNTT : BinaryNTTSecurity.DecisionProblem SourceView}
    {regularQH : BinaryNTTSecurity.DecisionProblem TargetView}
    (reduction : ExactProbReduction binaryNTT regularQH)
    (sourceAllowed : BinaryNTTSecurity.Distinguisher SourceView → Prop)
    (targetAllowed : BinaryNTTSecurity.Distinguisher TargetView → Prop)
    (bound : ℝ)
    (hClosed : ∀ distinguisher, targetAllowed distinguisher →
      sourceAllowed (reduction.toApproximate.pullback distinguisher))
    (hSource : BinaryNTTSecurity.HardAgainst binaryNTT sourceAllowed bound) :
    BinaryNTTSecurity.HardAgainst regularQH targetAllowed bound := by
  intro distinguisher hAllowed
  exact (reduction.advantage_le distinguisher).trans
    (hSource _ (hClosed distinguisher hAllowed))

/-- Exact reverse implication after supplying uniform square-root-sign sampling.  Regularity
removes the paper's invertibility abort, so there is no factor-four loss. -/
theorem theorem10_regular_hardAgainst {SourceView TargetView : Type}
    {regularQH : BinaryNTTSecurity.DecisionProblem SourceView}
    {binaryNTT : BinaryNTTSecurity.DecisionProblem TargetView}
    (reduction : ExactProbReduction regularQH binaryNTT)
    (sourceAllowed : BinaryNTTSecurity.Distinguisher SourceView → Prop)
    (targetAllowed : BinaryNTTSecurity.Distinguisher TargetView → Prop)
    (bound : ℝ)
    (hClosed : ∀ distinguisher, targetAllowed distinguisher →
      sourceAllowed (reduction.toApproximate.pullback distinguisher))
    (hSource : BinaryNTTSecurity.HardAgainst regularQH sourceAllowed bound) :
    BinaryNTTSecurity.HardAgainst binaryNTT targetAllowed bound := by
  intro distinguisher hAllowed
  exact (reduction.advantage_le distinguisher).trans
    (hSource _ (hClosed distinguisher hAllowed))

/-- Same-sample additive randomization remains exact for regular hints. -/
theorem theorem19_regular_sameSample_hardAgainst {SmallView UniformView : Type}
    {regularSmall : BinaryNTTSecurity.DecisionProblem SmallView}
    {regularUniform : BinaryNTTSecurity.DecisionProblem UniformView}
    (reduction : ExactProbReduction regularSmall regularUniform)
    (smallAllowed : BinaryNTTSecurity.Distinguisher SmallView → Prop)
    (uniformAllowed : BinaryNTTSecurity.Distinguisher UniformView → Prop)
    (bound : ℝ)
    (hClosed : ∀ distinguisher, uniformAllowed distinguisher →
      smallAllowed (reduction.toApproximate.pullback distinguisher))
    (hSmall : BinaryNTTSecurity.HardAgainst regularSmall smallAllowed bound) :
    BinaryNTTSecurity.HardAgainst regularUniform uniformAllowed bound := by
  intro distinguisher hAllowed
  exact (reduction.advantage_le distinguisher).trans
    (hSmall _ (hClosed distinguisher hAllowed))

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.Regular
