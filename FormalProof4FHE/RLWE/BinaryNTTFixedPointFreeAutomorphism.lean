/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BinaryNTTAutomorphismTransposition
import FormalProof4FHE.Probability.FiniteProduct

/-!
# Binary-NTT automorphism KDM for the tower involution

This module formalizes the simultaneous orbit-completion reduction for the index-two tower

`R'[Y] ⊂ R[X]`, `Y = X²`,

and the involution `σ(f(X)) = f(-X)`.  Unlike a coordinate-insertion proof, the reduction
completes every two-element NTT orbit at once.  Its finite algebra therefore has constant loss.

The concrete polynomial quotient supplies an even/odd coefficient equivalence.  The tower
assembly lemmas below are stated for an arbitrary bijective assembly map so that they do not
depend on a particular quotient-ring implementation.
-/

open OracleComp

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.FixedPointFreeAutomorphism

noncomputable section

abbrev PairedSlot (Slot : Type) := Slot × Bool

/-- The fixed-point-free involution on paired NTT coordinates. -/
def orbitInvolution {Slot : Type} : PairedSlot Slot → PairedSlot Slot
  | (slot, side) => (slot, !side)

@[simp]
theorem orbitInvolution_involution {Slot : Type} (coordinate : PairedSlot Slot) :
    orbitInvolution (orbitInvolution coordinate) = coordinate := by
  rcases coordinate with ⟨slot, side⟩
  cases side <;> rfl

/-- Complete one fixed-subring bit and one orbit coin into two independent bits. -/
def completionBits {Slot : Type} (fixed orbitCoin : Slot → Bool) :
    PairedSlot Slot → Bool
  | (slot, false) => fixed slot
  | (slot, true) => xor (fixed slot) (orbitCoin slot)

/-- Recover the fixed-subring bits and orbit coins from a completed vector. -/
def recoverCompletion {Slot : Type} (completed : PairedSlot Slot → Bool) :
    (Slot → Bool) × (Slot → Bool) :=
  (fun slot => completed (slot, false),
    fun slot => xor (completed (slot, false)) (completed (slot, true)))

@[simp]
theorem recoverCompletion_completionBits {Slot : Type}
    (fixed orbitCoin : Slot → Bool) :
    recoverCompletion (completionBits fixed orbitCoin) = (fixed, orbitCoin) := by
  apply Prod.ext <;> funext slot
  · rfl
  · simp [recoverCompletion, completionBits]

@[simp]
theorem completionBits_recoverCompletion {Slot : Type}
    (completed : PairedSlot Slot → Bool) :
    completionBits (recoverCompletion completed).1 (recoverCompletion completed).2 = completed := by
  funext coordinate
  rcases coordinate with ⟨slot, side⟩
  cases side
  · rfl
  · simp [recoverCompletion, completionBits]

/-- Orbit completion is an exact equivalence, not a leftover-hash argument. -/
def completionEquiv (Slot : Type) :
    ((Slot → Bool) × (Slot → Bool)) ≃ (PairedSlot Slot → Bool) where
  toFun pair := completionBits pair.1 pair.2
  invFun := recoverCompletion
  left_inv pair := by rcases pair with ⟨fixed, coin⟩; simp
  right_inv := completionBits_recoverCompletion

/-- Simultaneous completion of all orbits produces the exact uniform full Binary-NTT law. -/
theorem completionBits_uniform_evalDist {Slot : Type}
    [Fintype Slot] [DecidableEq Slot]
    [SampleableType (Slot → Bool)]
    [SampleableType ((Slot → Bool) × (Slot → Bool))]
    [SampleableType (PairedSlot Slot → Bool)] :
    evalDist ((completionEquiv Slot) <$>
      ($ᵗ ((Slot → Bool) × (Slot → Bool)))) =
      evalDist ($ᵗ (PairedSlot Slot → Bool)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := (Slot → Bool) × (Slot → Bool)) (β := PairedSlot Slot → Bool)
    (completionEquiv Slot) (completionEquiv Slot).bijective

/-! ## Coordinate realization of `S = H*T + C` -/

def fixedSecret {Slot K : Type} [Zero K] [One K]
    (fixed : Slot → Bool) : PairedSlot Slot → K :=
  fun coordinate =>
    AutomorphismTransposition.bitValue (K := K) (fixed coordinate.1)

def orbitMultiplier {Slot K : Type} [One K] [Neg K]
    (orbitCoin : Slot → Bool) : PairedSlot Slot → K
  | (_, false) => 1
  | (slot, true) => if orbitCoin slot then -1 else 1

def orbitOffset {Slot K : Type} [Zero K] [One K]
    (orbitCoin : Slot → Bool) : PairedSlot Slot → K
  | (_, false) => 0
  | (slot, true) => AutomorphismTransposition.bitValue (K := K) (orbitCoin slot)

theorem completedSecret_affine {Slot K : Type} [CommRing K]
    (fixed orbitCoin : Slot → Bool) :
    orbitMultiplier (K := K) orbitCoin * fixedSecret fixed + orbitOffset orbitCoin =
      AutomorphismTransposition.embedBits (K := K)
        (completionBits fixed orbitCoin) := by
  funext coordinate
  rcases coordinate with ⟨slot, side⟩
  cases hfixed : fixed slot <;> cases hcoin : orbitCoin slot <;>
    cases side <;> simp [orbitMultiplier, fixedSecret, orbitOffset, completionBits,
      AutomorphismTransposition.embedBits, AutomorphismTransposition.bitValue, hfixed, hcoin]

theorem orbitMultiplier_sq {Slot K : Type} [CommRing K]
    (orbitCoin : Slot → Bool) :
    orbitMultiplier (K := K) orbitCoin * orbitMultiplier orbitCoin = 1 := by
  funext coordinate
  rcases coordinate with ⟨slot, side⟩
  cases side <;> cases hcoin : orbitCoin slot <;>
    simp [orbitMultiplier, hcoin]

theorem orbitMultiplier_isUnit {Slot K : Type} [CommRing K]
    (orbitCoin : Slot → Bool) :
    IsUnit (orbitMultiplier (K := K) orbitCoin) := by
  refine ⟨⟨orbitMultiplier orbitCoin, orbitMultiplier orbitCoin, ?_, ?_⟩, rfl⟩
  · exact orbitMultiplier_sq orbitCoin
  · exact orbitMultiplier_sq orbitCoin

/-! ## Exact tower assembly -/

/-- Data needed to assemble two half-degree coefficient blocks into one full-ring block. -/
structure IndexTwoAssembly (Base Full : Type) [CommRing Base] [CommRing Full] where
  assemble : (Base × Base) ≃ Full
  embed : Base → Full
  mul_fixed : ∀ left right secret,
    assemble (left, right) * embed secret =
      assemble (left * secret, right * secret)

def assembleUniformSampler {Base Full : Type} [CommRing Base] [CommRing Full]
    [SampleableType (Base × Base)]
    (tower : IndexTwoAssembly Base Full) : ProbComp Full :=
  tower.assemble <$> ($ᵗ (Base × Base))

/-- Two independent uniform half-degree elements assemble to one exactly uniform full element. -/
theorem assemble_uniform_evalDist {Base Full : Type}
    [CommRing Base] [CommRing Full]
    [Fintype Base] [SampleableType Base]
    [Fintype Full] [SampleableType Full]
    [SampleableType (Base × Base)]
    (tower : IndexTwoAssembly Base Full) :
    evalDist (assembleUniformSampler tower) =
      evalDist ($ᵗ Full) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Base × Base) (β := Full) tower.assemble tower.assemble.bijective

/-- The coefficient assembly additionally preserves zero and addition. -/
structure AdditiveIndexTwoAssembly (Base Full : Type) [CommRing Base] [CommRing Full]
    extends IndexTwoAssembly Base Full where
  map_zero : assemble (0, 0) = 0
  map_add : ∀ left right : Base × Base,
    assemble (left + right) = assemble left + assemble right

theorem AdditiveIndexTwoAssembly.assemble_real_equation
    {Base Full : Type} [CommRing Base] [CommRing Full]
    (tower : AdditiveIndexTwoAssembly Base Full)
    (maskLeft maskRight errorLeft errorRight secret : Base) :
    tower.assemble
        (maskLeft * secret + errorLeft, maskRight * secret + errorRight) =
      tower.assemble (maskLeft, maskRight) * tower.embed secret +
        tower.assemble (errorLeft, errorRight) := by
  rw [show (maskLeft * secret + errorLeft, maskRight * secret + errorRight) =
      (maskLeft * secret, maskRight * secret) + (errorLeft, errorRight) by rfl]
  rw [tower.map_add, ← tower.mul_fixed]

/-! ## Full-ring automorphism encoder -/

def completedRingSecret {R : Type} [CommRing R]
    (multiplier : R) (fixedSecret offset : R) : R :=
  multiplier * fixedSecret + offset

def automorphismMask {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ) (sourceMask : R) : R :=
  (sourceMask - gadget * sigma multiplier) * ↑(multiplier⁻¹)

def automorphismBody {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset sourceBody targetMask : R) : R :=
  sourceBody + targetMask * offset + gadget * sigma offset

def zeroMask {R : Type} [CommRing R] (multiplier : Rˣ) (sourceMask : R) : R :=
  sourceMask * ↑(multiplier⁻¹)

def zeroBody {R : Type} [CommRing R]
    (offset sourceBody targetMask : R) : R :=
  sourceBody + targetMask * offset

theorem automorphismMask_reconstruct {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ) (sourceMask : R) :
    automorphismMask sigma gadget multiplier sourceMask * (multiplier : R) +
        gadget * sigma multiplier = sourceMask := by
  simp [automorphismMask]

/-- Exact real-branch identity for every gadget row. -/
theorem automorphismBody_real {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ)
    (offset fixedSecret error sourceMask : R)
    (hfixed : sigma fixedSecret = fixedSecret) :
    automorphismBody sigma gadget offset
        (sourceMask * fixedSecret + error)
        (automorphismMask sigma gadget multiplier sourceMask) =
      automorphismMask sigma gadget multiplier sourceMask *
          completedRingSecret (multiplier : R) fixedSecret offset +
        error + gadget * sigma (completedRingSecret (multiplier : R) fixedSecret offset) := by
  let targetMask := automorphismMask sigma gadget multiplier sourceMask
  have hsource : targetMask * (multiplier : R) + gadget * sigma multiplier = sourceMask :=
    automorphismMask_reconstruct sigma gadget multiplier sourceMask
  change sourceMask * fixedSecret + error + targetMask * offset + gadget * sigma offset =
    targetMask * ((multiplier : R) * fixedSecret + offset) + error +
      gadget * sigma ((multiplier : R) * fixedSecret + offset)
  rw [← hsource]
  simp only [map_add, map_mul, hfixed]
  ring

theorem zeroMask_reconstruct {R : Type} [CommRing R]
    (multiplier : Rˣ) (sourceMask : R) :
    zeroMask multiplier sourceMask * (multiplier : R) = sourceMask := by
  simp [zeroMask]

/-- Exact real-branch identity for the zero-message comparison block. -/
theorem zeroBody_real {R : Type} [CommRing R]
    (multiplier : Rˣ) (offset fixedSecret error sourceMask : R) :
    zeroBody offset (sourceMask * fixedSecret + error) (zeroMask multiplier sourceMask) =
      zeroMask multiplier sourceMask *
          completedRingSecret (multiplier : R) fixedSecret offset + error := by
  let targetMask := zeroMask multiplier sourceMask
  have hsource : targetMask * (multiplier : R) = sourceMask :=
    zeroMask_reconstruct multiplier sourceMask
  change sourceMask * fixedSecret + error + targetMask * offset =
    targetMask * ((multiplier : R) * fixedSecret + offset) + error
  rw [← hsource]
  ring

/-- Source-mask recovery for the automorphism encoder. -/
def automorphismMaskInv {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ) (targetMask : R) : R :=
  targetMask * multiplier + gadget * sigma multiplier

@[simp]
theorem automorphismMaskInv_automorphismMask {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ) (sourceMask : R) :
    automorphismMaskInv sigma gadget multiplier
      (automorphismMask sigma gadget multiplier sourceMask) = sourceMask := by
  exact automorphismMask_reconstruct sigma gadget multiplier sourceMask

@[simp]
theorem automorphismMask_automorphismMaskInv {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ) (targetMask : R) :
    automorphismMask sigma gadget multiplier
      (automorphismMaskInv sigma gadget multiplier targetMask) = targetMask := by
  simp [automorphismMask, automorphismMaskInv]

theorem automorphismMask_bijective {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget : R) (multiplier : Rˣ) :
    Function.Bijective (automorphismMask sigma gadget multiplier) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨automorphismMaskInv sigma gadget multiplier,
      automorphismMaskInv_automorphismMask sigma gadget multiplier,
      automorphismMask_automorphismMaskInv sigma gadget multiplier⟩

/-- Complete public row transform for the automorphism-message encoder. -/
def automorphismRow {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : R) (multiplier : Rˣ)
    (source : R × R) : R × R :=
  let targetMask := automorphismMask sigma gadget multiplier source.1
  (targetMask, automorphismBody sigma gadget offset source.2 targetMask)

def automorphismRowInv {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : R) (multiplier : Rˣ)
    (target : R × R) : R × R :=
  (automorphismMaskInv sigma gadget multiplier target.1,
    target.2 - target.1 * offset - gadget * sigma offset)

@[simp]
theorem automorphismRowInv_automorphismRow {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : R) (multiplier : Rˣ)
    (source : R × R) :
    automorphismRowInv sigma gadget offset multiplier
      (automorphismRow sigma gadget offset multiplier source) = source := by
  rcases source with ⟨mask, body⟩
  simp [automorphismRow, automorphismRowInv, automorphismBody]
  ring

@[simp]
theorem automorphismRow_automorphismRowInv {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : R) (multiplier : Rˣ)
    (target : R × R) :
    automorphismRow sigma gadget offset multiplier
      (automorphismRowInv sigma gadget offset multiplier target) = target := by
  rcases target with ⟨mask, body⟩
  simp [automorphismRow, automorphismRowInv, automorphismBody]
  ring

theorem automorphismRow_bijective {R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : R) (multiplier : Rˣ) :
    Function.Bijective (automorphismRow sigma gadget offset multiplier) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨automorphismRowInv sigma gadget offset multiplier,
      automorphismRowInv_automorphismRow sigma gadget offset multiplier,
      automorphismRow_automorphismRowInv sigma gadget offset multiplier⟩

/-- Conditioned on the orbit coins, a uniform source row maps to an exact uniform target row. -/
theorem automorphismRow_uniform_evalDist {R : Type} [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (R × R)]
    (sigma : R ≃+* R) (gadget offset : R) (multiplier : Rˣ) :
    evalDist (automorphismRow sigma gadget offset multiplier <$> ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R)
    (automorphismRow sigma gadget offset multiplier)
    (automorphismRow_bijective sigma gadget offset multiplier)

/-- Complete public row transform for the zero-message encoder. -/
def zeroRow {R : Type} [CommRing R]
    (offset : R) (multiplier : Rˣ) (source : R × R) : R × R :=
  let targetMask := zeroMask multiplier source.1
  (targetMask, zeroBody offset source.2 targetMask)

def zeroRowInv {R : Type} [CommRing R]
    (offset : R) (multiplier : Rˣ) (target : R × R) : R × R :=
  (target.1 * multiplier, target.2 - target.1 * offset)

@[simp]
theorem zeroRowInv_zeroRow {R : Type} [CommRing R]
    (offset : R) (multiplier : Rˣ) (source : R × R) :
    zeroRowInv offset multiplier (zeroRow offset multiplier source) = source := by
  rcases source with ⟨mask, body⟩
  simp [zeroRow, zeroRowInv, zeroBody, zeroMask]

@[simp]
theorem zeroRow_zeroRowInv {R : Type} [CommRing R]
    (offset : R) (multiplier : Rˣ) (target : R × R) :
    zeroRow offset multiplier (zeroRowInv offset multiplier target) = target := by
  rcases target with ⟨mask, body⟩
  simp [zeroRow, zeroRowInv, zeroBody, zeroMask]

theorem zeroRow_bijective {R : Type} [CommRing R]
    (offset : R) (multiplier : Rˣ) :
    Function.Bijective (zeroRow offset multiplier) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨zeroRowInv offset multiplier, zeroRowInv_zeroRow offset multiplier,
      zeroRow_zeroRowInv offset multiplier⟩

theorem zeroRow_uniform_evalDist {R : Type} [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (R × R)]
    (offset : R) (multiplier : Rˣ) :
    evalDist (zeroRow offset multiplier <$> ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R) (zeroRow offset multiplier)
    (zeroRow_bijective offset multiplier)

/-- Apply the automorphism encoder simultaneously to the complete gadget-row family. -/
def automorphismBatch {Row R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : Row → R) (multiplier : Rˣ)
    (source : Row → R × R) : Row → R × R :=
  fun row => automorphismRow sigma (gadget row) (offset row) multiplier (source row)

def automorphismBatchInv {Row R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : Row → R) (multiplier : Rˣ)
    (target : Row → R × R) : Row → R × R :=
  fun row => automorphismRowInv sigma (gadget row) (offset row) multiplier (target row)

@[simp]
theorem automorphismBatchInv_automorphismBatch {Row R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : Row → R) (multiplier : Rˣ)
    (source : Row → R × R) :
    automorphismBatchInv sigma gadget offset multiplier
      (automorphismBatch sigma gadget offset multiplier source) = source := by
  funext row
  simp [automorphismBatch, automorphismBatchInv]

@[simp]
theorem automorphismBatch_automorphismBatchInv {Row R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : Row → R) (multiplier : Rˣ)
    (target : Row → R × R) :
    automorphismBatch sigma gadget offset multiplier
      (automorphismBatchInv sigma gadget offset multiplier target) = target := by
  funext row
  simp [automorphismBatch, automorphismBatchInv]

theorem automorphismBatch_bijective {Row R : Type} [CommRing R]
    (sigma : R ≃+* R) (gadget offset : Row → R) (multiplier : Rˣ) :
    Function.Bijective (automorphismBatch sigma gadget offset multiplier) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨automorphismBatchInv sigma gadget offset multiplier,
      automorphismBatchInv_automorphismBatch sigma gadget offset multiplier,
      automorphismBatch_automorphismBatchInv sigma gadget offset multiplier⟩

/-- The entire random gadget-row transcript, not merely each marginal row, remains uniform. -/
theorem automorphismBatch_uniform_evalDist {Row R : Type} [CommRing R]
    [Finite Row] [DecidableEq Row]
    [Fintype R] [SampleableType R]
    [SampleableType (Row → R × R)]
    (sigma : R ≃+* R) (gadget offset : Row → R) (multiplier : Rˣ) :
    evalDist (automorphismBatch sigma gadget offset multiplier <$>
        ($ᵗ (Row → R × R))) =
      evalDist ($ᵗ (Row → R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Row → R × R) (β := Row → R × R)
    (automorphismBatch sigma gadget offset multiplier)
    (automorphismBatch_bijective sigma gadget offset multiplier)

def zeroBatch {Row R : Type} [CommRing R]
    (offset : Row → R) (multiplier : Rˣ)
    (source : Row → R × R) : Row → R × R :=
  fun row => zeroRow (offset row) multiplier (source row)

def zeroBatchInv {Row R : Type} [CommRing R]
    (offset : Row → R) (multiplier : Rˣ)
    (target : Row → R × R) : Row → R × R :=
  fun row => zeroRowInv (offset row) multiplier (target row)

theorem zeroBatch_bijective {Row R : Type} [CommRing R]
    (offset : Row → R) (multiplier : Rˣ) :
    Function.Bijective (zeroBatch offset multiplier) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨zeroBatchInv offset multiplier, ?_, ?_⟩
  · intro source
    funext row
    simp [zeroBatch, zeroBatchInv]
  · intro target
    funext row
    simp [zeroBatch, zeroBatchInv]

theorem zeroBatch_uniform_evalDist {Row R : Type} [CommRing R]
    [Finite Row] [DecidableEq Row]
    [Fintype R] [SampleableType R]
    [SampleableType (Row → R × R)]
    (offset : Row → R) (multiplier : Rˣ) :
    evalDist (zeroBatch offset multiplier <$> ($ᵗ (Row → R × R))) =
      evalDist ($ᵗ (Row → R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Row → R × R) (β := Row → R × R)
    (zeroBatch offset multiplier) (zeroBatch_bijective offset multiplier)

/-! ## Constant-loss comparison -/

/-- Randomized comparison of two Boolean outputs.  Its true probability is
`(1 + x - y)/2` at the sample level. -/
def compareOutputs (left right : Bool) : ProbComp Bool :=
  match left, right with
  | true, false => pure true
  | false, true => pure false
  | _, _ => $ᵗ Bool

theorem probOutput_compareOutputs_true (left right : Bool) :
    Pr[= true | compareOutputs left right].toReal =
      (1 + FormalProof4FHE.SquaredBias.bitReal left -
        FormalProof4FHE.SquaredBias.bitReal right) / 2 := by
  cases left <;> cases right <;>
    norm_num [compareOutputs, FormalProof4FHE.SquaredBias.bitReal,
      probOutput_uniformSample]

/-- Run one adversary on the automorphism transcript and one on the zero-message transcript. -/
def comparisonDistinguisher {View : Type}
    (distinguisher : View → ProbComp Bool) : (View × View) → ProbComp Bool :=
  fun views => do
    let left ← distinguisher views.1
    let right ← distinguisher views.2
    compareOutputs left right

/-- The comparison rule depends only on the two output marginals, even if the two public views
are correlated. -/
theorem probOutput_comparison_true
    {View : Type} [Fintype View]
    (views : ProbComp (View × View))
    (distinguisher : View → ProbComp Bool) :
    Pr[= true | views >>= comparisonDistinguisher distinguisher].toReal =
      (1 +
        Pr[= true | views >>= fun pair => distinguisher pair.1].toReal -
        Pr[= true | views >>= fun pair => distinguisher pair.2].toReal) / 2 := by
  rw [← FormalProof4FHE.SquaredBias.expectation_bitReal]
  rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
  let leftMean : View × View → ℝ := fun pair =>
    FormalProof4FHE.BoundedMoment.expectation
      (distinguisher pair.1) FormalProof4FHE.SquaredBias.bitReal
  let rightMean : View × View → ℝ := fun pair =>
    FormalProof4FHE.BoundedMoment.expectation
      (distinguisher pair.2) FormalProof4FHE.SquaredBias.bitReal
  have hconditioned (pair : View × View) :
      FormalProof4FHE.BoundedMoment.expectation
          (comparisonDistinguisher distinguisher pair)
          FormalProof4FHE.SquaredBias.bitReal =
        (1 + leftMean pair - rightMean pair) / 2 := by
    unfold comparisonDistinguisher
    rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
    have hright (left : Bool) :
        FormalProof4FHE.BoundedMoment.expectation
            (distinguisher pair.2 >>= fun right => compareOutputs left right)
            FormalProof4FHE.SquaredBias.bitReal =
          (1 + FormalProof4FHE.SquaredBias.bitReal left - rightMean pair) / 2 := by
      rw [FormalProof4FHE.SquaredBias.expectation_bind_nested]
      simp_rw [FormalProof4FHE.SquaredBias.expectation_bitReal,
        probOutput_compareOutputs_true]
      have h := FormalProof4FHE.SquaredBias.expectation_affine
        (distinguisher pair.2)
        ((1 + FormalProof4FHE.SquaredBias.bitReal left) / 2) (-1 / 2)
        FormalProof4FHE.SquaredBias.bitReal
      calc
        FormalProof4FHE.BoundedMoment.expectation (distinguisher pair.2)
            (fun right =>
              (1 + FormalProof4FHE.SquaredBias.bitReal left -
                FormalProof4FHE.SquaredBias.bitReal right) / 2) =
          FormalProof4FHE.BoundedMoment.expectation (distinguisher pair.2)
            (fun right => (1 + FormalProof4FHE.SquaredBias.bitReal left) / 2 +
              (-1 / 2) * FormalProof4FHE.SquaredBias.bitReal right) := by
                apply congrArg
                  (FormalProof4FHE.BoundedMoment.expectation (distinguisher pair.2))
                funext right
                ring
        _ = (1 + FormalProof4FHE.SquaredBias.bitReal left) / 2 +
            (-1 / 2) * rightMean pair := h
        _ = (1 + FormalProof4FHE.SquaredBias.bitReal left - rightMean pair) / 2 := by
          ring
    simp_rw [hright]
    have hleft := FormalProof4FHE.SquaredBias.expectation_affine
      (distinguisher pair.1) ((1 - rightMean pair) / 2) (1 / 2)
      FormalProof4FHE.SquaredBias.bitReal
    calc
      FormalProof4FHE.BoundedMoment.expectation (distinguisher pair.1)
          (fun left =>
            (1 + FormalProof4FHE.SquaredBias.bitReal left - rightMean pair) / 2) =
        FormalProof4FHE.BoundedMoment.expectation (distinguisher pair.1)
          (fun left => (1 - rightMean pair) / 2 +
            (1 / 2) * FormalProof4FHE.SquaredBias.bitReal left) := by
              apply congrArg
                (FormalProof4FHE.BoundedMoment.expectation (distinguisher pair.1))
              funext left
              ring
      _ = (1 - rightMean pair) / 2 + (1 / 2) * leftMean pair := hleft
      _ = (1 + leftMean pair - rightMean pair) / 2 := by ring
  simp_rw [hconditioned]
  have hsub := FormalProof4FHE.SquaredBias.expectation_sub views leftMean rightMean
  have haffine := FormalProof4FHE.SquaredBias.expectation_affine views
    (1 / 2) (1 / 2) (fun pair => leftMean pair - rightMean pair)
  rw [hsub] at haffine
  have hleftBind :
      FormalProof4FHE.BoundedMoment.expectation views leftMean =
        Pr[= true | views >>= fun pair => distinguisher pair.1].toReal := by
    rw [← FormalProof4FHE.SquaredBias.expectation_bitReal,
      FormalProof4FHE.SquaredBias.expectation_bind_nested]
  have hrightBind :
      FormalProof4FHE.BoundedMoment.expectation views rightMean =
        Pr[= true | views >>= fun pair => distinguisher pair.2].toReal := by
    rw [← FormalProof4FHE.SquaredBias.expectation_bitReal,
      FormalProof4FHE.SquaredBias.expectation_bind_nested]
  calc
    FormalProof4FHE.BoundedMoment.expectation views
        (fun pair => (1 + leftMean pair - rightMean pair) / 2) =
      FormalProof4FHE.BoundedMoment.expectation views
        (fun pair => 1 / 2 + (1 / 2) * (leftMean pair - rightMean pair)) := by
          apply congrArg (FormalProof4FHE.BoundedMoment.expectation views)
          funext pair
          ring
    _ = 1 / 2 + (1 / 2) *
        (FormalProof4FHE.BoundedMoment.expectation views leftMean -
          FormalProof4FHE.BoundedMoment.expectation views rightMean) := haffine
    _ = (1 +
        Pr[= true | views >>= fun pair => distinguisher pair.1].toReal -
        Pr[= true | views >>= fun pair => distinguisher pair.2].toReal) / 2 := by
          rw [hleftBind, hrightBind]
          ring

/-- Abstract endpoint package discharged by the exact tower encoders above. -/
structure SimultaneousEncoderLaws (View : Type) where
  sourceReal : ProbComp (View × View)
  sourceUniform : ProbComp (View × View)
  autoReal : ProbComp View
  zeroReal : ProbComp View
  uniform : ProbComp View
  sourceRealLeft : evalDist (sourceReal >>= fun views => pure views.1) = evalDist autoReal
  sourceRealRight : evalDist (sourceReal >>= fun views => pure views.2) = evalDist zeroReal
  sourceUniformLeft : evalDist (sourceUniform >>= fun views => pure views.1) = evalDist uniform
  sourceUniformRight : evalDist (sourceUniform >>= fun views => pure views.2) = evalDist uniform

theorem comparison_advantage_eq_half
    {View : Type} [Fintype View]
    (laws : SimultaneousEncoderLaws View)
    (distinguisher : View → ProbComp Bool) :
    BinaryNTTSecurity.advantage
      ⟨laws.sourceReal, laws.sourceUniform⟩
      (comparisonDistinguisher distinguisher) =
      BinaryNTTSecurity.advantage
        ⟨laws.autoReal, laws.zeroReal⟩ distinguisher / 2 := by
  have hrealLeftDist :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      laws.sourceRealLeft distinguisher
  have hrealRightDist :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      laws.sourceRealRight distinguisher
  have hleftDist :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      laws.sourceUniformLeft distinguisher
  have hrightDist :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      laws.sourceUniformRight distinguisher
  have huniformMarginal :
      Pr[= true |
          laws.sourceUniform >>= fun pair => distinguisher pair.1].toReal =
        Pr[= true |
          laws.sourceUniform >>= fun pair => distinguisher pair.2].toReal := by
    have hleft :
        Pr[= true |
            laws.sourceUniform >>= fun pair => distinguisher pair.1] =
          Pr[= true | laws.uniform >>= distinguisher] :=
      evalDist_ext_iff.mp (by simpa only [bind_assoc, pure_bind] using hleftDist) true
    have hright :
        Pr[= true |
            laws.sourceUniform >>= fun pair => distinguisher pair.2] =
          Pr[= true | laws.uniform >>= distinguisher] :=
      evalDist_ext_iff.mp (by simpa only [bind_assoc, pure_bind] using hrightDist) true
    rw [congrArg ENNReal.toReal hleft, congrArg ENNReal.toReal hright]
  have hrealFormula := probOutput_comparison_true laws.sourceReal distinguisher
  have huniformFormula := probOutput_comparison_true laws.sourceUniform distinguisher
  have hautoLeft :
      Pr[= true | laws.sourceReal >>= fun pair => distinguisher pair.1].toReal =
        Pr[= true | laws.autoReal >>= distinguisher].toReal := by
    exact congrArg ENNReal.toReal (evalDist_ext_iff.mp
      (by simpa only [bind_assoc, pure_bind] using hrealLeftDist) true)
  have hzeroRight :
      Pr[= true | laws.sourceReal >>= fun pair => distinguisher pair.2].toReal =
        Pr[= true | laws.zeroReal >>= distinguisher].toReal := by
    exact congrArg ENNReal.toReal (evalDist_ext_iff.mp
      (by simpa only [bind_assoc, pure_bind] using hrealRightDist) true)
  unfold BinaryNTTSecurity.advantage ProbComp.boolDistAdvantage
  rw [hrealFormula, huniformFormula, huniformMarginal,
    hautoLeft, hzeroRight]
  have htwo : (0 : ℝ) < 2 := by norm_num
  rw [show
      (1 + Pr[= true | laws.autoReal >>= distinguisher].toReal -
          Pr[= true | laws.zeroReal >>= distinguisher].toReal) / 2 -
        (1 +
          Pr[= true | laws.sourceUniform >>= fun pair => distinguisher pair.2].toReal -
          Pr[= true | laws.sourceUniform >>= fun pair => distinguisher pair.2].toReal) / 2 =
        (Pr[= true | laws.autoReal >>= distinguisher].toReal -
          Pr[= true | laws.zeroReal >>= distinguisher].toReal) / 2 by ring]
  rw [abs_div, abs_of_pos htwo]

theorem automorphismKDM_advantage_le_twice_source
    {View : Type} [Fintype View]
    (laws : SimultaneousEncoderLaws View)
    (distinguisher : View → ProbComp Bool) :
    BinaryNTTSecurity.advantage
        ⟨laws.autoReal, laws.zeroReal⟩ distinguisher ≤
      2 * BinaryNTTSecurity.advantage
        ⟨laws.sourceReal, laws.sourceUniform⟩
        (comparisonDistinguisher distinguisher) := by
  rw [comparison_advantage_eq_half]
  have hnonneg := abs_nonneg
    (Pr[= true | laws.autoReal >>= distinguisher].toReal -
      Pr[= true | laws.zeroReal >>= distinguisher].toReal)
  unfold BinaryNTTSecurity.advantage ProbComp.boolDistAdvantage at *
  linarith

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.FixedPointFreeAutomorphism
