/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BGVHierarchicalStagedDescent

/-!
# Regular-cover same-key BGV

This module formalizes the algebraic and exact-uniform core of
`sketch/regular_cover_same_key_bgv.tex`.  It does not claim the manuscript's final IND-CPA
theorem without a concrete native BGV public-key hybrid and correctness circuit.
-/

open OracleComp BigOperators

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.RegularCoverSameKeyBGV

noncomputable section

/-- Direct-product regular cover. -/
abbrev Cover (GroupIndex R : Type) := GroupIndex → R

/-- Lift a group action on the base ring to the regular cover. -/
def liftedAction {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (element : GroupIndex) :
    Cover GroupIndex R ≃+* Cover GroupIndex R where
  toFun value coordinate := action element (value (element⁻¹ * coordinate))
  invFun value coordinate := action element⁻¹ (value (element * coordinate))
  left_inv value := by
    funext coordinate
    simp
  right_inv value := by
    funext coordinate
    simp
  map_add' left right := by
    funext coordinate
    simp
  map_mul' left right := by
    funext coordinate
    simp

/-- Lifted automorphisms compose according to the original group law. -/
theorem liftedAction_mul {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (left right : GroupIndex) :
    (liftedAction action left).trans (liftedAction action right) =
      liftedAction action (right * left) := by
  ext value coordinate
  simp only [RingEquiv.trans_apply, liftedAction]
  change (action right) ((action left)
      (value (left⁻¹ * (right⁻¹ * coordinate)))) =
    (action (right * left)) (value ((right * left)⁻¹ * coordinate))
  rw [mul_inv_rev]
  rw [← mul_assoc]
  change (action right * action left)
      (value (left⁻¹ * right⁻¹ * coordinate)) =
    (action (right * left)) (value (left⁻¹ * right⁻¹ * coordinate))
  exact congrArg (fun equivalence : R ≃+* R =>
    equivalence (value (left⁻¹ * right⁻¹ * coordinate)))
    (action.map_mul right left).symm

/-- Constant diagonal embedding. -/
def diagonal {GroupIndex R : Type} (value : R) : Cover GroupIndex R :=
  fun _ => value

/-- Full-dimensional embedding fixed by the lifted regular action. -/
def fixedEmbedding {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (value : R) : Cover GroupIndex R :=
  fun coordinate => action coordinate value

theorem liftedAction_diagonal {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (element : GroupIndex) (value : R) :
    liftedAction action element (diagonal value) =
      diagonal (action element value) := by
  funext coordinate
  rfl

theorem liftedAction_fixedEmbedding {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (element : GroupIndex) (value : R) :
    liftedAction action element (fixedEmbedding action value) =
      fixedEmbedding action value := by
  funext coordinate
  change (action element) ((action (element⁻¹ * coordinate)) value) =
    (action coordinate) value
  change (action element * action (element⁻¹ * coordinate)) value =
    (action coordinate) value
  rw [← action.map_mul]
  simp

/-- Every cover element fixed by the whole lifted regular action comes from the base ring. -/
theorem eq_fixedEmbedding_of_fixed {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (value : Cover GroupIndex R)
    (hfixed : ∀ element, liftedAction action element value = value) :
    value = fixedEmbedding action (value 1) := by
  funext coordinate
  have hcoordinate := congrFun (hfixed coordinate) coordinate
  simpa [liftedAction, fixedEmbedding] using hcoordinate.symm

/-- Exact description of the invariant cover elements. -/
theorem fixed_iff_mem_fixedEmbedding {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (value : Cover GroupIndex R) :
    (∀ element, liftedAction action element value = value) ↔
      ∃ base, value = fixedEmbedding action base := by
  constructor
  · intro hfixed
    exact ⟨value 1, eq_fixedEmbedding_of_fixed action value hfixed⟩
  · rintro ⟨base, rfl⟩ element
    exact liftedAction_fixedEmbedding action element base

/-! ## Exact regular-orbit Binary-NTT completion -/

/-- Bottom orbit bits and one completion bit for every nonidentity cover coordinate. -/
abbrev CoverCompletionSource (GroupIndex Slot : Type) [One GroupIndex] :=
  (Slot → Bool) × ({element : GroupIndex // element ≠ 1} → Slot → Bool)

def coverCompletionBits {GroupIndex Slot : Type}
    [One GroupIndex] [DecidableEq GroupIndex]
    (source : CoverCompletionSource GroupIndex Slot) : GroupIndex → Slot → Bool :=
  fun element slot =>
    if helement : element = 1 then source.1 slot
    else xor (source.1 slot) (source.2 ⟨element, helement⟩ slot)

def recoverCoverCompletion {GroupIndex Slot : Type}
    [One GroupIndex] [DecidableEq GroupIndex]
    (completed : GroupIndex → Slot → Bool) : CoverCompletionSource GroupIndex Slot :=
  (completed 1, fun element slot => xor (completed 1 slot) (completed element.1 slot))

@[simp]
theorem recoverCoverCompletion_coverCompletionBits {GroupIndex Slot : Type}
    [One GroupIndex] [DecidableEq GroupIndex]
    (source : CoverCompletionSource GroupIndex Slot) :
    recoverCoverCompletion (coverCompletionBits source) = source := by
  rcases source with ⟨bottom, coins⟩
  apply Prod.ext
  · funext slot
    simp [recoverCoverCompletion, coverCompletionBits]
  · funext element slot
    simp [recoverCoverCompletion, coverCompletionBits, element.2]

@[simp]
theorem coverCompletionBits_recoverCoverCompletion {GroupIndex Slot : Type}
    [One GroupIndex] [DecidableEq GroupIndex]
    (completed : GroupIndex → Slot → Bool) :
    coverCompletionBits (recoverCoverCompletion completed) = completed := by
  funext element slot
  by_cases helement : element = 1
  · subst element
    simp [coverCompletionBits, recoverCoverCompletion]
  · simp [coverCompletionBits, recoverCoverCompletion, helement]

/-- Regular-cover completion is an exact equivalence with all cover Binary-NTT bits. -/
def coverCompletionEquiv (GroupIndex Slot : Type)
    [One GroupIndex] [DecidableEq GroupIndex] :
    CoverCompletionSource GroupIndex Slot ≃ (GroupIndex → Slot → Bool) where
  toFun := coverCompletionBits
  invFun := recoverCoverCompletion
  left_inv := recoverCoverCompletion_coverCompletionBits
  right_inv := coverCompletionBits_recoverCoverCompletion

theorem coverCompletion_uniform_evalDist
    (GroupIndex Slot : Type)
    [Fintype GroupIndex] [DecidableEq GroupIndex] [One GroupIndex]
    [Fintype Slot]
    [SampleableType (CoverCompletionSource GroupIndex Slot)]
    [SampleableType (GroupIndex → Slot → Bool)] :
    evalDist (coverCompletionEquiv GroupIndex Slot <$>
        ($ᵗ (CoverCompletionSource GroupIndex Slot))) =
      evalDist ($ᵗ (GroupIndex → Slot → Bool)) :=
  evalDist_map_bijective_uniform_cross
    (α := CoverCompletionSource GroupIndex Slot)
    (β := GroupIndex → Slot → Bool)
    (coverCompletionEquiv GroupIndex Slot)
    (coverCompletionEquiv GroupIndex Slot).bijective

/-! ## Exact cover-sample assembly -/

def assembleCover {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (values : GroupIndex → R) : Cover GroupIndex R :=
  fun coordinate => action coordinate (values coordinate)

def disassembleCover {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (values : Cover GroupIndex R) : GroupIndex → R :=
  fun coordinate => action coordinate⁻¹ (values coordinate)

@[simp]
theorem disassembleCover_assembleCover {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (values : GroupIndex → R) :
    disassembleCover action (assembleCover action values) = values := by
  funext coordinate
  simp [assembleCover, disassembleCover]

@[simp]
theorem assembleCover_disassembleCover {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (values : Cover GroupIndex R) :
    assembleCover action (disassembleCover action values) = values := by
  funext coordinate
  simp [assembleCover, disassembleCover]

theorem assembleCover_bijective {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) :
    Function.Bijective (assembleCover action) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨disassembleCover action, disassembleCover_assembleCover action,
      assembleCover_disassembleCover action⟩

theorem assembleCover_uniform_evalDist {GroupIndex R : Type}
    [Group GroupIndex] [Fintype GroupIndex] [DecidableEq GroupIndex]
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (GroupIndex → R)]
    (action : GroupIndex →* R ≃+* R) :
    evalDist (assembleCover action <$> ($ᵗ (GroupIndex → R))) =
      evalDist ($ᵗ (Cover GroupIndex R)) :=
  evalDist_map_bijective_uniform_cross
    (α := GroupIndex → R) (β := Cover GroupIndex R)
    (assembleCover action) (assembleCover_bijective action)

/-- Componentwise assembly preserves the common-secret RLWE equation exactly. -/
theorem assembleCover_real {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (mask error : GroupIndex → R) (secret : R) :
    assembleCover action (fun coordinate => mask coordinate * secret + error coordinate) =
      assembleCover action mask * fixedEmbedding action secret +
        assembleCover action error := by
  funext coordinate
  simp [assembleCover, fixedEmbedding]

/-! ## Simultaneous affine-automorphism compiler -/

def compilerMask {Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (sourceMask : R) : R :=
  (sourceMask - ∑ index, weights index * sigma index multiplier) * ↑(multiplier⁻¹)

def compilerBody {Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (offset sourceBody targetMask : R) : R :=
  sourceBody + targetMask * offset +
    ∑ index, weights index * sigma index offset

theorem compilerMask_reconstruct {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (sourceMask : R) :
    compilerMask sigma weights multiplier sourceMask * multiplier +
        ∑ index, weights index * sigma index multiplier = sourceMask := by
  simp [compilerMask]

theorem compilerBody_real {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset invariant error sourceMask : R)
    (hfixed : ∀ index, sigma index invariant = invariant) :
    compilerBody sigma weights offset (sourceMask * invariant + error)
        (compilerMask sigma weights multiplier sourceMask) =
      compilerMask sigma weights multiplier sourceMask *
          (multiplier * invariant + offset) + error +
        ∑ index, weights index * sigma index (multiplier * invariant + offset) := by
  let targetMask := compilerMask sigma weights multiplier sourceMask
  have hreconstruct :
      targetMask * (multiplier : R) +
          ∑ index, weights index * sigma index multiplier = sourceMask :=
    compilerMask_reconstruct sigma weights multiplier sourceMask
  change sourceMask * invariant + error + targetMask * offset +
      ∑ index, weights index * sigma index offset =
    targetMask * ((multiplier : R) * invariant + offset) + error +
      ∑ index, weights index * sigma index
        ((multiplier : R) * invariant + offset)
  rw [← hreconstruct]
  simp_rw [map_add, map_mul, hfixed, mul_add, Finset.sum_add_distrib]
  simp only [add_mul, Finset.sum_mul]
  ring_nf

def compilerRow {Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset : R) (source : R × R) : R × R :=
  let targetMask := compilerMask sigma weights multiplier source.1
  (targetMask, compilerBody sigma weights offset source.2 targetMask)

def compilerRowInv {Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset : R) (target : R × R) : R × R :=
  (target.1 * multiplier + ∑ index, weights index * sigma index multiplier,
    target.2 - target.1 * offset -
      ∑ index, weights index * sigma index offset)

@[simp]
theorem compilerRowInv_compilerRow {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset : R) (source : R × R) :
    compilerRowInv sigma weights multiplier offset
      (compilerRow sigma weights multiplier offset source) = source := by
  rcases source with ⟨mask, body⟩
  simp [compilerRow, compilerRowInv, compilerBody, compilerMask]
  ring

@[simp]
theorem compilerRow_compilerRowInv {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset : R) (target : R × R) :
    compilerRow sigma weights multiplier offset
      (compilerRowInv sigma weights multiplier offset target) = target := by
  rcases target with ⟨mask, body⟩
  simp [compilerRow, compilerRowInv, compilerBody, compilerMask]
  ring

theorem compilerRow_bijective {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset : R) :
    Function.Bijective (compilerRow sigma weights multiplier offset) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨compilerRowInv sigma weights multiplier offset,
      compilerRowInv_compilerRow sigma weights multiplier offset,
      compilerRow_compilerRowInv sigma weights multiplier offset⟩

theorem compilerRow_uniform_evalDist {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (R × R)]
    (sigma : Sigma → R ≃+* R) (weights : Sigma → R)
    (multiplier : Rˣ) (offset : R) :
    evalDist (compilerRow sigma weights multiplier offset <$> ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R)
    (compilerRow sigma weights multiplier offset)
    (compilerRow_bijective sigma weights multiplier offset)

/-- Apply the simultaneous automorphism compiler to a complete family of rows. -/
def compilerBatch {Row Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Row → Sigma → R)
    (multiplier : Rˣ) (offset : R) (source : Row → R × R) : Row → R × R :=
  fun row => compilerRow sigma (weights row) multiplier offset (source row)

def compilerBatchInv {Row Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Row → Sigma → R)
    (multiplier : Rˣ) (offset : R) (target : Row → R × R) : Row → R × R :=
  fun row => compilerRowInv sigma (weights row) multiplier offset (target row)

theorem compilerBatch_bijective {Row Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (weights : Row → Sigma → R)
    (multiplier : Rˣ) (offset : R) :
    Function.Bijective (compilerBatch sigma weights multiplier offset) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨compilerBatchInv sigma weights multiplier offset, ?_, ?_⟩
  · intro source
    funext row
    simp [compilerBatch, compilerBatchInv]
  · intro target
    funext row
    simp [compilerBatch, compilerBatchInv]

theorem compilerBatch_uniform_evalDist {Row Sigma R : Type}
    [Finite Row] [DecidableEq Row] [Fintype Sigma] [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (Row → R × R)]
    (sigma : Sigma → R ≃+* R) (weights : Row → Sigma → R)
    (multiplier : Rˣ) (offset : R) :
    evalDist (compilerBatch sigma weights multiplier offset <$>
        ($ᵗ (Row → R × R))) =
      evalDist ($ᵗ (Row → R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Row → R × R) (β := Row → R × R)
    (compilerBatch sigma weights multiplier offset)
    (compilerBatch_bijective sigma weights multiplier offset)

/-! ## Unit-pivot success arithmetic -/

/-- Bernoulli lower bound used by the cover pivot: if the split dimension is at most half the
field size, a uniform split-ring element is a unit with probability at least one half. -/
theorem splitUnitProbability_ge_half (dimension q : ℕ)
    (hq : 0 < q) (hdimension : 2 * dimension ≤ q) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (q : ℝ)) ^ dimension := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hinv : 1 / (q : ℝ) ≤ 1 := (div_le_one hqpos).mpr hqone
  have ha : (-2 : ℝ) ≤ -(1 / (q : ℝ)) := by linarith
  have hbernoulli := one_add_mul_le_pow ha dimension
  have hratio : (dimension : ℝ) / q ≤ 1 / 2 := by
    rw [div_le_iff₀ hqpos]
    have hcast : (2 : ℝ) * dimension ≤ q := by exact_mod_cast hdimension
    nlinarith
  have hone : 1 + (dimension : ℝ) * (-(1 / (q : ℝ))) =
      1 - (dimension : ℝ) / q := by
    field_simp
    ring
  rw [hone] at hbernoulli
  have hbase : (1 : ℝ) + -(1 / (q : ℝ)) = 1 - 1 / (q : ℝ) := by ring
  rw [hbase] at hbernoulli
  linarith

/-- Repeating a trial whose failure probability is at most one half gives failure at most
`2^{-attempts}`. -/
theorem repeatedPivotFailure_le (failure : ℝ) (attempts : ℕ)
    (hfailure_nonneg : 0 ≤ failure) (hfailure : failure ≤ 1 / 2) :
    failure ^ attempts ≤ (1 / 2 : ℝ) ^ attempts :=
  pow_le_pow_left₀ hfailure_nonneg hfailure attempts

/-! ## Pivot to a coefficient-small operational secret -/

def pivotBeta {R : Type} [CommRing R] (alpha witness operational : R) : R :=
  alpha * witness + operational

def hintU {R : Type} [CommRing R] (alpha beta : R) : R :=
  2 * beta - alpha

def hintV {R : Type} [CommRing R] (alpha beta : R) : R :=
  alpha * beta - beta ^ 2

theorem pivot_quadratic_hint {R : Type} [CommRing R]
    (alpha witness operational : R) (hidempotent : witness ^ 2 = witness) :
    operational ^ 2 =
      hintU alpha (pivotBeta alpha witness operational) * operational +
        hintV alpha (pivotBeta alpha witness operational) := by
  symm
  simp only [pivotBeta, hintU, hintV]
  calc
    _ = operational ^ 2 + alpha ^ 2 * (witness - witness ^ 2) := by ring
    _ = operational ^ 2 := by rw [hidempotent]; ring

/-- Convert an ordinary row under the witness secret to the operational secret. -/
def pivotOrdinaryRow {R : Type} [CommRing R]
    (alpha : Rˣ) (beta : R) (source : R × R) : R × R :=
  (-source.1 * ↑(alpha⁻¹), source.2 - source.1 * ↑(alpha⁻¹) * beta)

theorem pivotOrdinaryRow_real {R : Type} [CommRing R]
    (alpha : Rˣ) (witness operational error mask : R)
    (beta : R) (hbeta : beta = alpha * witness + operational) :
    (pivotOrdinaryRow alpha beta (mask, mask * witness + error)).2 -
        (pivotOrdinaryRow alpha beta (mask, mask * witness + error)).1 * operational =
      error := by
  subst beta
  have hunit : (↑(alpha⁻¹) : R) * alpha = 1 := by simp
  simp only [pivotOrdinaryRow, neg_mul]
  ring_nf
  rw [mul_assoc (mask * witness), hunit]
  ring

def pivotOrdinaryRowInv {R : Type} [CommRing R]
    (alpha : Rˣ) (beta : R) (target : R × R) : R × R :=
  (-target.1 * alpha, target.2 - target.1 * beta)

theorem pivotOrdinaryRow_bijective {R : Type} [CommRing R]
    (alpha : Rˣ) (beta : R) :
    Function.Bijective (pivotOrdinaryRow alpha beta) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨pivotOrdinaryRowInv alpha beta, ?_, ?_⟩
  · intro source
    rcases source with ⟨mask, body⟩
    simp [pivotOrdinaryRow, pivotOrdinaryRowInv]
  · intro target
    rcases target with ⟨mask, body⟩
    simp [pivotOrdinaryRow, pivotOrdinaryRowInv]

theorem pivotOrdinaryRow_uniform_evalDist {R : Type} [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (R × R)]
    (alpha : Rˣ) (beta : R) :
    evalDist (pivotOrdinaryRow alpha beta <$> ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R) (pivotOrdinaryRow alpha beta)
    (pivotOrdinaryRow_bijective alpha beta)

/-- Convert a compiled witness-secret row into an affine-automorphism row under the operational
secret. -/
def pivotAffineRow {Sigma R : Type} [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (coefficients : Sigma → R)
    (alpha : Rˣ) (beta constant : R) (source : R × R) : R × R :=
  let converted := pivotOrdinaryRow alpha beta source
  (converted.1,
    converted.2 + constant +
      ∑ index, coefficients index * sigma index beta)

theorem pivotAffineRow_phase {Sigma R : Type}
    [Fintype Sigma] [CommRing R]
    (sigma : Sigma → R ≃+* R) (coefficients : Sigma → R)
    (alpha : Rˣ) (beta constant witness operational error : R)
    (source : R × R)
    (hbeta : beta = alpha * witness + operational)
    (hsource : source.2 - source.1 * witness =
      error - ∑ index,
        coefficients index * sigma index alpha * sigma index witness) :
    (pivotAffineRow sigma coefficients alpha beta constant source).2 -
        (pivotAffineRow sigma coefficients alpha beta constant source).1 * operational =
      error + constant +
        ∑ index, coefficients index * sigma index operational := by
  subst beta
  have hunit : (↑(alpha⁻¹) : R) * alpha = 1 := by simp
  simp only [pivotAffineRow, pivotOrdinaryRow]
  rw [show source.2 = source.1 * witness +
      (error - ∑ index,
        coefficients index * sigma index alpha * sigma index witness) by
    calc
      source.2 = source.1 * witness +
          (source.2 - source.1 * witness) := by abel
      _ = _ := by rw [hsource]]
  simp_rw [map_add, map_mul, mul_add]
  rw [Finset.sum_add_distrib]
  ring_nf
  rw [mul_assoc (source.1 * witness), hunit]
  ring

/-- Public quadratic-hint multiplication of two two-component ciphertexts. -/
def quadraticHintMul {R : Type} [CommRing R]
    (u v : R) (left right : R × R) : R × R :=
  (left.1 * right.2 + right.1 * left.2 - left.1 * right.1 * u,
    left.2 * right.2 + left.1 * right.1 * v)

theorem quadraticHintMul_phase {R : Type} [CommRing R]
    (secret u v : R) (hhint : secret ^ 2 = u * secret + v)
    (left right : R × R) :
    (quadraticHintMul u v left right).2 -
        (quadraticHintMul u v left right).1 * secret =
      (left.2 - left.1 * secret) * (right.2 - right.1 * secret) := by
  simp [quadraticHintMul]
  calc
    left.2 * right.2 + left.1 * right.1 * v -
          (left.1 * right.2 + right.1 * left.2 - left.1 * right.1 * u) * secret =
      (left.2 - left.1 * secret) * (right.2 - right.1 * secret) +
        left.1 * right.1 * (u * secret + v - secret ^ 2) := by ring
    _ = _ := by rw [← hhint]; ring

/-! ## Automorphism switching -/

def automorphismSwitch {Digit R : Type} [Fintype Digit] [CommRing R]
    (sigma : R ≃+* R) (digits : Digit → R)
    (keys : Digit → R × R) (ciphertext : R × R) : R × R :=
  (-∑ index, digits index * (keys index).1,
    sigma ciphertext.2 - ∑ index, digits index * (keys index).2)

theorem automorphismSwitch_phase {Digit R : Type}
    [Fintype Digit] [CommRing R]
    (sigma : R ≃+* R) (digits gadget errors : Digit → R)
    (keys : Digit → R × R) (secret plaintextScale : R)
    (ciphertext : R × R)
    (hdecompose : sigma ciphertext.1 = ∑ index, digits index * gadget index)
    (hkeys : ∀ index, (keys index).2 - (keys index).1 * secret =
      gadget index * sigma secret + plaintextScale * errors index) :
    (automorphismSwitch sigma digits keys ciphertext).2 -
        (automorphismSwitch sigma digits keys ciphertext).1 * secret =
      sigma (ciphertext.2 - ciphertext.1 * secret) -
        plaintextScale * ∑ index, digits index * errors index := by
  simp only [automorphismSwitch, map_sub, map_mul, hdecompose]
  have hbody (index : Digit) :
      (keys index).2 = (keys index).1 * secret +
        (gadget index * sigma secret + plaintextScale * errors index) := by
    calc
      (keys index).2 = (keys index).1 * secret +
          ((keys index).2 - (keys index).1 * secret) := by abel
      _ = _ := by rw [hkeys index]
  simp_rw [hbody, mul_add, Finset.sum_add_distrib]
  have hmask :
      (∑ index, digits index * ((keys index).1 * secret)) =
        (∑ index, digits index * (keys index).1) * secret := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index _
    ring
  have hgadget :
      (∑ index, digits index * (gadget index * sigma secret)) =
        (∑ index, digits index * gadget index) * sigma secret := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index _
    ring
  have herror :
      (∑ index, digits index * (plaintextScale * errors index)) =
        plaintextScale * ∑ index, digits index * errors index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hmask, hgadget, herror]
  ring

/-! ## Circuit lifting on diagonal plaintexts -/

inductive RingCircuit (GroupIndex R : Type) where
  | input : ℕ → RingCircuit GroupIndex R
  | constant : R → RingCircuit GroupIndex R
  | add : RingCircuit GroupIndex R → RingCircuit GroupIndex R → RingCircuit GroupIndex R
  | mul : RingCircuit GroupIndex R → RingCircuit GroupIndex R → RingCircuit GroupIndex R
  | automorphism : GroupIndex → RingCircuit GroupIndex R → RingCircuit GroupIndex R

def RingCircuit.evalBase {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (inputs : ℕ → R) :
    RingCircuit GroupIndex R → R
  | .input index => inputs index
  | .constant value => value
  | .add left right => left.evalBase action inputs + right.evalBase action inputs
  | .mul left right => left.evalBase action inputs * right.evalBase action inputs
  | .automorphism element circuit => action element (circuit.evalBase action inputs)

def RingCircuit.evalCover {GroupIndex R : Type} [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (inputs : ℕ → Cover GroupIndex R) :
    RingCircuit GroupIndex R → Cover GroupIndex R
  | .input index => inputs index
  | .constant value => diagonal value
  | .add left right => left.evalCover action inputs + right.evalCover action inputs
  | .mul left right => left.evalCover action inputs * right.evalCover action inputs
  | .automorphism element circuit =>
      liftedAction action element (circuit.evalCover action inputs)

theorem RingCircuit.evalCover_diagonal {GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R) (inputs : ℕ → R)
    (circuit : RingCircuit GroupIndex R) :
    circuit.evalCover action (fun index => diagonal (inputs index)) =
      diagonal (circuit.evalBase action inputs) := by
  induction circuit with
  | input index => rfl
  | constant value => rfl
  | add left right hleft hright =>
      simp only [RingCircuit.evalCover, RingCircuit.evalBase, hleft, hright]
      funext coordinate
      rfl
  | mul left right hleft hright =>
      simp only [RingCircuit.evalCover, RingCircuit.evalBase, hleft, hright]
      funext coordinate
      rfl
  | automorphism element circuit ih =>
      simp [RingCircuit.evalCover, RingCircuit.evalBase, ih, liftedAction_diagonal]

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.RegularCoverSameKeyBGV
