/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.IntervalMaskedQuadratic
import FormalProof4FHE.TFHE.NativeTRGSWQuadraticKDMAndTFHET
import FormalProof4FHE.TFHE.RGSWCoefficientCircularSecurity

/-!
# Minimal circular assumptions for true self-key TFHE

This file formalizes the internal theorems and assumption hierarchy of
`sketch/tfhe_circular_security_minimal_assumption.tex`.

The finite algebra says:

* a native nonce row is exactly message-RLWE with plaintext `-mu * S`;
* every public ring-affine plaintext `alpha * S + beta` is obtained from a homogeneous row by
  the public translation `(A,B) ↦ (A-alpha,B+beta)`, jointly over an arbitrary finite batch;
* aggregating the native body rows gives a scaled encryption of `S`;
* negating and aggregating the native nonce rows gives a scaled encryption of `S^2`.

The probabilistic layer defines complete self, independent-copy, and zero experiments without
restricting the view carrier.  Therefore the view may contain the entire BRK, a designated
same-key auxiliary tape, serialization state, and any other fixed public component.  No
universal auxiliary leakage is asserted.

Two named assumption interfaces are exposed as ordinary propositions, not Lean axioms:

* coefficient-product correlation: replace the control secret in the complete view by an
  independent copy while retaining the encryption secret;
* square correlation: replace `S^2` by `S*S'` in a specified projected square view.

The independent-copy-to-zero endpoint and the final zero-to-ideal endpoint remain separate
premises.  Exact triangle theorems prove the manuscript's bounds with every loss charged once.
Public projection proves the forward coefficient-product-to-square implication; no converse is
claimed because aggregation discards the individual native control rows.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.CircularSecurityMinimalAssumption

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWQuadraticKDMAndTFHET

/-! ## Native message-RLWE row algebra -/

/-- A two-component ring row. -/
abbrev MessageRow (R : Type) := NativeRow R

/-- Rank-one RLWE phase convention `B - A*S`. -/
def phase {R : Type} [CommRing R] (secret : R) (row : MessageRow R) : R :=
  row.2 - row.1 * secret

@[simp]
theorem phase_mk {R : Type} [CommRing R] (secret mask body : R) :
    phase secret (mask, body) = body - mask * secret :=
  rfl

/-- The public translation which installs the ring-affine plaintext `alpha*S + beta`. -/
def affineTranslateRow {R : Type} [CommRing R]
    (alpha beta : R) (row : MessageRow R) : MessageRow R :=
  (row.1 - alpha, row.2 + beta)

/-- Explicit inverse of `affineTranslateRow`. -/
def affineUntranslateRow {R : Type} [CommRing R]
    (alpha beta : R) (row : MessageRow R) : MessageRow R :=
  (row.1 + alpha, row.2 - beta)

@[simp]
theorem affineUntranslateRow_translate {R : Type} [CommRing R]
    (alpha beta : R) (row : MessageRow R) :
    affineUntranslateRow alpha beta (affineTranslateRow alpha beta row) = row := by
  rcases row with ⟨mask, body⟩
  simp [affineTranslateRow, affineUntranslateRow]

@[simp]
theorem affineTranslateRow_untranslate {R : Type} [CommRing R]
    (alpha beta : R) (row : MessageRow R) :
    affineTranslateRow alpha beta (affineUntranslateRow alpha beta row) = row := by
  rcases row with ⟨mask, body⟩
  simp [affineTranslateRow, affineUntranslateRow]

/-- Public ring-affine row translation is a permutation of the complete row carrier. -/
theorem affineTranslateRow_bijective {R : Type} [CommRing R]
    (alpha beta : R) :
    Function.Bijective (affineTranslateRow alpha beta : MessageRow R → MessageRow R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨affineUntranslateRow alpha beta,
      affineUntranslateRow_translate alpha beta,
      affineTranslateRow_untranslate alpha beta⟩

/-- The exact affine-KDM phase identity from a homogeneous row. -/
theorem affineTranslateRow_homogeneous {R : Type} [CommRing R]
    (secret mask error alpha beta : R) :
    affineTranslateRow alpha beta (homogeneousRow secret mask error) =
      (mask - alpha,
        (mask - alpha) * secret + error + (alpha * secret + beta)) := by
  apply Prod.ext
  · rfl
  · simp only [affineTranslateRow, homogeneousRow]
    ring

/-- Equivalently, public translation adds exactly `alpha*S + beta` to the phase. -/
theorem phase_affineTranslateRow {R : Type} [CommRing R]
    (secret alpha beta : R) (row : MessageRow R) :
    phase secret (affineTranslateRow alpha beta row) =
      phase secret row + alpha * secret + beta := by
  rcases row with ⟨mask, body⟩
  simp only [phase, affineTranslateRow]
  ring

/-- A fixed public affine translation preserves an exactly uniform row. -/
theorem affineTranslateRow_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (alpha beta : R) :
    evalDist (affineTranslateRow alpha beta <$> ($ᵗ (MessageRow R))) =
      evalDist ($ᵗ (MessageRow R)) :=
  evalDist_map_bijective_uniform_cross
    (α := MessageRow R) (β := MessageRow R)
    (affineTranslateRow alpha beta)
    (affineTranslateRow_bijective alpha beta)

/-- Native body placement is the affine translation with `(alpha,beta)=(0,mu)`. -/
theorem affineTranslateRow_homogeneous_eq_nativeBodyRow
    {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (mask error : R) :
    affineTranslateRow 0 (gadget * bitScalar message)
        (homogeneousRow secret mask error) =
      nativeBodyRow secret gadget message mask error := by
  apply Prod.ext <;>
    simp [affineTranslateRow, homogeneousRow, nativeBodyRow]

/-- Native nonce placement is the affine translation with `alpha=-mu` and `beta=0`. -/
theorem affineTranslateRow_homogeneous_eq_nativeNonceRow
    {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (mask error : R) :
    affineTranslateRow (-(gadget * bitScalar message)) 0
        (homogeneousRow secret mask error) =
      nativeNonceRow secret gadget message mask error := by
  apply Prod.ext
  · simp [affineTranslateRow, homogeneousRow, nativeNonceRow]
  · simp [affineTranslateRow, homogeneousRow, nativeNonceRow]

/-- Direct phase form of an unnormalized native nonce row. -/
theorem nativeNonceRow_phase {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (mask error : R) :
    phase secret (nativeNonceRow secret gadget message mask error) =
      -(gadget * bitScalar message * secret) + error := by
  simp only [phase, nativeNonceRow]
  ring

/-- Direct phase form of a native body row. -/
theorem nativeBodyRow_phase' {R : Type} [CommRing R]
    (secret gadget : R) (message : Bool) (mask error : R) :
    phase secret (nativeBodyRow secret gadget message mask error) =
      gadget * bitScalar message + error := by
  exact nativeBodyRow_phase secret gadget message mask error

/-! ## Complete public affine batches -/

/-- A complete finite row batch.  Its index may include row type, control coordinate, and
gadget level. -/
abbrev MessageBatch (R Index : Type) := Index → MessageRow R

/-- Coordinatewise public ring-affine translation. -/
def affineTranslateBatch {R Index : Type} [CommRing R]
    (alpha beta : Index → R) (rows : MessageBatch R Index) : MessageBatch R Index :=
  fun index ↦ affineTranslateRow (alpha index) (beta index) (rows index)

/-- Coordinatewise inverse translation. -/
def affineUntranslateBatch {R Index : Type} [CommRing R]
    (alpha beta : Index → R) (rows : MessageBatch R Index) : MessageBatch R Index :=
  fun index ↦ affineUntranslateRow (alpha index) (beta index) (rows index)

@[simp]
theorem affineUntranslateBatch_translate {R Index : Type} [CommRing R]
    (alpha beta : Index → R) (rows : MessageBatch R Index) :
    affineUntranslateBatch alpha beta (affineTranslateBatch alpha beta rows) = rows := by
  funext index
  exact affineUntranslateRow_translate (alpha index) (beta index) (rows index)

@[simp]
theorem affineTranslateBatch_untranslate {R Index : Type} [CommRing R]
    (alpha beta : Index → R) (rows : MessageBatch R Index) :
    affineTranslateBatch alpha beta (affineUntranslateBatch alpha beta rows) = rows := by
  funext index
  exact affineTranslateRow_untranslate (alpha index) (beta index) (rows index)

theorem affineTranslateBatch_bijective {R Index : Type} [CommRing R]
    (alpha beta : Index → R) :
    Function.Bijective
      (affineTranslateBatch alpha beta : MessageBatch R Index → MessageBatch R Index) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨affineUntranslateBatch alpha beta,
      affineUntranslateBatch_translate alpha beta,
      affineTranslateBatch_untranslate alpha beta⟩

/-- Public affine translation preserves the exact uniform law of the whole batch, rather than
only its row marginals. -/
theorem affineTranslateBatch_uniform_evalDist
    {R Index : Type} [CommRing R] [Fintype R] [Fintype Index]
    [SampleableType (MessageBatch R Index)]
    (alpha beta : Index → R) :
    evalDist (affineTranslateBatch alpha beta <$> ($ᵗ (MessageBatch R Index))) =
      evalDist ($ᵗ (MessageBatch R Index)) :=
  evalDist_map_bijective_uniform_cross
    (α := MessageBatch R Index) (β := MessageBatch R Index)
    (affineTranslateBatch alpha beta)
    (affineTranslateBatch_bijective alpha beta)

/-- Deterministic homogeneous batch with an arbitrary complete error vector. -/
def homogeneousBatch {R Index : Type} [CommRing R]
    (secret : R) (masks errors : Index → R) : MessageBatch R Index :=
  fun index ↦ homogeneousRow secret (masks index) (errors index)

/-- The batch version of public ring-affine KDM closure preserves every coordinate of the
supplied joint error vector. -/
theorem affineTranslateBatch_homogeneous {R Index : Type} [CommRing R]
    (secret : R) (masks errors alpha beta : Index → R) :
    affineTranslateBatch alpha beta (homogeneousBatch secret masks errors) =
      fun index ↦
        (masks index - alpha index,
          (masks index - alpha index) * secret + errors index +
            (alpha index * secret + beta index)) := by
  funext index
  exact affineTranslateRow_homogeneous secret (masks index) (errors index)
    (alpha index) (beta index)

/-! ## Generic complete-view advantages -/

/-- A public probabilistic distinguisher. -/
abbrev Distinguisher (View : Type) := View → ProbComp Bool

/-- Distinguishing advantage between two complete view samplers. -/
def distinguishingAdvantage {View : Type}
    (left right : ProbComp View) (distinguisher : Distinguisher View) : ℝ :=
  (left >>= distinguisher).boolDistAdvantage (right >>= distinguisher)

theorem distinguishingAdvantage_symm {View : Type}
    (left right : ProbComp View) (distinguisher : Distinguisher View) :
    distinguishingAdvantage left right distinguisher =
      distinguishingAdvantage right left distinguisher := by
  unfold distinguishingAdvantage ProbComp.boolDistAdvantage
  rw [abs_sub_comm]

theorem distinguishingAdvantage_triangle {View : Type}
    (first middle last : ProbComp View) (distinguisher : Distinguisher View) :
    distinguishingAdvantage first last distinguisher ≤
      distinguishingAdvantage first middle distinguisher +
        distinguishingAdvantage middle last distinguisher := by
  exact ProbComp.boolDistAdvantage_triangle
    (first >>= distinguisher) (middle >>= distinguisher) (last >>= distinguisher)

/-! ## Exact two-branch standard endpoint -/

/-- Sample a known public prefix and apply one of two public affine translations to a complete
source batch.  The false branch is allowed its own translation; native real/zero endpoints use
the body/nonce shifts in the true branch and zero shifts in the false branch. -/
def affineBranchView {R Index Prefix : Type} [CommRing R]
    (prefixSampler : ProbComp Prefix) (source : ProbComp (MessageBatch R Index))
    (alpha beta : Bool → Prefix → Index → R) (branch : Bool) :
    ProbComp (MessageBatch R Index) := do
  let prefixValue ← prefixSampler
  let rows ← source
  return affineTranslateBatch (alpha branch prefixValue) (beta branch prefixValue) rows

/-- The whole uniform batch erases the branch exactly for every prefix when the two branches are
public affine translations. -/
theorem affineBranchView_uniform_evalDist_eq
    {R Index Prefix : Type} [CommRing R] [Fintype R] [Fintype Index]
    [SampleableType (MessageBatch R Index)]
    (prefixSampler : ProbComp Prefix)
    (alpha beta : Bool → Prefix → Index → R) :
    evalDist (affineBranchView prefixSampler ($ᵗ (MessageBatch R Index))
        alpha beta true) =
      evalDist (affineBranchView prefixSampler ($ᵗ (MessageBatch R Index))
        alpha beta false) := by
  unfold affineBranchView
  refine evalDist_bind_congr' prefixSampler fun prefixValue ↦ ?_
  have htrue := affineTranslateBatch_uniform_evalDist
    (alpha true prefixValue) (beta true prefixValue)
  have hfalse := affineTranslateBatch_uniform_evalDist
    (alpha false prefixValue) (beta false prefixValue)
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using htrue.trans hfalse.symm

/-- Advantage between the two real-source affine branches. -/
def affineTargetAdvantage {R Index Prefix : Type} [CommRing R]
    (prefixSampler : ProbComp Prefix) (realSource : ProbComp (MessageBatch R Index))
    (alpha beta : Bool → Prefix → Index → R)
    (distinguisher : MessageBatch R Index → ProbComp Bool) : ℝ :=
  distinguishingAdvantage
    (affineBranchView prefixSampler realSource alpha beta true)
    (affineBranchView prefixSampler realSource alpha beta false)
    distinguisher

/-- One ordinary real-versus-uniform source advantage for a selected branch translation. -/
def affineSourceAdvantage {R Index Prefix : Type} [CommRing R]
    (prefixSampler : ProbComp Prefix)
    (realSource uniformSource : ProbComp (MessageBatch R Index))
    (alpha beta : Bool → Prefix → Index → R) (branch : Bool)
    (distinguisher : MessageBatch R Index → ProbComp Bool) : ℝ :=
  distinguishingAdvantage
    (affineBranchView prefixSampler realSource alpha beta branch)
    (affineBranchView prefixSampler uniformSource alpha beta branch)
    distinguisher

theorem distinguishingAdvantage_eq_zero_of_evalDist_eq
    {View : Type} {left right : ProbComp View}
    (h : evalDist left = evalDist right) (distinguisher : Distinguisher View) :
    distinguishingAdvantage left right distinguisher = 0 := by
  have hdecision := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    h distinguisher
  unfold distinguishingAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl hdecision]
  simp

/-- Exact branch-selection theorem.  If the comparison source is an exactly uniform complete
batch, each of the two real branches is bounded by one ordinary source distinguisher. -/
theorem affineTargetAdvantage_le_two_sourceBranches
    {R Index Prefix : Type} [CommRing R] [Fintype R] [Fintype Index]
    [SampleableType (MessageBatch R Index)]
    (prefixSampler : ProbComp Prefix)
    (realSource : ProbComp (MessageBatch R Index))
    (alpha beta : Bool → Prefix → Index → R)
    (distinguisher : MessageBatch R Index → ProbComp Bool) :
    affineTargetAdvantage prefixSampler realSource alpha beta distinguisher ≤
      affineSourceAdvantage prefixSampler realSource ($ᵗ (MessageBatch R Index))
          alpha beta true distinguisher +
        affineSourceAdvantage prefixSampler realSource ($ᵗ (MessageBatch R Index))
          alpha beta false distinguisher := by
  let realTrue := affineBranchView prefixSampler realSource alpha beta true
  let realFalse := affineBranchView prefixSampler realSource alpha beta false
  let uniformTrue := affineBranchView prefixSampler ($ᵗ (MessageBatch R Index))
    alpha beta true
  let uniformFalse := affineBranchView prefixSampler ($ᵗ (MessageBatch R Index))
    alpha beta false
  have huniform : evalDist uniformTrue = evalDist uniformFalse := by
    exact affineBranchView_uniform_evalDist_eq prefixSampler alpha beta
  have hfirst := distinguishingAdvantage_triangle realTrue uniformTrue realFalse distinguisher
  have hsecond := distinguishingAdvantage_triangle uniformTrue uniformFalse realFalse distinguisher
  have hmiddle : distinguishingAdvantage uniformTrue uniformFalse distinguisher = 0 :=
    distinguishingAdvantage_eq_zero_of_evalDist_eq huniform distinguisher
  have hreverse :
      distinguishingAdvantage uniformFalse realFalse distinguisher =
        distinguishingAdvantage realFalse uniformFalse distinguisher :=
    distinguishingAdvantage_symm uniformFalse realFalse distinguisher
  unfold affineTargetAdvantage affineSourceAdvantage
  change distinguishingAdvantage realTrue realFalse distinguisher ≤
    distinguishingAdvantage realTrue uniformTrue distinguisher +
      distinguishingAdvantage realFalse uniformFalse distinguisher
  linarith

/-- Uniformly bounding the two ordinary source distinguishers gives the factor-two endpoint in
the manuscript. -/
theorem affineTargetAdvantage_le_two_mul_sourceBound
    {R Index Prefix : Type} [CommRing R] [Fintype R] [Fintype Index]
    [SampleableType (MessageBatch R Index)]
    (prefixSampler : ProbComp Prefix)
    (realSource : ProbComp (MessageBatch R Index))
    (alpha beta : Bool → Prefix → Index → R)
    (distinguisher : MessageBatch R Index → ProbComp Bool)
    (sourceBound : ℝ)
    (hsource : ∀ branch,
      affineSourceAdvantage prefixSampler realSource ($ᵗ (MessageBatch R Index))
        alpha beta branch distinguisher ≤ sourceBound) :
    affineTargetAdvantage prefixSampler realSource alpha beta distinguisher ≤
      2 * sourceBound := by
  have h := affineTargetAdvantage_le_two_sourceBranches
    prefixSampler realSource alpha beta distinguisher
  have htrue := hsource true
  have hfalse := hsource false
  linarith

/-! ## Public aggregation to scaled `S` and `S^2` -/

/-- Public linear aggregation of two-component ring rows. -/
def aggregateRows {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (rows : Index → MessageRow R) : MessageRow R :=
  (∑ index, basis index * (rows index).1,
    ∑ index, basis index * (rows index).2)

/-- Public negation of a row. -/
def negateRow {R : Type} [CommRing R] (row : MessageRow R) : MessageRow R :=
  (-row.1, -row.2)

@[simp]
theorem phase_negateRow {R : Type} [CommRing R]
    (secret : R) (row : MessageRow R) :
    phase secret (negateRow row) = -phase secret row := by
  rcases row with ⟨mask, body⟩
  simp only [phase, negateRow]
  ring

/-- Phase commutes with a public finite row aggregation. -/
theorem phase_aggregateRows {R Index : Type} [CommRing R] [Fintype Index]
    (secret : R) (basis : Index → R) (rows : Index → MessageRow R) :
    phase secret (aggregateRows basis rows) =
      ∑ index, basis index * phase secret (rows index) := by
  unfold phase aggregateRows
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Aggregating native body rows gives a scaled encryption of the embedded control secret. -/
theorem aggregateNativeBodyRows_phase
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret gadget : R) (basis masks errors : Index → R)
    (controlBits : Index → Bool) :
    phase secret
        (aggregateRows basis fun index ↦
          nativeBodyRow secret gadget (controlBits index) (masks index) (errors index)) =
      gadget * prefixEmbedding basis controlBits + aggregateError basis errors := by
  rw [phase_aggregateRows]
  simp_rw [nativeBodyRow_phase']
  unfold prefixEmbedding aggregateError
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- At a self-key control vector, the body aggregate encrypts `gadget*S`. -/
theorem aggregateNativeBodyRows_phase_linear
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret gadget : R) (basis masks errors : Index → R)
    (controlBits : Index → Bool)
    (hsecret : prefixEmbedding basis controlBits = secret) :
    phase secret
        (aggregateRows basis fun index ↦
          nativeBodyRow secret gadget (controlBits index) (masks index) (errors index)) =
      gadget * secret + aggregateError basis errors := by
  rw [aggregateNativeBodyRows_phase, hsecret]

/-- Aggregating native nonce rows gives the coefficient-product plaintext
`-gadget * E(controlBits) * S`. -/
theorem aggregateNativeNonceRows_phase
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret gadget : R) (basis masks errors : Index → R)
    (controlBits : Index → Bool) :
    phase secret
        (aggregateRows basis fun index ↦
          nativeNonceRow secret gadget (controlBits index) (masks index) (errors index)) =
      -(gadget * prefixEmbedding basis controlBits * secret) +
        aggregateError basis errors := by
  rw [phase_aggregateRows]
  simp_rw [nativeNonceRow_phase]
  unfold prefixEmbedding aggregateError
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ index, basis index * -(gadget * bitScalar (controlBits index) * secret)) =
        -(∑ index, gadget * (bitScalar (controlBits index) * basis index) * secret) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro index _
          ring
    _ = -(gadget * (∑ index, bitScalar (controlBits index) * basis index) * secret) := by
          rw [Finset.mul_sum, Finset.sum_mul]

/-- Negating the public nonce aggregate at a self-key control vector gives a scaled encryption
of `S^2` with the exactly negated aggregate error. -/
theorem aggregateNegativeNativeNonceRows_phase_square
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret gadget : R) (basis masks errors : Index → R)
    (controlBits : Index → Bool)
    (hsecret : prefixEmbedding basis controlBits = secret) :
    phase secret
        (negateRow (aggregateRows basis fun index ↦
          nativeNonceRow secret gadget (controlBits index) (masks index) (errors index))) =
      gadget * secret ^ 2 - aggregateError basis errors := by
  rw [phase_negateRow, aggregateNativeNonceRows_phase, hsecret]
  ring

/-! ## Coefficient-product correlation experiments -/

/-- Complete coefficient-product experiment interface.

`productView encryptionSecret controlSecret` is intended to contain all native body/nonce rows
whose encryption key is the first secret and whose control coefficients come from the second.
The carrier `View` is deliberately unrestricted so that the prescribed auxiliary interface is
part of the same experiment. -/
structure CoefficientProductExperiment (Secret View : Type) where
  secretSampler : ProbComp Secret
  productView : Secret → Secret → ProbComp View
  zeroView : Secret → ProbComp View

namespace CoefficientProductExperiment

variable {Secret View : Type}

/-- Honest self-key complete view. -/
def selfSampler (experiment : CoefficientProductExperiment Secret View) : ProbComp View := do
  let secret ← experiment.secretSampler
  experiment.productView secret secret

/-- The control vector is sampled independently while the encryption key remains the first
secret. -/
def independentSampler
    (experiment : CoefficientProductExperiment Secret View) : ProbComp View := do
  let encryptionSecret ← experiment.secretSampler
  let controlSecret ← experiment.secretSampler
  experiment.productView encryptionSecret controlSecret

/-- Zero-message complete view under the same encryption-key law. -/
def zeroSampler (experiment : CoefficientProductExperiment Secret View) : ProbComp View := do
  let secret ← experiment.secretSampler
  experiment.zeroView secret

/-- Minimal circular coefficient-product correlation advantage. -/
def correlationAdvantage (experiment : CoefficientProductExperiment Secret View)
    (distinguisher : Distinguisher View) : ℝ :=
  distinguishingAdvantage experiment.selfSampler experiment.independentSampler distinguisher

/-- Standard independent-message-to-zero endpoint. -/
def independentZeroAdvantage (experiment : CoefficientProductExperiment Secret View)
    (distinguisher : Distinguisher View) : ℝ :=
  distinguishingAdvantage experiment.independentSampler experiment.zeroSampler distinguisher

/-- Direct native complete-view one-circular advantage. -/
def oneCircularAdvantage (experiment : CoefficientProductExperiment Secret View)
    (distinguisher : Distinguisher View) : ℝ :=
  distinguishingAdvantage experiment.selfSampler experiment.zeroSampler distinguisher

/-- The direct native one-circular game factors through the independent-control experiment. -/
theorem oneCircularAdvantage_le_correlation_add_independentZero
    (experiment : CoefficientProductExperiment Secret View)
    (distinguisher : Distinguisher View) :
    experiment.oneCircularAdvantage distinguisher ≤
      experiment.correlationAdvantage distinguisher +
        experiment.independentZeroAdvantage distinguisher := by
  exact distinguishingAdvantage_triangle experiment.selfSampler
    experiment.independentSampler experiment.zeroSampler distinguisher

/-- Named coefficient-product correlation assumption against a selected adversary class. -/
def CorrelationHardAgainst
    (experiment : CoefficientProductExperiment Secret View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    experiment.correlationAdvantage distinguisher ≤ bound

/-- Named independent-message standard endpoint. -/
def IndependentZeroHardAgainst
    (experiment : CoefficientProductExperiment Secret View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    experiment.independentZeroAdvantage distinguisher ≤ bound

/-- Direct complete-view native one-circularity. -/
def OneCircularHardAgainst
    (experiment : CoefficientProductExperiment Secret View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    experiment.oneCircularAdvantage distinguisher ≤ bound

/-- The minimal correlation assumption plus the standard endpoint imply direct native
one-circularity. -/
theorem oneCircularHardAgainst_of_correlation_and_independentZero
    (experiment : CoefficientProductExperiment Secret View)
    (allowed : Distinguisher View → Prop)
    (correlationBound endpointBound : ℝ)
    (hcorrelation : experiment.CorrelationHardAgainst allowed correlationBound)
    (hendpoint : experiment.IndependentZeroHardAgainst allowed endpointBound) :
    experiment.OneCircularHardAgainst allowed (correlationBound + endpointBound) := by
  intro distinguisher hallowed
  exact (experiment.oneCircularAdvantage_le_correlation_add_independentZero
    distinguisher).trans (add_le_add
      (hcorrelation distinguisher hallowed) (hendpoint distinguisher hallowed))

/-- Manuscript bound (7.8): the correlation term is charged once and the complete-batch source
uses one branch-selection factor, with layout and auxiliary defects explicit. -/
theorem oneCircularAdvantage_le_minimalCorrelation
    (experiment : CoefficientProductExperiment Secret View)
    (distinguisher : Distinguisher View)
    (correlationBound zeroRowBound layoutDefect auxiliaryDefect : ℝ)
    (hcorrelation : experiment.correlationAdvantage distinguisher ≤ correlationBound)
    (hendpoint : experiment.independentZeroAdvantage distinguisher ≤
      2 * zeroRowBound + layoutDefect + auxiliaryDefect) :
    experiment.oneCircularAdvantage distinguisher ≤
      correlationBound + 2 * zeroRowBound + layoutDefect + auxiliaryDefect := by
  have h := experiment.oneCircularAdvantage_le_correlation_add_independentZero distinguisher
  linarith

end CoefficientProductExperiment

/-! ## Square-correlation experiments and public projection -/

/-- Complete scaled-square experiment interface.

`squareView encryptionSecret multiplierSecret` is intended to encrypt the fixed public scale
vector times `encryptionSecret * multiplierSecret`. -/
structure SquareExperiment (Secret View : Type) where
  secretSampler : ProbComp Secret
  squareView : Secret → Secret → ProbComp View
  zeroView : Secret → ProbComp View

namespace SquareExperiment

variable {Secret View : Type}

def selfSampler (experiment : SquareExperiment Secret View) : ProbComp View := do
  let secret ← experiment.secretSampler
  experiment.squareView secret secret

def independentSampler (experiment : SquareExperiment Secret View) : ProbComp View := do
  let encryptionSecret ← experiment.secretSampler
  let multiplierSecret ← experiment.secretSampler
  experiment.squareView encryptionSecret multiplierSecret

def zeroSampler (experiment : SquareExperiment Secret View) : ProbComp View := do
  let secret ← experiment.secretSampler
  experiment.zeroView secret

/-- Scaled `S^2` versus scaled `S*S'` correlation advantage. -/
def correlationAdvantage (experiment : SquareExperiment Secret View)
    (distinguisher : Distinguisher View) : ℝ :=
  distinguishingAdvantage experiment.selfSampler experiment.independentSampler distinguisher

/-- Independent product versus homogeneous zero rows. -/
def independentZeroAdvantage (experiment : SquareExperiment Secret View)
    (distinguisher : Distinguisher View) : ℝ :=
  distinguishingAdvantage experiment.independentSampler experiment.zeroSampler distinguisher

/-- Direct scaled square-circular advantage. -/
def circularAdvantage (experiment : SquareExperiment Secret View)
    (distinguisher : Distinguisher View) : ℝ :=
  distinguishingAdvantage experiment.selfSampler experiment.zeroSampler distinguisher

theorem circularAdvantage_le_correlation_add_independentZero
    (experiment : SquareExperiment Secret View)
    (distinguisher : Distinguisher View) :
    experiment.circularAdvantage distinguisher ≤
      experiment.correlationAdvantage distinguisher +
        experiment.independentZeroAdvantage distinguisher := by
  exact distinguishingAdvantage_triangle experiment.selfSampler
    experiment.independentSampler experiment.zeroSampler distinguisher

def CorrelationHardAgainst (experiment : SquareExperiment Secret View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    experiment.correlationAdvantage distinguisher ≤ bound

def IndependentZeroHardAgainst (experiment : SquareExperiment Secret View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    experiment.independentZeroAdvantage distinguisher ≤ bound

def CircularHardAgainst (experiment : SquareExperiment Secret View)
    (allowed : Distinguisher View → Prop) (bound : ℝ) : Prop :=
  ∀ distinguisher, allowed distinguisher →
    experiment.circularAdvantage distinguisher ≤ bound

theorem circularHardAgainst_of_correlation_and_independentZero
    (experiment : SquareExperiment Secret View)
    (allowed : Distinguisher View → Prop)
    (correlationBound endpointBound : ℝ)
    (hcorrelation : experiment.CorrelationHardAgainst allowed correlationBound)
    (hendpoint : experiment.IndependentZeroHardAgainst allowed endpointBound) :
    experiment.CircularHardAgainst allowed (correlationBound + endpointBound) := by
  intro distinguisher hallowed
  exact (experiment.circularAdvantage_le_correlation_add_independentZero
    distinguisher).trans (add_le_add
      (hcorrelation distinguisher hallowed) (hendpoint distinguisher hallowed))

/-- Manuscript bound (8.9). -/
theorem circularAdvantage_le_squareCorrelation
    (experiment : SquareExperiment Secret View)
    (distinguisher : Distinguisher View)
    (correlationBound zeroRowBound auxiliaryDefect : ℝ)
    (hcorrelation : experiment.correlationAdvantage distinguisher ≤ correlationBound)
    (hendpoint : experiment.independentZeroAdvantage distinguisher ≤
      2 * zeroRowBound + auxiliaryDefect) :
    experiment.circularAdvantage distinguisher ≤
      correlationBound + 2 * zeroRowBound + auxiliaryDefect := by
  have h := experiment.circularAdvantage_le_correlation_add_independentZero distinguisher
  linarith

/-- Deterministically project a coefficient-product experiment to a square-view carrier. -/
def ofCoefficientProjection {ProductView SquareView : Type}
    (experiment : CoefficientProductExperiment Secret ProductView)
    (project : ProductView → SquareView) : SquareExperiment Secret SquareView where
  secretSampler := experiment.secretSampler
  squareView encryptionSecret multiplierSecret :=
    project <$> experiment.productView encryptionSecret multiplierSecret
  zeroView secret := project <$> experiment.zeroView secret

/-- The projected square-correlation advantage is exactly the coefficient-product advantage of
the lifted distinguisher.  This is the finite data-processing implication `CPCorr => SqCorr`. -/
theorem ofCoefficientProjection_correlationAdvantage_eq
    {ProductView SquareView : Type}
    (experiment : CoefficientProductExperiment Secret ProductView)
    (project : ProductView → SquareView)
    (distinguisher : Distinguisher SquareView) :
    (ofCoefficientProjection experiment project).correlationAdvantage distinguisher =
      experiment.correlationAdvantage (fun view ↦ distinguisher (project view)) := by
  simp only [correlationAdvantage, CoefficientProductExperiment.correlationAdvantage,
    distinguishingAdvantage, selfSampler, independentSampler,
    CoefficientProductExperiment.selfSampler,
    CoefficientProductExperiment.independentSampler, ofCoefficientProjection,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, monad_norm]

/-- Hardness transfers forward through an allowed public aggregation. -/
theorem correlationHardAgainst_of_coefficientProjection
    {ProductView SquareView : Type}
    (experiment : CoefficientProductExperiment Secret ProductView)
    (project : ProductView → SquareView)
    (productAllowed : Distinguisher ProductView → Prop)
    (squareAllowed : Distinguisher SquareView → Prop)
    (bound : ℝ)
    (hproduct : experiment.CorrelationHardAgainst productAllowed bound)
    (hlift : ∀ distinguisher, squareAllowed distinguisher →
      productAllowed (fun view ↦ distinguisher (project view))) :
    (ofCoefficientProjection experiment project).CorrelationHardAgainst squareAllowed bound := by
  intro distinguisher hallowed
  rw [ofCoefficientProjection_correlationAdvantage_eq]
  exact hproduct _ (hlift distinguisher hallowed)

end SquareExperiment

/-! ## End-to-end game compositions -/

/-- Direct one-circular formulation (9.1), stated on the literal complete games. -/
theorem directOneCircularSecurity_le
    {Secret View : Type}
    (experiment : CoefficientProductExperiment Secret View)
    (actual ideal : ProbComp View) (distinguisher : Distinguisher View)
    (oneCircularBound zeroEndpointBound samplerDefect : ℝ)
    (hsampler : distinguishingAdvantage actual experiment.selfSampler distinguisher ≤
      samplerDefect)
    (hcircular : experiment.oneCircularAdvantage distinguisher ≤ oneCircularBound)
    (hzero : distinguishingAdvantage experiment.zeroSampler ideal distinguisher ≤
      zeroEndpointBound) :
    distinguishingAdvantage actual ideal distinguisher ≤
      oneCircularBound + zeroEndpointBound + samplerDefect := by
  unfold CoefficientProductExperiment.oneCircularAdvantage at hcircular
  have hfirst := distinguishingAdvantage_triangle actual experiment.selfSampler ideal distinguisher
  have hsecond := distinguishingAdvantage_triangle experiment.selfSampler
    experiment.zeroSampler ideal distinguisher
  linarith

/-- Minimal coefficient-correlation formulation (9.2), with the complete-batch branch-selection,
layout, auxiliary, endpoint, and sampler terms each appearing once. -/
theorem minimalCorrelationSecurity_le
    {Secret View : Type}
    (experiment : CoefficientProductExperiment Secret View)
    (actual ideal : ProbComp View) (distinguisher : Distinguisher View)
    (correlationBound zeroRowBound zeroEndpointBound layoutDefect auxiliaryDefect
      samplerDefect : ℝ)
    (hsampler : distinguishingAdvantage actual experiment.selfSampler distinguisher ≤
      samplerDefect)
    (hcorrelation : experiment.correlationAdvantage distinguisher ≤ correlationBound)
    (hindependentZero : experiment.independentZeroAdvantage distinguisher ≤
      2 * zeroRowBound + layoutDefect + auxiliaryDefect)
    (hzero : distinguishingAdvantage experiment.zeroSampler ideal distinguisher ≤
      zeroEndpointBound) :
    distinguishingAdvantage actual ideal distinguisher ≤
      correlationBound + 2 * zeroRowBound + zeroEndpointBound + layoutDefect +
        auxiliaryDefect + samplerDefect := by
  unfold CoefficientProductExperiment.correlationAdvantage at hcorrelation
  unfold CoefficientProductExperiment.independentZeroAdvantage at hindependentZero
  have hone := distinguishingAdvantage_triangle actual experiment.selfSampler ideal distinguisher
  have htwo := distinguishingAdvantage_triangle experiment.selfSampler
    experiment.independentSampler ideal distinguisher
  have hthree := distinguishingAdvantage_triangle experiment.independentSampler
    experiment.zeroSampler ideal distinguisher
  linarith

/-- Modified square-key theorem (9.4).  `evaluationDefect` is the separately supplied coupling
or functionality defect of the modified evaluator. -/
theorem squareKeySecurity_le
    {Secret View : Type}
    (experiment : SquareExperiment Secret View)
    (actual ideal : ProbComp View) (distinguisher : Distinguisher View)
    (correlationBound zeroRowBound zeroEndpointBound evaluationDefect auxiliaryDefect
      samplerDefect : ℝ)
    (hfidelity : distinguishingAdvantage actual experiment.selfSampler distinguisher ≤
      evaluationDefect + samplerDefect)
    (hcorrelation : experiment.correlationAdvantage distinguisher ≤ correlationBound)
    (hindependentZero : experiment.independentZeroAdvantage distinguisher ≤
      2 * zeroRowBound + auxiliaryDefect)
    (hzero : distinguishingAdvantage experiment.zeroSampler ideal distinguisher ≤
      zeroEndpointBound) :
    distinguishingAdvantage actual ideal distinguisher ≤
      correlationBound + 2 * zeroRowBound + zeroEndpointBound + evaluationDefect +
        auxiliaryDefect + samplerDefect := by
  unfold SquareExperiment.correlationAdvantage at hcorrelation
  unfold SquareExperiment.independentZeroAdvantage at hindependentZero
  have hone := distinguishingAdvantage_triangle actual experiment.selfSampler ideal distinguisher
  have htwo := distinguishingAdvantage_triangle experiment.selfSampler
    experiment.independentSampler ideal distinguisher
  have hthree := distinguishingAdvantage_triangle experiment.independentSampler
    experiment.zeroSampler ideal distinguisher
  linarith

end

end FormalProof4FHE.TFHE.CircularSecurityMinimalAssumption
