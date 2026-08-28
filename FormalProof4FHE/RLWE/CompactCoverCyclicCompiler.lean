/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CompactCoverTechnical

/-!
# Cyclic affine compiler for compact cover frontiers

This module formalizes the central construction of `sketch/proof-compact-cover.md`: arbitrary
cross-frontier affine messages and the final cyclic return are compiled from fresh ordinary
Binary-NTT RLWE rows sharing one embedded witness.
-/

open OracleComp BigOperators

namespace FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverCyclicCompiler

noncomputable section

/-! ## Admissible frontier maps -/

/-- A ring map between two frontier rings that is linear over the common embedded base secret. -/
structure AdmissibleMap (Base Source Target : Type)
    [CommRing Base] [CommRing Source] [CommRing Target] where
  sourceEmbedding : Base →+* Source
  targetEmbedding : Base →+* Target
  map : Source →+* Target
  covariance : ∀ value scalar,
    map (value * sourceEmbedding scalar) = map value * targetEmbedding scalar

/-- Admissible maps carry an affine hidden-witness decomposition into the target frontier. -/
theorem AdmissibleMap.map_sub_mul_embedding
    {Base Source Target : Type}
    [CommRing Base] [CommRing Source] [CommRing Target]
    (transition : AdmissibleMap Base Source Target)
    (constant coefficient : Source) (witness : Base) :
    transition.map
        (constant - coefficient * transition.sourceEmbedding witness) =
      transition.map constant -
        transition.map coefficient * transition.targetEmbedding witness := by
  rw [map_sub, transition.covariance]

/-- Concrete partial-cover relabeling `y <- kappa(y)` with automorphism
`y*kappa(y)^-1`. -/
def frontierRelabel
    {SourceLabel TargetLabel GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (sourceName : SourceLabel → GroupIndex)
    (targetName : TargetLabel → GroupIndex)
    (kappa : TargetLabel → SourceLabel) :
    CompactCoverTechnical.PartialCover SourceLabel R →+*
      CompactCoverTechnical.PartialCover TargetLabel R where
  toFun := CompactCoverTechnical.relabel action kappa
    (fun target => targetName target * (sourceName (kappa target))⁻¹)
  map_one' := by funext target; simp [CompactCoverTechnical.relabel]
  map_mul' left right := CompactCoverTechnical.relabel_mul action kappa _ left right
  map_zero' := by funext target; simp [CompactCoverTechnical.relabel]
  map_add' left right := CompactCoverTechnical.relabel_add action kappa _ left right

/-- Concrete relabeling sends the restricted source witness to the restricted target witness. -/
theorem frontierRelabel_fixedEmbedding
    {SourceLabel TargetLabel GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (sourceName : SourceLabel → GroupIndex)
    (targetName : TargetLabel → GroupIndex)
    (kappa : TargetLabel → SourceLabel) (witness : R) :
    frontierRelabel action sourceName targetName kappa
        (CompactCoverTechnical.restrictedFixedEmbedding action sourceName witness) =
      CompactCoverTechnical.restrictedFixedEmbedding action targetName witness := by
  funext target
  change action (targetName target * (sourceName (kappa target))⁻¹)
      (action (sourceName (kappa target)) witness) =
    action (targetName target) witness
  change (action (targetName target * (sourceName (kappa target))⁻¹) *
      action (sourceName (kappa target))) witness = _
  rw [← action.map_mul]
  simp

/-- The concrete relabeling is admissible for the common base witness. -/
def frontierRelabelAdmissible
    {SourceLabel TargetLabel GroupIndex R : Type}
    [Group GroupIndex] [CommRing R]
    (action : GroupIndex →* R ≃+* R)
    (sourceName : SourceLabel → GroupIndex)
    (targetName : TargetLabel → GroupIndex)
    (kappa : TargetLabel → SourceLabel) :
    AdmissibleMap R (CompactCoverTechnical.PartialCover SourceLabel R)
      (CompactCoverTechnical.PartialCover TargetLabel R) where
  sourceEmbedding :=
    { toFun := CompactCoverTechnical.restrictedFixedEmbedding action sourceName
      map_one' := by funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding]
      map_mul' := by intros; funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding]
      map_zero' := by funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding]
      map_add' := by intros; funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding] }
  targetEmbedding :=
    { toFun := CompactCoverTechnical.restrictedFixedEmbedding action targetName
      map_one' := by funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding]
      map_mul' := by intros; funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding]
      map_zero' := by funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding]
      map_add' := by intros; funext index; simp [CompactCoverTechnical.restrictedFixedEmbedding] }
  map := frontierRelabel action sourceName targetName kappa
  covariance value scalar := by
    change frontierRelabel action sourceName targetName kappa
        (value * CompactCoverTechnical.restrictedFixedEmbedding
          action sourceName scalar) =
      frontierRelabel action sourceName targetName kappa value *
        CompactCoverTechnical.restrictedFixedEmbedding action targetName scalar
    rw [map_mul, frontierRelabel_fixedEmbedding]

/-! ## Affine witness normal form -/

/-- A value represented as `constant - coefficient*witnessEmbedding`. -/
structure WitnessAffine (R : Type) [CommRing R] where
  constant : R
  coefficient : R

def WitnessAffine.value {R : Type} [CommRing R]
    (form : WitnessAffine R) (embeddedWitness : R) : R :=
  form.constant - form.coefficient * embeddedWitness

/-- Public linear combinations of witness-affine values remain witness-affine. -/
def affineCombination {Index R : Type} [Fintype Index] [CommRing R]
    (weights : Index → R) (forms : Index → WitnessAffine R) : WitnessAffine R where
  constant := ∑ index, weights index * (forms index).constant
  coefficient := ∑ index, weights index * (forms index).coefficient

theorem affineCombination_value {Index R : Type}
    [Fintype Index] [CommRing R]
    (weights : Index → R) (forms : Index → WitnessAffine R)
    (embeddedWitness : R) :
    (affineCombination weights forms).value embeddedWitness =
      ∑ index, weights index * (forms index).value embeddedWitness := by
  simp only [affineCombination, WitnessAffine.value]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul]
  apply congrArg (fun value =>
    (∑ index, weights index * (forms index).constant) - value)
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Mapping a source affine form through an admissible frontier map gives a target affine form. -/
def mapWitnessAffine
    {Base Source Target : Type}
    [CommRing Base] [CommRing Source] [CommRing Target]
    (transition : AdmissibleMap Base Source Target)
    (form : WitnessAffine Source) : WitnessAffine Target where
  constant := transition.map form.constant
  coefficient := transition.map form.coefficient

theorem mapWitnessAffine_value
    {Base Source Target : Type}
    [CommRing Base] [CommRing Source] [CommRing Target]
    (transition : AdmissibleMap Base Source Target)
    (form : WitnessAffine Source) (witness : Base) :
    (mapWitnessAffine transition form).value
        (transition.targetEmbedding witness) =
      transition.map
        (form.value (transition.sourceEmbedding witness)) := by
  exact (transition.map_sub_mul_embedding form.constant form.coefficient witness).symm

/-! ## Exact cyclic compiler -/

/-- Target secret `d - P*I`, with `P` a unit. -/
def targetSecret {R : Type} [CommRing R]
    (pivot : Rˣ) (offset invariantWitness : R) : R :=
  offset - (pivot : R) * invariantWitness

/-- Compiler mask for one arbitrary target witness-affine message. -/
def compilerMask {R : Type} [CommRing R]
    (targetPivot : Rˣ) (messageCoefficient sourceMask : R) : R :=
  -(sourceMask + messageCoefficient) * ↑(targetPivot⁻¹)

/-- Compiler body. -/
def compilerBody {R : Type} [CommRing R]
    (targetOffset messageConstant publicConstant sourceBody targetMask : R) : R :=
  sourceBody + targetMask * targetOffset + publicConstant + messageConstant

/-- **Cyclic multi-frontier affine compiler identity.** -/
theorem compiler_phase
    {R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset invariantWitness error : R)
    (message : WitnessAffine R) (publicConstant sourceMask : R) :
    let sourceBody := sourceMask * invariantWitness + error
    let targetMask := compilerMask targetPivot message.coefficient sourceMask
    compilerBody targetOffset message.constant publicConstant sourceBody targetMask -
        targetMask * targetSecret targetPivot targetOffset invariantWitness =
      error + publicConstant + message.value invariantWitness := by
  dsimp only
  have hunit : (↑(targetPivot⁻¹) : R) * targetPivot = 1 := by simp
  simp only [compilerMask, compilerBody, targetSecret, WitnessAffine.value]
  ring_nf
  rw [mul_assoc (sourceMask * invariantWitness), hunit,
    mul_assoc (invariantWitness * message.coefficient), hunit]
  ring

/-- Complete public row map used by the compiler. -/
def compilerRow {R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : WitnessAffine R) (publicConstant : R)
    (source : R × R) : R × R :=
  let targetMask := compilerMask targetPivot message.coefficient source.1
  (targetMask,
    compilerBody targetOffset message.constant publicConstant source.2 targetMask)

def compilerRowInv {R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : WitnessAffine R) (publicConstant : R)
    (target : R × R) : R × R :=
  (-target.1 * targetPivot - message.coefficient,
    target.2 - target.1 * targetOffset - publicConstant - message.constant)

@[simp]
theorem compilerRowInv_compilerRow {R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : WitnessAffine R) (publicConstant : R) (source : R × R) :
    compilerRowInv targetPivot targetOffset message publicConstant
      (compilerRow targetPivot targetOffset message publicConstant source) = source := by
  rcases source with ⟨mask, body⟩
  simp [compilerRowInv, compilerRow, compilerMask, compilerBody]
  ring

@[simp]
theorem compilerRow_compilerRowInv {R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : WitnessAffine R) (publicConstant : R) (target : R × R) :
    compilerRow targetPivot targetOffset message publicConstant
      (compilerRowInv targetPivot targetOffset message publicConstant target) = target := by
  rcases target with ⟨mask, body⟩
  simp [compilerRowInv, compilerRow, compilerMask, compilerBody]
  ring

theorem compilerRow_bijective {R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : WitnessAffine R) (publicConstant : R) :
    Function.Bijective
      (compilerRow targetPivot targetOffset message publicConstant) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨compilerRowInv targetPivot targetOffset message publicConstant,
      compilerRowInv_compilerRow targetPivot targetOffset message publicConstant,
      compilerRow_compilerRowInv targetPivot targetOffset message publicConstant⟩

/-- One compiler row preserves the exact uniform source endpoint. -/
theorem compilerRow_uniform_evalDist {R : Type} [CommRing R]
    [Fintype R] [SampleableType R] [SampleableType (R × R)]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : WitnessAffine R) (publicConstant : R) :
    evalDist (compilerRow targetPivot targetOffset message publicConstant <$>
        ($ᵗ (R × R))) = evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R)
    (compilerRow targetPivot targetOffset message publicConstant)
    (compilerRow_bijective targetPivot targetOffset message publicConstant)

/-- Complete row-family compiler. -/
def compilerBatch {Row R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : Row → WitnessAffine R) (publicConstant : Row → R)
    (source : Row → R × R) : Row → R × R :=
  fun row => compilerRow targetPivot targetOffset (message row)
    (publicConstant row) (source row)

def compilerBatchInv {Row R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : Row → WitnessAffine R) (publicConstant : Row → R)
    (target : Row → R × R) : Row → R × R :=
  fun row => compilerRowInv targetPivot targetOffset (message row)
    (publicConstant row) (target row)

theorem compilerBatch_bijective {Row R : Type} [CommRing R]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : Row → WitnessAffine R) (publicConstant : Row → R) :
    Function.Bijective
      (compilerBatch targetPivot targetOffset message publicConstant) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨compilerBatchInv targetPivot targetOffset message publicConstant, ?_, ?_⟩
  · intro source
    funext row
    simp [compilerBatch, compilerBatchInv]
  · intro target
    funext row
    simp [compilerBatch, compilerBatchInv]

theorem compilerBatch_uniform_evalDist {Row R : Type}
    [Finite Row] [DecidableEq Row]
    [CommRing R] [Fintype R] [SampleableType R]
    [SampleableType (Row → R × R)]
    (targetPivot : Rˣ) (targetOffset : R)
    (message : Row → WitnessAffine R) (publicConstant : Row → R) :
    evalDist (compilerBatch targetPivot targetOffset message publicConstant <$>
        ($ᵗ (Row → R × R))) =
      evalDist ($ᵗ (Row → R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := Row → R × R) (β := Row → R × R)
    (compilerBatch targetPivot targetOffset message publicConstant)
    (compilerBatch_bijective targetPivot targetOffset message publicConstant)

/-! ## Exact gadget transition -/

def transitionCiphertext {SourceIndex Digit Source Target : Type}
    [Fintype SourceIndex] [Fintype Digit] [CommRing Source] [CommRing Target]
    (rhoBody : SourceIndex → Source → Target)
    (weights : SourceIndex → Target)
    (digits : SourceIndex → Digit → Target)
    (keys : SourceIndex → Digit → Target × Target)
    (publicConstant : Target)
    (ciphertexts : SourceIndex → Source × Source) : Target × Target :=
  (-∑ source, ∑ digit, digits source digit * (keys source digit).1,
    publicConstant +
      ∑ source, weights source * rhoBody source (ciphertexts source).2 -
        ∑ source, ∑ digit, digits source digit * (keys source digit).2)

/-- Exact phase of an aligned multi-source gadget transition. -/
theorem transitionCiphertext_phase
    {SourceIndex Digit Source Target : Type}
    [Fintype SourceIndex] [Fintype Digit] [CommRing Source] [CommRing Target]
    (rho : SourceIndex → Source →+* Target)
    (weights : SourceIndex → Target)
    (digits : SourceIndex → Digit → Target)
    (gadget : Digit → Target)
    (keys : SourceIndex → Digit → Target × Target)
    (sourceSecret : SourceIndex → Source) (targetSecret : Target)
    (errors : SourceIndex → Digit → Target)
    (publicConstant : Target)
    (ciphertexts : SourceIndex → Source × Source)
    (hdecompose : ∀ source,
      weights source * rho source (ciphertexts source).1 =
        ∑ digit, digits source digit * gadget digit)
    (hkeys : ∀ source digit,
      (keys source digit).2 - (keys source digit).1 * targetSecret =
        gadget digit * rho source (sourceSecret source) + errors source digit) :
    (transitionCiphertext (fun source => rho source) weights digits keys
        publicConstant ciphertexts).2 -
      (transitionCiphertext (fun source => rho source) weights digits keys
        publicConstant ciphertexts).1 * targetSecret =
      publicConstant +
        ∑ source, weights source *
          rho source ((ciphertexts source).2 -
            (ciphertexts source).1 * sourceSecret source) -
        ∑ source, ∑ digit, digits source digit * errors source digit := by
  simp only [transitionCiphertext, neg_mul, sub_neg_eq_add]
  have hkeyBody (source : SourceIndex) (digit : Digit) :
      (keys source digit).2 = (keys source digit).1 * targetSecret +
        (gadget digit * rho source (sourceSecret source) + errors source digit) := by
    calc
      (keys source digit).2 = (keys source digit).1 * targetSecret +
          ((keys source digit).2 - (keys source digit).1 * targetSecret) := by abel
      _ = _ := by rw [hkeys]
  have hsourceSum :
      (∑ source, weights source *
        rho source ((ciphertexts source).2 -
          (ciphertexts source).1 * sourceSecret source)) =
        (∑ source, weights source * rho source (ciphertexts source).2) -
          ∑ source, weights source * rho source (ciphertexts source).1 *
            rho source (sourceSecret source) := by
    simp_rw [map_sub, map_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    apply congrArg (fun value =>
      (∑ source, weights source * rho source (ciphertexts source).2) - value)
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [hsourceSum]
  have hmask :
      (∑ source, ∑ digit,
        digits source digit * ((keys source digit).1 * targetSecret)) =
        (∑ source, ∑ digit,
          digits source digit * (keys source digit).1) * targetSecret := by
    calc
      _ = ∑ source, ∑ digit,
          (digits source digit * (keys source digit).1) * targetSecret := by
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro digit _
        ring
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro source _
        rw [Finset.sum_mul]
  have hgadget (source : SourceIndex) :
      (∑ digit, digits source digit *
        (gadget digit * rho source (sourceSecret source))) =
        weights source * rho source (ciphertexts source).1 *
          rho source (sourceSecret source) := by
    calc
      _ = ∑ digit, (digits source digit * gadget digit) *
          rho source (sourceSecret source) := by
        apply Finset.sum_congr rfl
        intro digit _
        ring
      _ = (∑ digit, digits source digit * gadget digit) *
          rho source (sourceSecret source) := by rw [Finset.sum_mul]
      _ = _ := by rw [← hdecompose source]
  have hkeySum :
      (∑ source, ∑ digit, digits source digit * (keys source digit).2) =
        (∑ source, ∑ digit,
          digits source digit * ((keys source digit).1 * targetSecret)) +
        (∑ source, ∑ digit,
          digits source digit *
            (gadget digit * rho source (sourceSecret source))) +
        ∑ source, ∑ digit, digits source digit * errors source digit := by
    simp_rw [hkeyBody, mul_add, Finset.sum_add_distrib]
    ring
  rw [hkeySum, hmask]
  simp_rw [hgadget]
  ring_nf

/-! ## Joint reduction accounting -/

/-- Finite advantage accounting for one joint reduction that outputs a fair bit on any frontier
pivot failure. -/
structure JointReductionCertificate where
  targetAdvantage : ℝ
  sourceAdvantage : ℝ
  pivotFailureBound : ℝ
  target_nonneg : 0 ≤ targetAdvantage
  target_le_one : targetAdvantage ≤ 1
  source_nonneg : 0 ≤ sourceAdvantage
  failure_nonneg : 0 ≤ pivotFailureBound
  failure_le_one : pivotFailureBound ≤ 1
  retained_gap :
    (1 - pivotFailureBound) * targetAdvantage ≤ sourceAdvantage

/-- The additive form used in the manuscript: the target gap is at most the ordinary-source gap
plus the union bound on pivot failure. -/
theorem JointReductionCertificate.target_le_source_add_failure
    (certificate : JointReductionCertificate) :
    certificate.targetAdvantage ≤
      certificate.sourceAdvantage + certificate.pivotFailureBound := by
  nlinarith [certificate.retained_gap,
    mul_le_mul_of_nonneg_left certificate.target_le_one
      certificate.failure_nonneg]

/-- Adding an explicit public-key masking hybrid gives the final IND-CPA arithmetic. -/
theorem indCpa_le_source_add_failure_add_masking
    (indCpaAdvantage maskingDistance : ℝ)
    (certificate : JointReductionCertificate)
    (hhybrid : indCpaAdvantage ≤
      certificate.targetAdvantage + maskingDistance) :
    indCpaAdvantage ≤ certificate.sourceAdvantage +
      certificate.pivotFailureBound + maskingDistance := by
  linarith [certificate.target_le_source_add_failure]

end

end FormalProof4FHE.RLWE.BinaryNTTSecurity.CompactCoverCyclicCompiler
