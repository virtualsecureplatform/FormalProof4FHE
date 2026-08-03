/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BlockBinarySelfCircular
import FormalProof4FHE.TFHE.NativeTRGSWAggregateProjectedLeakage
import FormalProof4FHE.TFHE.NativeTRGSWHashCompressedSecurity
import FormalProof4FHE.TFHE.RGSWCoefficientCircularSecurity
import FormalProof4FHE.TFHE.RotationLookup
import Mathlib.Data.Fintype.Perm

/-!
# Block-categorical self-circular native TFHE

This file formalizes the finite and reduction-theoretic content of
`block_categorical_self_circular_tfhe.tex`.  A block of length `ell` has `ell + 1`
categories: zero or one selected coordinate.  Completing the BRK with one ciphertext for every
category makes a category permutation a literal reindexing, rather than ciphertext arithmetic.

The main checked facts are:

* exact equivariance of the completed one-hot plaintext table and preservation of a uniform
  complete carrier under public relabeling;
* the exact wrong-candidate kernel
  `lambda * I + (1 - lambda) * J`, where `lambda = 1 / (L - 1)^2`;
* the multicategory prediction coefficient `(L - 1)^2 / (L - 2)`, its block telescope, and the
  contextual squared-bias composition with loss `sqrt (2 * L * epsilon)`;
* the resulting real-to-ideal polynomial-loss theorem, including the independent-message and
  correlated-zero endpoints exactly once;
* the full-key `L^k` baseline, the corrected translation-interface leakage lower bound, and a
  concrete positive-gap/zero-source oracle counterexample to a generic black-box implication.

The native contextual-source constructor is deliberately not postulated here.  Its advantage,
the CVZR transition, the complete-batch zero endpoint, and finite representation/sampler defects
remain hypotheses of the final theorem.  This is the cryptographic research boundary isolated by
the manuscript.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.BlockCategoricalSelfCircular

noncomputable section

open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWHashCompressedSecurity
open RGSWCoefficientCircularSecurity

/-! ## Block categories and the full-key baseline -/

/-- The zero category followed by the `ell` one-hot categories. -/
abbrev Category (ell : ℕ) := Fin (ell + 1)

/-- A block-categorical key is exactly the compact block-binary key. -/
abbrev Key (ell blockCount : ℕ) := Fin blockCount → Category ell

@[simp]
theorem card_category (ell : ℕ) : Fintype.card (Category ell) = ell + 1 := by
  simp [Category]

@[simp]
theorem card_key (ell blockCount : ℕ) :
    Fintype.card (Key ell blockCount) = (ell + 1) ^ blockCount := by
  exact BlockBinary.card_key ell blockCount

/-- Uniform full-key matching pays exactly the exponential carrier `(ell + 1)^k`. -/
theorem uniformKey_halfRenyiConcentration (ell blockCount : ℕ) :
    halfRenyiConcentration ($ᵗ (Key ell blockCount)) =
      (ell + 1 : ℝ) ^ blockCount := by
  rw [halfRenyiConcentration_uniform, card_key]
  norm_num

/-! ## Proof-only categorical completion and exact public relabeling -/

/-- The plaintext in the completed ciphertext at label `label`. -/
def categoryIndicator {C : Type} [DecidableEq C] (active label : C) : Bool :=
  decide (active = label)

@[simp]
theorem categoryIndicator_self {C : Type} [DecidableEq C] (active : C) :
    categoryIndicator active active = true := by
  simp [categoryIndicator]

@[simp]
theorem categoryIndicator_eq_false {C : Type} [DecidableEq C]
    {active label : C} (hne : active ≠ label) :
    categoryIndicator active label = false := by
  simp [categoryIndicator, hne]

/-- Relabel a complete category-indexed table by a public permutation. -/
def relabelTable {C Payload : Type} (permutation : Equiv.Perm C)
    (table : C → Payload) : C → Payload :=
  fun label ↦ table (permutation.symm label)

@[simp]
theorem relabelTable_apply {C Payload : Type} (permutation : Equiv.Perm C)
    (table : C → Payload) (label : C) :
    relabelTable permutation table label = table (permutation.symm label) := rfl

/-- Relabeling the one-hot plaintext table moves its active category exactly. -/
theorem relabelTable_categoryIndicator {C : Type} [DecidableEq C]
    (permutation : Equiv.Perm C) (active : C) :
    relabelTable permutation (categoryIndicator active) =
      categoryIndicator (permutation active) := by
  funext label
  simp only [relabelTable_apply, categoryIndicator]
  apply Bool.decide_congr
  constructor
  · intro h
    exact (congrArg permutation h).trans (permutation.apply_symm_apply label)
  · intro h
    calc
      active = permutation.symm (permutation active) :=
        (permutation.symm_apply_apply active).symm
      _ = permutation.symm label := congrArg permutation.symm h

/-- A completed category table is obtained from one coin object per category label. -/
def completeCategoryTable {C Coin Payload : Type} [DecidableEq C]
    (encrypt : Bool → Coin → Payload) (active : C) (coins : C → Coin) :
    C → Payload :=
  fun label ↦ encrypt (categoryIndicator active label) (coins label)

/-- The conditioned categorical-equivariance proof is pointwise: relabeling ciphertext objects
is exactly the same as relabeling their coin table and moving the active category. -/
theorem relabelTable_completeCategoryTable
    {C Coin Payload : Type} [DecidableEq C]
    (encrypt : Bool → Coin → Payload)
    (permutation : Equiv.Perm C) (active : C) (coins : C → Coin) :
    relabelTable permutation (completeCategoryTable encrypt active coins) =
      completeCategoryTable encrypt (permutation active)
        (relabelTable permutation coins) := by
  funext label
  simp only [relabelTable_apply, completeCategoryTable]
  congr 1
  simp only [categoryIndicator]
  apply Bool.decide_congr
  constructor
  · intro h
    exact (congrArg permutation h).trans (permutation.apply_symm_apply label)
  · intro h
    calc
      active = permutation.symm (permutation active) :=
        (permutation.symm_apply_apply active).symm
      _ = permutation.symm label := congrArg permutation.symm h

/-- Reindex all complete block tables, allowing a different public category permutation per
block. -/
def relabelTables {Block C Payload : Type}
    (permutation : Block → Equiv.Perm C)
    (tables : Block → C → Payload) : Block → C → Payload :=
  fun block ↦ relabelTable (permutation block) (tables block)

/-- Reindexing complete tables is an explicit equivalence; its inverse applies the inverse
permutation at every block. -/
def relabelTablesEquiv {Block C Payload : Type}
    (permutation : Block → Equiv.Perm C) :
    (Block → C → Payload) ≃ (Block → C → Payload) where
  toFun := relabelTables permutation
  invFun := relabelTables (fun block ↦ (permutation block).symm)
  left_inv tables := by
    funext block label
    simp [relabelTables, relabelTable]
  right_inv tables := by
    funext block label
    simp [relabelTables, relabelTable]

/-- Consequently a uniform complete ciphertext carrier is exactly invariant under every public
category relabeling. -/
theorem relabelTables_uniform_evalDist
    {Block C Payload : Type}
    [Fintype Block] [Fintype C] [Fintype Payload]
    [SampleableType (Block → C → Payload)]
    (permutation : Block → Equiv.Perm C) :
    evalDist
        (relabelTables permutation <$>
          ($ᵗ (Block → C → Payload))) =
      evalDist ($ᵗ (Block → C → Payload)) := by
  simpa only using evalDist_map_bijective_uniform_cross
    (α := Block → C → Payload) (β := Block → C → Payload)
    (relabelTables permutation)
    (relabelTablesEquiv permutation).bijective

/-! ## The exact candidate-stabilizer kernel -/

/-- Permutations fixing one distinguished point. -/
def FixedPerm (C : Type) (fixed : C) :=
  {permutation : Equiv.Perm C // permutation fixed = fixed}

/-- A permutation is equivalently its image of one point together with a residual permutation
fixing that point.  This supplies a finite, choice-free orbit decomposition. -/
def permEvaluationEquiv {C : Type} [DecidableEq C] (fixed : C) :
    Equiv.Perm C ≃ C × FixedPerm C fixed where
  toFun permutation :=
    (permutation fixed,
      ⟨permutation.trans (Equiv.swap (permutation fixed) fixed), by simp⟩)
  invFun output :=
    output.2.1.trans (Equiv.swap fixed output.1)
  left_inv permutation := by
    ext point
    simp only [Equiv.trans_apply]
    rw [Equiv.swap_comm (permutation fixed) fixed]
    exact (Equiv.swap fixed (permutation fixed)).symm_apply_apply _
  right_inv output := by
    rcases output with ⟨image, ⟨residual, hfixed⟩⟩
    apply Prod.ext
    · simp [Equiv.trans_apply, hfixed]
    · apply Subtype.ext
      ext point
      simp only [Equiv.trans_apply, hfixed, Equiv.swap_apply_left]
      rw [Equiv.swap_comm image fixed]
      exact (Equiv.swap fixed image).symm_apply_apply _

/-- Evaluation of a uniformly sampled permutation at a fixed point is exactly uniform. -/
theorem permutationEvaluation_uniform_evalDist
    {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    [SampleableType C] [SampleableType (Equiv.Perm C)]
    (fixed : C) :
    evalDist ((fun permutation : Equiv.Perm C ↦ permutation fixed) <$>
        ($ᵗ Equiv.Perm C)) =
      evalDist ($ᵗ C) := by
  classical
  letI : Nonempty (FixedPerm C fixed) :=
    ⟨⟨Equiv.refl C, rfl⟩⟩
  letI : Fintype (FixedPerm C fixed) := by
    unfold FixedPerm
    infer_instance
  letI : SampleableType (FixedPerm C fixed) :=
    SampleableType.ofFintype (FixedPerm C fixed)
  letI : SampleableType (C × FixedPerm C fixed) :=
    SampleableType.ofFintype (C × FixedPerm C fixed)
  have hdecomposition :
    evalDist (permEvaluationEquiv fixed <$> ($ᵗ Equiv.Perm C)) =
        evalDist ($ᵗ (C × FixedPerm C fixed)) :=
    evalDist_map_bijective_uniform_cross
      (α := Equiv.Perm C) (β := C × FixedPerm C fixed)
      (permEvaluationEquiv fixed) (permEvaluationEquiv fixed).bijective
  have hmapped := evalDist_map_eq_of_evalDist_eq hdecomposition Prod.fst
  have hmarginal :
      evalDist (Prod.fst <$> ($ᵗ (C × FixedPerm C fixed))) =
        evalDist ($ᵗ C) :=
    evalDist_map_fst_uniformSample_prod
  simpa [Functor.map_map, permEvaluationEquiv] using hmapped.trans hmarginal

/-- A stabilizer of `candidate` is represented by a permutation of its complement. -/
def extendCandidateStabilizer {C : Type} [DecidableEq C] (candidate : C)
    (permutation : Equiv.Perm {category : C // category ≠ candidate}) :
    Equiv.Perm C :=
  (Equiv.refl {category : C // category = candidate}).subtypeCongr permutation

@[simp]
theorem extendCandidateStabilizer_fixed
    {C : Type} [DecidableEq C] (candidate : C)
    (permutation : Equiv.Perm {category : C // category ≠ candidate}) :
    extendCandidateStabilizer candidate permutation candidate = candidate := by
  unfold extendCandidateStabilizer
  change (Equiv.Perm.subtypeCongr
    (Equiv.refl {category : C // category = candidate}) permutation) candidate = candidate
  simpa only [Equiv.refl_apply, Subtype.coe_eta] using
    (Equiv.Perm.subtypeCongr.left_apply
      (Equiv.refl {category : C // category = candidate}) permutation rfl)

theorem extendCandidateStabilizer_apply
    {C : Type} [DecidableEq C] {candidate actual : C}
    (hwrong : actual ≠ candidate)
    (permutation : Equiv.Perm {category : C // category ≠ candidate}) :
    extendCandidateStabilizer candidate permutation actual =
      permutation ⟨actual, hwrong⟩ := by
  unfold extendCandidateStabilizer
  change (Equiv.Perm.subtypeCongr
    (Equiv.refl {category : C // category = candidate}) permutation) actual =
      permutation ⟨actual, hwrong⟩
  exact Equiv.Perm.subtypeCongr.right_apply
    (Equiv.refl {category : C // category = candidate}) permutation hwrong

/-- Therefore a uniform candidate stabilizer sends every wrong actual category uniformly over
the complement of the candidate.  This discharges the group-action symmetry used before the
explicit compatible-candidate count. -/
theorem candidateStabilizerImage_uniform_evalDist
    {C : Type} [Fintype C] [DecidableEq C]
    {candidate actual : C} (hwrong : actual ≠ candidate)
    [SampleableType {category : C // category ≠ candidate}]
    [SampleableType
      (Equiv.Perm {category : C // category ≠ candidate})] :
    evalDist
        ((fun permutation :
            Equiv.Perm {category : C // category ≠ candidate} ↦
              permutation ⟨actual, hwrong⟩) <$>
          ($ᵗ Equiv.Perm {category : C // category ≠ candidate})) =
      evalDist ($ᵗ {category : C // category ≠ candidate}) := by
  letI : Nonempty {category : C // category ≠ candidate} :=
    ⟨⟨actual, hwrong⟩⟩
  exact permutationEvaluation_uniform_evalDist
    (C := {category : C // category ≠ candidate})
    (⟨actual, hwrong⟩ : {category : C // category ≠ candidate})

/-- Candidates compatible with the wrong-candidate experiment: the guessed category differs
from the actual category and the stabilizer image cannot equal the guessed category. -/
def compatibleWrongCandidates {C : Type} [Fintype C] [DecidableEq C]
    (actual output : C) : Finset C :=
  (Finset.univ.erase actual).erase output

@[simp]
theorem card_compatibleWrongCandidates_self
    {C : Type} [Fintype C] [DecidableEq C] (actual : C) :
    (compatibleWrongCandidates actual actual).card = Fintype.card C - 1 := by
  simp [compatibleWrongCandidates]

theorem card_compatibleWrongCandidates_of_ne
    {C : Type} [Fintype C] [DecidableEq C]
    {actual output : C} (hne : actual ≠ output) :
    (compatibleWrongCandidates actual output).card = Fintype.card C - 2 := by
  have houtput : output ∈ Finset.univ.erase actual := by
    simp [Ne.symm hne]
  rw [compatibleWrongCandidates, Finset.card_erase_of_mem houtput]
  simp
  omega

/-- Normalize the explicit compatible-candidate count by the two independent complement choices.
This is the finite counting experiment underlying (7.3). -/
def countedWrongCandidateKernel {C : Type} [Fintype C] [DecidableEq C]
    (actual output : C) : ℝ :=
  (compatibleWrongCandidates actual output).card /
    ((Fintype.card C - 1 : ℕ) : ℝ) ^ 2

/-- The diagonal mass of the candidate-stabilizer transition. -/
def candidateLambda (L : ℕ) : ℝ :=
  1 / ((L : ℝ) - 1) ^ 2

theorem one_sub_candidateLambda_pos
    {L : ℕ} (hL : 3 ≤ L) : 0 < 1 - candidateLambda L := by
  have hLreal : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hdenominator : 1 < ((L : ℝ) - 1) ^ 2 := by
    nlinarith [sq_nonneg ((L : ℝ) - 1)]
  have hpositive : 0 < ((L : ℝ) - 1) ^ 2 := by linarith
  have hinverse : 1 / ((L : ℝ) - 1) ^ 2 < 1 :=
    (div_lt_one hpositive).2 hdenominator
  simpa [candidateLambda] using sub_pos.mpr hinverse

/-- The exact transition law after averaging a uniform wrong candidate and a uniform element of
its stabilizer. -/
def wrongCandidateKernel (L : ℕ) {C : Type} [DecidableEq C]
    (actual output : C) : ℝ :=
  if actual = output then
    1 / ((L : ℝ) - 1)
  else
    ((L : ℝ) - 2) / ((L : ℝ) - 1) ^ 2

/-- The explicit finite candidate count evaluates to the displayed diagonal/off-diagonal
transition kernel. -/
theorem countedWrongCandidateKernel_eq
    {L : ℕ} (hL : 3 ≤ L) (actual output : Fin L) :
    countedWrongCandidateKernel actual output =
      wrongCandidateKernel L actual output := by
  have hone : 1 ≤ L := by omega
  have htwo : 2 ≤ L := by omega
  have hLreal : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hminusOne : (L : ℝ) - 1 ≠ 0 := by linarith
  by_cases heq : actual = output
  · subst output
    rw [countedWrongCandidateKernel, card_compatibleWrongCandidates_self]
    simp only [Fintype.card_fin, wrongCandidateKernel, if_pos]
    rw [Nat.cast_sub hone]
    norm_num
    field_simp [hminusOne]
  · rw [countedWrongCandidateKernel,
      card_compatibleWrongCandidates_of_ne heq]
    simp only [Fintype.card_fin, wrongCandidateKernel, if_neg heq]
    rw [Nat.cast_sub htwo, Nat.cast_sub hone]
    norm_num

/-- Formula (7.5): for at least three categories the wrong-candidate kernel is exactly
`lambda * I + (1 - lambda) * J`. -/
theorem wrongCandidateKernel_eq_identity_uniform
    {L : ℕ} (hL : 3 ≤ L) (actual output : Fin L) :
    wrongCandidateKernel L actual output =
      candidateLambda L * (if actual = output then 1 else 0) +
        (1 - candidateLambda L) * (1 / (L : ℝ)) := by
  have hLreal : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLzero : (L : ℝ) ≠ 0 := by linarith
  have hLminusOne : (L : ℝ) - 1 ≠ 0 := by linarith
  have hsquare : ((L : ℝ) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hLminusOne
  by_cases heq : actual = output
  · unfold wrongCandidateKernel candidateLambda
    rw [if_pos heq, if_pos heq]
    field_simp [hLzero, hLminusOne, hsquare]
    ring
  · unfold wrongCandidateKernel candidateLambda
    rw [if_neg heq, if_neg heq]
    field_simp [hLzero, hLminusOne, hsquare]
    ring

@[simp]
theorem candidateLambda_two : candidateLambda 2 = 1 := by
  norm_num [candidateLambda]

/-- With only two categories the stabilizer kernel is the identity, so this randomizer supplies
no adjacent-hybrid mixing. -/
theorem wrongCandidateKernel_two (actual output : Fin 2) :
    wrongCandidateKernel 2 actual output =
      if actual = output then 1 else 0 := by
  by_cases heq : actual = output
  · simp [wrongCandidateKernel, heq]
    norm_num
  · simp [wrongCandidateKernel, heq]

/-! ## Multicategory prediction -/

/-- Acceptance-to-success conversion used by the category predictor. -/
def predictorSuccess (L : ℕ) (correctAcceptance wrongAcceptance : ℝ) : ℝ :=
  1 / (L : ℝ) + (correctAcceptance - wrongAcceptance) / (L : ℝ)

/-- Substituting correct-candidate preservation and the wrong-candidate mixture gives the signed
prediction identity from (8.2). -/
theorem predictorSuccess_sub_uniform
    {L : ℕ} (hL : 3 ≤ L) (previous next : ℝ) :
    predictorSuccess L previous
          (candidateLambda L * previous + (1 - candidateLambda L) * next) -
        1 / (L : ℝ) =
      (1 - candidateLambda L) / (L : ℝ) * (previous - next) := by
  have hLreal : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLzero : (L : ℝ) ≠ 0 := by linarith
  unfold predictorSuccess
  field_simp
  ring

/-- The exact loss multiplying each adjacent category-hybrid prediction excess. -/
def predictionCoefficient (L : ℕ) : ℝ :=
  ((L : ℝ) - 1) ^ 2 / ((L : ℝ) - 2)

/-- Algebraic form of `L / (1 - lambda_L) = (L - 1)^2 / (L - 2)`. -/
theorem predictionCoefficient_eq
    {L : ℕ} (hL : 3 ≤ L) :
    (L : ℝ) / (1 - candidateLambda L) = predictionCoefficient L := by
  have hLreal : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLminusOne : (L : ℝ) - 1 ≠ 0 := by linarith
  have hLminusTwo : (L : ℝ) - 2 ≠ 0 := by linarith
  have honeMinus : 1 - candidateLambda L ≠ 0 :=
    ne_of_gt (one_sub_candidateLambda_pos hL)
  apply (div_eq_iff honeMinus).2
  unfold candidateLambda predictionCoefficient
  field_simp [hLminusOne, hLminusTwo]
  ring

/-- A convenient exact definition of the complemented predictor's nonnegative excess. -/
def categoryPredictionExcess (L : ℕ) (previous next : ℝ) : ℝ :=
  (1 - candidateLambda L) / (L : ℝ) * |previous - next|

theorem adjacentGap_eq_predictionCoefficient_mul_excess
    {L : ℕ} (hL : 3 ≤ L) (previous next : ℝ) :
    |previous - next| =
      predictionCoefficient L * categoryPredictionExcess L previous next := by
  have hLreal : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLzero : (L : ℝ) ≠ 0 := by linarith
  have hLminusOne : (L : ℝ) - 1 ≠ 0 := by linarith
  have hLminusTwo : (L : ℝ) - 2 ≠ 0 := by linarith
  have honeMinus : 1 - candidateLambda L ≠ 0 :=
    ne_of_gt (one_sub_candidateLambda_pos hL)
  have hfactor :
      predictionCoefficient L *
          ((1 - candidateLambda L) / (L : ℝ)) = 1 := by
    rw [← predictionCoefficient_eq hL]
    field_simp [hLzero, honeMinus]
  unfold categoryPredictionExcess
  rw [← mul_assoc, hfactor, one_mul]

/-- Under an independent uniform category, the accept/otherwise-complement rule has success
exactly `1/L`, regardless of the conditioned distinguisher acceptance probability. -/
theorem uniformSource_predictionBaseline
    {L : ℕ} (hL : 2 ≤ L) (acceptance : ℝ) :
    (1 / (L : ℝ)) * acceptance +
        (((L : ℝ) - 1) / (L : ℝ)) *
          ((1 - acceptance) / ((L : ℝ) - 1)) =
      1 / (L : ℝ) := by
  have hLreal : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLzero : (L : ℝ) ≠ 0 := by linarith
  have hLminusOne : (L : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Telescope the adjacent hybrid predictions without any full-key matching factor. -/
theorem realToIndependent_le_sum_categoryPrediction
    {L blockCount : ℕ} (_hL : 3 ≤ L)
    (values prediction : ℕ → ℝ)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤ predictionCoefficient L * prediction block) :
    |values 0 - values blockCount| ≤
      predictionCoefficient L *
        ∑ block ∈ Finset.range blockCount, prediction block := by
  calc
    |values 0 - values blockCount| ≤
        ∑ block ∈ Finset.range blockCount,
          |values block - values (block + 1)| :=
      abs_sub_le_sum_blockGaps values blockCount
    _ ≤ ∑ block ∈ Finset.range blockCount,
          predictionCoefficient L * prediction block := by
      apply Finset.sum_le_sum
      intro block hblock
      exact hlocal block (Finset.mem_range.mp hblock)
    _ = predictionCoefficient L *
        ∑ block ∈ Finset.range blockCount, prediction block := by
      rw [Finset.mul_sum]

/-! ## Contextual squared-bias bridge and polynomial composition -/

/-- The abstract squared-bias step behind the contextual two-copy source theorem. -/
theorem predictionExcess_le_sqrt_contextual
    {L : ℕ} (predictionExcess contextualAdvantage : ℝ)
    (hsecondMoment : predictionExcess ^ 2 ≤
      2 * (L : ℝ) * contextualAdvantage) :
    predictionExcess ≤
      Real.sqrt (2 * (L : ℝ) * contextualAdvantage) := by
  exact Real.le_sqrt_of_sq_le hsecondMoment

/-- Isolated-block form: an exact ordinary two-copy source supplies the squared-bias term and a
complete-view simulation defect is then added once. -/
theorem isolatedCategoryPrediction_le
    {L : ℕ} (predictionExcess exactPrediction sourceAdvantage defect : ℝ)
    (hsimulation : predictionExcess ≤ exactPrediction + defect)
    (hsecondMoment : exactPrediction ^ 2 ≤
      2 * (L : ℝ) * sourceAdvantage) :
    predictionExcess ≤
      Real.sqrt (2 * (L : ℝ) * sourceAdvantage) + defect := by
  have hexact := predictionExcess_le_sqrt_contextual
    (L := L) exactPrediction sourceAdvantage hsecondMoment
  linarith

/-- At the last block there is no future secret-message context, so the same bridge accepts the
complete-batch ordinary block-binary source bound directly. -/
theorem finalBlockPrediction_le
    {L : ℕ} (predictionExcess ordinarySourceAdvantage samplerDefect : ℝ)
    (hsecondMoment : predictionExcess ^ 2 ≤
      2 * (L : ℝ) *
        (2 * ordinarySourceAdvantage + samplerDefect)) :
    predictionExcess ≤
      Real.sqrt (2 * (L : ℝ) *
        (2 * ordinarySourceAdvantage + samplerDefect)) := by
  exact predictionExcess_le_sqrt_contextual
    predictionExcess (2 * ordinarySourceAdvantage + samplerDefect) hsecondMoment

/-- Direct specialization of the generic finite leakage-removal theorem to one `L`-valued block
category.  This is the game-level source of the same `sqrt (2 * L * epsilon)` factor. -/
theorem categoricalLeakageRemovalBridge
    {Secret : Type} [Fintype Secret]
    {ell : ℕ}
    (secretSampler : ProbComp Secret) (leakage : Secret → Category ell)
    (real ideal : Category ell → Secret → ProbComp Bool) :
    leakedAdvantage secretSampler leakage real ideal ≤
      Real.sqrt (2 * (ell + 1 : ℝ) *
        leakageRemovalAdvantage secretSampler ($ᵗ (Category ell)) real ideal) := by
  simpa using
    (leakedAdvantage_le_sqrt_two_mul_card_mul_removal
      secretSampler leakage real ideal)

/-- The manuscript's main real-to-zero theorem.  The local contextual advantages, CVZR endpoint,
and all finite simulation defects occur explicitly. -/
theorem blockCategoricalSelfCircular_le
    {L blockCount : ℕ} (hL : 3 ≤ L)
    (values contextualAdvantage : ℕ → ℝ)
    (zeroAcceptance cvzrAdvantage simulationDefect : ℝ)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤
        predictionCoefficient L *
          Real.sqrt (2 * (L : ℝ) * contextualAdvantage block))
    (hzero : |values blockCount - zeroAcceptance| ≤
      2 * cvzrAdvantage + simulationDefect) :
    |values 0 - zeroAcceptance| ≤
      predictionCoefficient L *
          ∑ block ∈ Finset.range blockCount,
            Real.sqrt (2 * (L : ℝ) * contextualAdvantage block) +
        2 * cvzrAdvantage + simulationDefect := by
  have hblocks := realToIndependent_le_sum_categoryPrediction hL values
    (fun block ↦ Real.sqrt (2 * (L : ℝ) * contextualAdvantage block)) hlocal
  calc
    |values 0 - zeroAcceptance| ≤
        |values 0 - values blockCount| +
          |values blockCount - zeroAcceptance| := abs_sub_le _ _ _
    _ ≤ predictionCoefficient L *
          ∑ block ∈ Finset.range blockCount,
            Real.sqrt (2 * (L : ℝ) * contextualAdvantage block) +
        (2 * cvzrAdvantage + simulationDefect) :=
      add_le_add hblocks hzero
    _ = _ := by ring

/-- Uniform contextual bounds give the explicit polynomial `k * O(L^(3/2))` loss and no
`L^k` term. -/
theorem blockCategoricalSelfCircular_uniformContext_le
    {L blockCount : ℕ} (hL : 3 ≤ L)
    (values : ℕ → ℝ)
    (contextualBound zeroAcceptance cvzrAdvantage simulationDefect : ℝ)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤
        predictionCoefficient L *
          Real.sqrt (2 * (L : ℝ) * contextualBound))
    (hzero : |values blockCount - zeroAcceptance| ≤
      2 * cvzrAdvantage + simulationDefect) :
    |values 0 - zeroAcceptance| ≤
      (blockCount : ℝ) * predictionCoefficient L *
          Real.sqrt (2 * (L : ℝ) * contextualBound) +
        2 * cvzrAdvantage + simulationDefect := by
  have hmain := blockCategoricalSelfCircular_le hL values
    (fun _ ↦ contextualBound) zeroAcceptance cvzrAdvantage simulationDefect hlocal hzero
  rw [show (∑ _block ∈ Finset.range blockCount,
      Real.sqrt (2 * (L : ℝ) * contextualBound)) =
        (blockCount : ℝ) * Real.sqrt (2 * (L : ℝ) * contextualBound) by
      simp] at hmain
  have hreorder :
      predictionCoefficient L *
          ((blockCount : ℝ) * Real.sqrt (2 * (L : ℝ) * contextualBound)) =
        (blockCount : ℝ) * predictionCoefficient L *
          Real.sqrt (2 * (L : ℝ) * contextualBound) := by ring
  rw [hreorder] at hmain
  exact hmain

/-- Final real-to-ideal composition, including the complete-batch correlated zero-BRK endpoint.
Each source and defect is charged with precisely the coefficient displayed in (18.1). -/
theorem realToIdealBlockCategorical_le
    {L blockCount : ℕ} (hL : 3 ≤ L)
    (values contextualAdvantage : ℕ → ℝ)
    (zeroAcceptance idealAcceptance cvzrAdvantage zeroSourceAdvantage : ℝ)
    (cvzrDefect zeroEndpointDefect samplerDefect : ℝ)
    (hlocal : ∀ block < blockCount,
      |values block - values (block + 1)| ≤
        predictionCoefficient L *
          Real.sqrt (2 * (L : ℝ) * contextualAdvantage block))
    (hindependentToZero : |values blockCount - zeroAcceptance| ≤
      2 * cvzrAdvantage + cvzrDefect)
    (hzeroEndpoint : |zeroAcceptance - idealAcceptance| ≤
      2 * zeroSourceAdvantage + zeroEndpointDefect)
    (hdefects : cvzrDefect + zeroEndpointDefect ≤ samplerDefect) :
    |values 0 - idealAcceptance| ≤
      predictionCoefficient L *
          ∑ block ∈ Finset.range blockCount,
            Real.sqrt (2 * (L : ℝ) * contextualAdvantage block) +
        2 * cvzrAdvantage + 2 * zeroSourceAdvantage + samplerDefect := by
  have hrealToZero := blockCategoricalSelfCircular_le hL values contextualAdvantage
    zeroAcceptance cvzrAdvantage cvzrDefect hlocal hindependentToZero
  calc
    |values 0 - idealAcceptance| ≤
        |values 0 - zeroAcceptance| + |zeroAcceptance - idealAcceptance| :=
      abs_sub_le _ _ _
    _ ≤ predictionCoefficient L *
          ∑ block ∈ Finset.range blockCount,
            Real.sqrt (2 * (L : ℝ) * contextualAdvantage block) +
        2 * cvzrAdvantage + cvzrDefect +
        (2 * zeroSourceAdvantage + zeroEndpointDefect) :=
      add_le_add hrealToZero hzeroEndpoint
    _ ≤ _ := by linarith

/-! ## Correlated zero-BRK sample extraction -/

/-- Negacyclic reciprocal-coefficient extraction is a signed permutation of every mask
coefficient. -/
theorem reciprocalCoefficients_bijective
    {R : Type} [AddGroup R] {degree : ℕ} :
    Function.Bijective
      (SampleExtraction.reciprocalCoefficients :
        (Fin (degree + 1) → R) → (Fin (degree + 1) → R)) := by
  exact Function.Involutive.bijective
    RotationLookup.reciprocalCoefficients_involutive

/-- Hence sample extraction maps a uniform ring mask to an exactly uniform scalar mask. -/
theorem reciprocalCoefficients_uniform_evalDist
    {R : Type} [AddGroup R] [Fintype R] [SampleableType R]
    {degree : ℕ} :
    evalDist
        (SampleExtraction.reciprocalCoefficients <$>
          ($ᵗ (Fin (degree + 1) → R))) =
      evalDist ($ᵗ (Fin (degree + 1) → R)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Fin (degree + 1) → R) (β := Fin (degree + 1) → R)
    (SampleExtraction.reciprocalCoefficients :
      (Fin (degree + 1) → R) → (Fin (degree + 1) → R))
    reciprocalCoefficients_bijective

/-! ## Original zero-or-one ciphertext representation -/

/-- Integer simplex encoding: category zero is the zero vector and category `j + 1` is the
`j`-th standard basis vector. -/
def simplexVertex (ell : ℕ) (category : Category ell) : Fin ell → ℤ :=
  Fin.cases (fun _ ↦ 0)
    (fun selected coordinate ↦ if selected = coordinate then 1 else 0)
    category

@[simp]
theorem simplexVertex_zero (ell : ℕ) :
    simplexVertex ell 0 = 0 := by
  funext coordinate
  rfl

@[simp]
theorem simplexVertex_succ (ell : ℕ) (selected coordinate : Fin ell) :
    simplexVertex ell selected.succ coordinate =
      if selected = coordinate then 1 else 0 := by
  rfl

/-- Translation vector of the affine action induced by a category permutation. -/
def simplexTranslation {ell : ℕ} (permutation : Equiv.Perm (Category ell)) :
    Fin ell → ℤ :=
  simplexVertex ell (permutation 0)

/-- Columns of the integral linear part induced by a category permutation. -/
def simplexLinearColumn {ell : ℕ} (permutation : Equiv.Perm (Category ell))
    (selected : Fin ell) : Fin ell → ℤ :=
  simplexVertex ell (permutation selected.succ) - simplexTranslation permutation

/-- The affine action in the original `ell`-ciphertext representation. -/
def simplexAffineAction {ell : ℕ} (permutation : Equiv.Perm (Category ell))
    (point : Fin ell → ℤ) : Fin ell → ℤ :=
  simplexTranslation permutation +
    ∑ selected : Fin ell, point selected • simplexLinearColumn permutation selected

/-- Formula (17.1) on the zero vertex. -/
theorem simplexAffineAction_zero
    {ell : ℕ} (permutation : Equiv.Perm (Category ell)) :
    simplexAffineAction permutation (simplexVertex ell 0) =
      simplexVertex ell (permutation 0) := by
  simp [simplexAffineAction, simplexTranslation]

/-- Formula (17.1) on a one-hot vertex. -/
theorem simplexAffineAction_succ
    {ell : ℕ} (permutation : Equiv.Perm (Category ell))
    (selected : Fin ell) :
    simplexAffineAction permutation (simplexVertex ell selected.succ) =
      simplexVertex ell (permutation selected.succ) := by
  funext coordinate
  simp only [simplexAffineAction, simplexVertex_succ, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single selected]
  · simp [simplexLinearColumn, simplexTranslation]
  · intro other _ hother
    simp [Ne.symm hother]
  · simp

/-- Every category vertex is relabeled by the integral affine action.  The resulting transformed
error vector is the linear-column combination above; comparison with a target error law is
therefore correctly charged as a complete joint representation defect. -/
theorem simplexAffineAction_vertex
    {ell : ℕ} (permutation : Equiv.Perm (Category ell))
    (category : Category ell) :
    simplexAffineAction permutation (simplexVertex ell category) =
      simplexVertex ell (permutation category) := by
  refine Fin.cases ?_ (fun selected ↦ ?_) category
  · exact simplexAffineAction_zero permutation
  · exact simplexAffineAction_succ permutation selected

/-! The following barycentric construction packages the same integral simplex permutation as an
explicit equivalence.  It is the constructive content of the manuscript's "unimodular" claim:
the action and its inverse are defined over every additive coefficient ring, so reduction modulo
any ciphertext modulus remains a permutation of the full carrier. -/

/-- Affine barycentric weights, whose total weight is one. -/
def AffineWeights (R : Type) [AddCommGroup R] [One R] (ell : ℕ) :=
  {weights : Category ell → R // ∑ category, weights category = 1}

/-- Convert ordinary simplex coordinates to barycentric weights. -/
def pointToWeights {R : Type} [AddCommGroup R] [One R] {ell : ℕ}
    (point : Fin ell → R) : AffineWeights R ell where
  val := Fin.cases (1 - ∑ coordinate, point coordinate) point
  property := by
    rw [Fin.sum_univ_succ]
    simp

/-- Drop the zero-category barycentric coordinate. -/
def weightsToPoint {R : Type} [AddCommGroup R] [One R] {ell : ℕ}
    (weights : AffineWeights R ell) : Fin ell → R :=
  fun coordinate ↦ weights.1 coordinate.succ

/-- Ordinary coordinates and total-one barycentric coordinates are explicitly equivalent. -/
def pointWeightsEquiv {R : Type} [AddCommGroup R] [One R] (ell : ℕ) :
    (Fin ell → R) ≃ AffineWeights R ell where
  toFun := pointToWeights
  invFun := weightsToPoint
  left_inv point := rfl
  right_inv weights := by
    apply Subtype.ext
    funext category
    refine Fin.cases ?_ (fun _ ↦ rfl) category
    change 1 - ∑ coordinate : Fin ell, weights.1 coordinate.succ = weights.1 0
    have htotal := weights.2
    rw [Fin.sum_univ_succ] at htotal
    exact (eq_sub_of_add_eq htotal).symm

/-- A category permutation literally reindexes barycentric coordinates. -/
def relabelWeightsEquiv {R : Type} [AddCommGroup R] [One R] {ell : ℕ}
    (permutation : Equiv.Perm (Category ell)) :
    AffineWeights R ell ≃ AffineWeights R ell where
  toFun weights := ⟨fun category ↦ weights.1 (permutation.symm category), by
    calc
      ∑ category, weights.1 (permutation.symm category) =
          ∑ category, weights.1 category :=
        Equiv.sum_comp permutation.symm weights.1
      _ = 1 := weights.2⟩
  invFun weights := ⟨fun category ↦ weights.1 (permutation category), by
    calc
      ∑ category, weights.1 (permutation category) =
          ∑ category, weights.1 category :=
        Equiv.sum_comp permutation weights.1
      _ = 1 := weights.2⟩
  left_inv weights := by
    apply Subtype.ext
    funext category
    simp
  right_inv weights := by
    apply Subtype.ext
    funext category
    simp

/-- Conjugating barycentric reindexing by `pointWeightsEquiv` gives an explicit affine
permutation of the original `ell` coordinates. -/
def simplexPointPermutationEquiv
    {R : Type} [AddCommGroup R] [One R] {ell : ℕ}
    (permutation : Equiv.Perm (Category ell)) :
    (Fin ell → R) ≃ (Fin ell → R) :=
  (pointWeightsEquiv ell).trans
    ((relabelWeightsEquiv permutation).trans (pointWeightsEquiv ell).symm)

@[simp]
theorem simplexPointPermutationEquiv_apply
    {R : Type} [AddCommGroup R] [One R] {ell : ℕ}
    (permutation : Equiv.Perm (Category ell))
    (point : Fin ell → R) (coordinate : Fin ell) :
    simplexPointPermutationEquiv permutation point coordinate =
      (pointToWeights point).1 (permutation.symm coordinate.succ) := by
  rfl

theorem pointToWeights_simplexVertex
    {ell : ℕ} (category label : Category ell) :
    (pointToWeights (simplexVertex ell category)).1 label =
      if category = label then 1 else 0 := by
  refine Fin.cases ?_ (fun selected ↦ ?_) category
  · refine Fin.cases ?_ (fun coordinate ↦ ?_) label
    · simp [pointToWeights, simplexVertex]
    · simp [pointToWeights, simplexVertex, (Fin.succ_ne_zero coordinate).symm]
  · refine Fin.cases ?_ (fun coordinate ↦ ?_) label
    · simp [pointToWeights, simplexVertex]
    · simp [pointToWeights, simplexVertex]

theorem simplexVertex_eq_indicatorSucc
    {ell : ℕ} (category : Category ell) (coordinate : Fin ell) :
    simplexVertex ell category coordinate =
      if category = coordinate.succ then 1 else 0 := by
  refine Fin.cases ?_ (fun selected ↦ ?_) category
  · simp [simplexVertex, (Fin.succ_ne_zero coordinate).symm]
  · simp [simplexVertex]

/-- The explicit barycentric equivalence realizes the same category action on every simplex
vertex.  Together with its inverse this is an implementation-independent unimodularity
certificate. -/
theorem simplexPointPermutationEquiv_vertex
    {ell : ℕ} (permutation : Equiv.Perm (Category ell))
    (category : Category ell) :
    simplexPointPermutationEquiv permutation (simplexVertex ell category) =
      simplexVertex ell (permutation category) := by
  funext coordinate
  rw [simplexPointPermutationEquiv_apply,
    pointToWeights_simplexVertex, simplexVertex_eq_indicatorSucc]
  congr 1
  exact propext permutation.eq_symm_apply

/-- The affine simplex action is a permutation over every finite coefficient carrier, hence it
preserves a uniform original-format ciphertext carrier exactly. -/
theorem simplexPointPermutation_uniform_evalDist
    {R : Type} [AddCommGroup R] [One R] [Fintype R] [SampleableType R]
    {ell : ℕ} (permutation : Equiv.Perm (Category ell)) :
    evalDist
        (simplexPointPermutationEquiv permutation <$>
          ($ᵗ (Fin ell → R))) =
      evalDist ($ᵗ (Fin ell → R)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Fin ell → R) (β := Fin ell → R)
    (simplexPointPermutationEquiv permutation)
    (simplexPointPermutationEquiv permutation).bijective

/-! ## Translation-only leakage lower bound -/

/-- Exact public translation can force recovery of a future-category tuple only when the full
family of target laws is pairwise separated.  This is the precise premise needed by the proof;
one separated pair of shifts is not sufficient to recover every category. -/
theorem futureCategories_separated_of_exactCompiler
    {Future Suffix Leakage Law : Type}
    (leakage : Future × Suffix → Leakage)
    (targetLaw : Future × Suffix → Law)
    (compiledLaw : Leakage → Law)
    (hexact : ∀ key, compiledLaw (leakage key) = targetLaw key)
    (htargetSeparated : ∀ first second,
      targetLaw first = targetLaw second → first.1 = second.1) :
    ∀ first second, leakage first = leakage second → first.1 = second.1 := by
  intro first second hleakage
  apply htargetSeparated first second
  rw [← hexact first, ← hexact second, hleakage]

/-- Once exact compilation separates every future tuple, its leakage has at least the complete
future-category carrier as Renyi-half concentration. -/
theorem futureCategoryLeakageLowerBound
    {Future Suffix Leakage : Type}
    [Fintype Future] [DecidableEq Future] [Nonempty Future]
    [Fintype Suffix] [Nonempty Suffix]
    [Fintype Leakage] [DecidableEq Leakage]
    [SampleableType Future] [SampleableType Suffix]
    [SampleableType (Future × Suffix)]
    (leakage : Future × Suffix → Leakage)
    (hseparated : ∀ first second, leakage first = leakage second →
      first.1 = second.1) :
    (Fintype.card Future : ℝ) ≤
      halfRenyiConcentration
        (leakageLaw ($ᵗ (Future × Suffix)) leakage) := by
  exact card_le_halfRenyiConcentration_leakageLaw_uniform_product
    leakage hseparated

/-- Specialization to `remainingBlocks` independent uniform `L`-category blocks. -/
theorem futureBlockKeyLeakageLowerBound
    {ell remainingBlocks : ℕ} {Suffix Leakage : Type}
    [Fintype Suffix] [Nonempty Suffix]
    [Fintype Leakage] [DecidableEq Leakage]
    [SampleableType Suffix]
    [SampleableType (Key ell remainingBlocks × Suffix)]
    (leakage : Key ell remainingBlocks × Suffix → Leakage)
    (hseparated : ∀ first second, leakage first = leakage second →
      first.1 = second.1) :
    ((ell + 1 : ℝ) ^ remainingBlocks) ≤
      halfRenyiConcentration
        (leakageLaw ($ᵗ (Key ell remainingBlocks × Suffix)) leakage) := by
  simpa using futureCategoryLeakageLowerBound leakage hseparated

/-! ## Concrete oracle countermodel -/

/-- Equality test on a repeated uniformly sampled opaque token. -/
def repeatedTokenEqualityGame
    {Token : Type} [DecidableEq Token] [SampleableType Token] : ProbComp Bool := do
  let token ← $ᵗ Token
  pure (decide (token = token))

/-- Equality test on two independently sampled opaque tokens. -/
def independentTokenEqualityGame
    {Token : Type} [DecidableEq Token] [SampleableType Token] : ProbComp Bool := do
  let first ← $ᵗ Token
  let second ← $ᵗ Token
  pure (decide (first = second))

@[simp]
theorem repeatedTokenEqualityGame_accepts
    {Token : Type} [Fintype Token] [DecidableEq Token]
    [SampleableType Token] :
    Pr[= true |
      (repeatedTokenEqualityGame (Token := Token) : ProbComp Bool)] = 1 := by
  simp [repeatedTokenEqualityGame]

/-- Two independent uniform tokens are equal with exact probability `1 / |Token|`. -/
theorem independentTokenEqualityGame_acceptance
    {Token : Type} [Fintype Token] [DecidableEq Token]
    [SampleableType Token] :
    Pr[= true |
      (independentTokenEqualityGame (Token := Token) : ProbComp Bool)] =
      (Fintype.card Token : ENNReal)⁻¹ := by
  classical
  unfold independentTokenEqualityGame
  simp only [probOutput_bind_eq_sum_fintype, probOutput_uniformSample,
    probOutput_pure, true_eq_decide_iff]
  rw [show (∑ first : Token,
      (Fintype.card Token : ENNReal)⁻¹ *
        ∑ second : Token,
          (Fintype.card Token : ENNReal)⁻¹ *
            if first = second then 1 else 0) =
      ∑ first : Token,
        (Fintype.card Token : ENNReal)⁻¹ ^ 2 by
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_eq_single first]
    · simp [pow_two]
    · intro second _ hne
      simp [Ne.symm hne]
    · simp]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card Token : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  rw [pow_two, ENNReal.mul_inv_cancel_left hcard (ENNReal.natCast_ne_top _)]

/-- Equality accepts the circular opaque-token pair always, but accepts two independent uniform
tokens with probability `1 / |Key|`. -/
def opaqueTokenEqualityGap (ell blockCount : ℕ) : ℝ :=
  1 - 1 / ((ell + 1 : ℝ) ^ blockCount)

/-- The gap is exactly `1 - L^{-k}`. -/
theorem opaqueTokenEqualityGap_eq_card
    (ell blockCount : ℕ) :
    opaqueTokenEqualityGap ell blockCount =
      1 - 1 / (Fintype.card (Key ell blockCount) : ℝ) := by
  simp [opaqueTokenEqualityGap]

/-- The numerical gap is the actual acceptance-probability difference of the repeated-token and
independent-token games. -/
theorem opaqueTokenEqualityGap_eq_gameDifference
    (ell blockCount : ℕ) :
    opaqueTokenEqualityGap ell blockCount =
      Pr[= true |
        (repeatedTokenEqualityGame (Token := Key ell blockCount) :
          ProbComp Bool)].toReal -
      Pr[= true |
        (independentTokenEqualityGame (Token := Key ell blockCount) :
          ProbComp Bool)].toReal := by
  rw [repeatedTokenEqualityGame_accepts,
    independentTokenEqualityGame_acceptance]
  calc
    opaqueTokenEqualityGap ell blockCount =
        1 - 1 / (Fintype.card (Key ell blockCount) : ℝ) :=
      opaqueTokenEqualityGap_eq_card ell blockCount
    _ = (1 : ENNReal).toReal -
        ((Fintype.card (Key ell blockCount) : ENNReal)⁻¹).toReal := by
      rw [ENNReal.toReal_one, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      rw [one_div]

/-- With at least two categories and one block, the circular/independent equality gap is
strictly positive. -/
theorem opaqueTokenEqualityGap_pos
    {ell blockCount : ℕ} (hell : 1 ≤ ell) (hblocks : 1 ≤ blockCount) :
    0 < opaqueTokenEqualityGap ell blockCount := by
  have hbase : 1 < ell + 1 := by omega
  have hpowerNat : 1 < (ell + 1) ^ blockCount :=
    Nat.one_lt_pow (by omega) hbase
  have hpowerReal : (1 : ℝ) < ((ell + 1 : ℝ) ^ blockCount) := by
    exact_mod_cast hpowerNat
  unfold opaqueTokenEqualityGap
  have hpositive : 0 < ((ell + 1 : ℝ) ^ blockCount) := by positivity
  rw [sub_pos]
  exact (div_lt_one hpositive).mpr hpowerReal

/-- Concrete numerical refutation of any black-box rule saying that zero ordinary-source
advantage plus exact public equivariance forces the contextual circular gap to be zero.  This is
the formal countermodel; the stronger phrase "no relativizing theorem" is metamathematical and
is not asserted as an internal Lean proposition. -/
theorem no_zeroSource_blackBoxBound
    {ell blockCount : ℕ} (hell : 1 ≤ ell) (hblocks : 1 ≤ blockCount) :
    ¬ opaqueTokenEqualityGap ell blockCount ≤ (0 : ℝ) + 0 := by
  simpa using (not_le.mpr (opaqueTokenEqualityGap_pos hell hblocks))

end

end FormalProof4FHE.TFHE.Native.BlockCategoricalSelfCircular
