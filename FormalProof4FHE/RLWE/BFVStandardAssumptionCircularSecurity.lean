/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.RankBound
import FormalProof4FHE.RLWE.BFVQuadraticCircularSecurity

/-!
# BFV circular security through HNF and number-ring knapsack: checked boundary

This file formalizes the sound finite algebra and the corrected theorem interface from
`sketch/bfv_standard_assumption_circular_security.tex`.

The adjacent-difference theorem is generalized to both branches `gamma = 0,1`.  A fixed-HNF
row is normalized exactly from a knapsack whose square tail is invertible.  The public
normalization is an explicit equivalence, and a linear encoding of matrix columns into an
extension field preserves both the knapsack value and uniform public weights exactly.  The
probability that the square tail is singular is tied to the repository's exact finite-field rank
formula.

The final claimed standard-assumption-only closure is not asserted.  The two cited black-box
theorems have premises omitted by the manuscript:

* the general-distribution HNF result includes a standard decisional M-LWE term, an M-SIS
  (second-preimage) term, and statistical losses, rather than following from search M-LWE alone;
* Mandal--Singh Theorem 3.1 additionally requires a medium-norm folded family with noticeable
  distinguishing advantage.  Making every relevant fold quotient a singleton makes every such
  advantage zero and therefore cannot provide that witness.

These requirements are represented by proof-carrying certificates, never by Lean axioms.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.RLWE.BFVStandardAssumptionCircularSecurity

noncomputable section

namespace BFV

export BFVQuadraticCircularSecurity
  (Batch Transcript radixWeight transcriptEquiv adjacentTransform adjacentEquiv stockTranscript
    Distinguisher stockKDMAdvantage correlatedHNFAdvantage reverseDistinguisher
    zeroUniformAdvantage stockKDMAdvantage_le_correlatedHNF_add_zero)

end BFV

/-! ## Both quadratic-circular branches -/

section GammaNormalForm

variable {R : Type} [CommRing R]

/-- Stock BFV transcript with a public scalar `gamma` multiplying every quadratic gadget
message.  The manuscript uses `gamma = 0` and `gamma = 1`. -/
def gammaStockTranscript (levels : ℕ) (radix gamma secret : R)
    (error mask : BFV.Batch R levels) : BFV.Transcript R levels :=
  (mask, fun row ↦
    mask row * secret + error row +
      gamma * BFV.radixWeight radix row * secret ^ 2)

/-- Correlated source coordinates produced by adjacent differencing in branch `gamma`. -/
def gammaCorrelatedError (levels : ℕ) (radix gamma secret : R)
    (error : BFV.Batch R levels) : BFV.Batch R levels :=
  fun row ↦ Fin.cases (gamma * secret ^ 2 + error 0)
    (fun previous ↦ error previous.succ - radix * error previous.castSucc) row

@[simp]
theorem gammaCorrelatedError_zero
    (levels : ℕ) (radix gamma secret : R) (error : BFV.Batch R levels) :
    gammaCorrelatedError levels radix gamma secret error 0 =
      gamma * secret ^ 2 + error 0 := by
  simp [gammaCorrelatedError]

@[simp]
theorem gammaCorrelatedError_succ
    (levels : ℕ) (radix gamma secret : R) (error : BFV.Batch R levels)
    (previous : Fin levels) :
    gammaCorrelatedError levels radix gamma secret error previous.succ =
      error previous.succ - radix * error previous.castSucc := by
  simp [gammaCorrelatedError]

/-- Linear fixed-HNF transcript for branch `gamma`. -/
def gammaHNFTranscript (levels : ℕ) (radix gamma secret : R)
    (error mask : BFV.Batch R levels) : BFV.Transcript R levels :=
  (mask, fun row ↦
    mask row * secret + gammaCorrelatedError levels radix gamma secret error row)

/-- Exact adjacent cancellation simultaneously covering the real (`gamma=1`) and zero
(`gamma=0`) BFV branches. -/
theorem adjacent_gammaStockTranscript
    (levels : ℕ) (radix gamma secret : R)
    (error mask : BFV.Batch R levels) :
    BFV.transcriptEquiv levels radix
        (gammaStockTranscript levels radix gamma secret error mask) =
      gammaHNFTranscript levels radix gamma secret error
        (BFV.adjacentTransform levels radix mask) := by
  apply Prod.ext
  · rfl
  · funext row
    refine Fin.cases ?_ (fun previous ↦ ?_) row
    · change
        BFV.adjacentTransform levels radix
            (fun row ↦ mask row * secret + error row +
              gamma * BFV.radixWeight radix row * secret ^ 2) 0 =
          BFV.adjacentTransform levels radix mask 0 * secret +
            gammaCorrelatedError levels radix gamma secret error 0
      simp [BFV.radixWeight]
      ring
    · change
        BFV.adjacentTransform levels radix
            (fun row ↦ mask row * secret + error row +
              gamma * BFV.radixWeight radix row * secret ^ 2) previous.succ =
          BFV.adjacentTransform levels radix mask previous.succ * secret +
            gammaCorrelatedError levels radix gamma secret error previous.succ
      simp [BFV.radixWeight, pow_succ]
      ring

/-- Branch-dependent first-coordinate spike. -/
def gammaSquareSpike (levels : ℕ) (gamma secret : R) : BFV.Batch R levels :=
  fun row ↦ Fin.cases (gamma * secret ^ 2) (fun _previous ↦ 0) row

theorem gammaCorrelatedError_eq_adjacent_add_spike
    (levels : ℕ) (radix gamma secret : R) (error : BFV.Batch R levels) :
    gammaCorrelatedError levels radix gamma secret error =
      BFV.adjacentTransform levels radix error + gammaSquareSpike levels gamma secret := by
  funext row
  refine Fin.cases ?_ (fun previous ↦ ?_) row <;>
    simp [gammaSquareSpike]
  ring

/-- For every fixed `gamma`, correlated source coordinates are only a bijective
reparameterization of the original secret and independent errors. -/
def gammaSourceEquiv (levels : ℕ) (radix gamma : R) :
    (R × BFV.Batch R levels) ≃ (R × BFV.Batch R levels) where
  toFun source :=
    (source.1, gammaCorrelatedError levels radix gamma source.1 source.2)
  invFun source :=
    (source.1, (BFV.adjacentEquiv levels radix).symm
      (source.2 - gammaSquareSpike levels gamma source.1))
  left_inv source := by
    rcases source with ⟨secret, error⟩
    apply Prod.ext
    · rfl
    · change
        (BFV.adjacentEquiv levels radix).symm
            (gammaCorrelatedError levels radix gamma secret error -
              gammaSquareSpike levels gamma secret) = error
      rw [gammaCorrelatedError_eq_adjacent_add_spike]
      have hSub :
          BFV.adjacentTransform levels radix error + gammaSquareSpike levels gamma secret -
              gammaSquareSpike levels gamma secret =
            BFV.adjacentTransform levels radix error := by
        funext row
        simp
      rw [hSub]
      exact (BFV.adjacentEquiv levels radix).symm_apply_apply error
  right_inv source := by
    rcases source with ⟨secret, error⟩
    apply Prod.ext
    · rfl
    · change
        gammaCorrelatedError levels radix gamma secret
            ((BFV.adjacentEquiv levels radix).symm
              (error - gammaSquareSpike levels gamma secret)) = error
      rw [gammaCorrelatedError_eq_adjacent_add_spike]
      change
        BFV.adjacentEquiv levels radix
            ((BFV.adjacentEquiv levels radix).symm
              (error - gammaSquareSpike levels gamma secret)) +
                gammaSquareSpike levels gamma secret = error
      rw [Equiv.apply_symm_apply]
      funext row
      simp

/-- The branch source equivalence preserves every point mass, which is the exact finite content
of entropy preservation. -/
theorem gammaSource_probOutput
    (levels : ℕ) (radix gamma : R)
    (sourceSampler : ProbComp (R × BFV.Batch R levels))
    (source : R × BFV.Batch R levels) :
    Pr[= gammaSourceEquiv levels radix gamma source |
        gammaSourceEquiv levels radix gamma <$> sourceSampler] =
      Pr[= source | sourceSampler] := by
  exact probOutput_map_injective sourceSampler
    (gammaSourceEquiv levels radix gamma).injective source

theorem gammaStockTranscript_one
    (levels : ℕ) (radix secret : R)
    (error mask : BFV.Batch R levels) :
    gammaStockTranscript levels radix 1 secret error mask =
      BFV.stockTranscript levels radix secret error mask := by
  simp [gammaStockTranscript, BFV.stockTranscript]

theorem gammaStockTranscript_zero
    (levels : ℕ) (radix secret : R)
    (error mask : BFV.Batch R levels) :
    gammaStockTranscript levels radix 0 secret error mask =
      (mask, fun row ↦ mask row * secret + error row) := by
  simp [gammaStockTranscript]

end GammaNormalForm

/-! ## Exact fixed-HNF / invertible-tail knapsack normalization -/

section HNFKnapsack

variable {F Row : Type} [Field F]

/-- Vectors indexed by HNF rows. -/
abbrev Vector := Row → F

/-- Source coefficient followed by the HNF error coordinates. -/
abbrev HNFSource := F × Vector (F := F) (Row := Row)

/-- The fixed-HNF value `[-a | I]x`. -/
def hnfValue (mask : Vector (F := F) (Row := Row))
    (source : HNFSource (F := F) (Row := Row)) : Vector (F := F) (Row := Row) :=
  fun row ↦ -mask row * source.1 + source.2 row

/-- Knapsack value represented by its first column and an invertible square tail. -/
def invertibleTailKnapsackValue
    (column : Vector (F := F) (Row := Row))
    (tail : Vector (F := F) (Row := Row) ≃ₗ[F] Vector (F := F) (Row := Row))
    (source : HNFSource (F := F) (Row := Row)) : Vector (F := F) (Row := Row) :=
  source.1 • column + tail source.2

/-- Normalize the first column of an invertible-tail knapsack to the HNF mask. -/
def normalizedMask
    (tail : Vector (F := F) (Row := Row) ≃ₗ[F] Vector (F := F) (Row := Row))
    (column : Vector (F := F) (Row := Row)) : Vector (F := F) (Row := Row) :=
  -tail.symm column

/-- Applying the inverse tail to a knapsack value gives the fixed-HNF value exactly. -/
theorem normalize_invertibleTailKnapsackValue
    (column : Vector (F := F) (Row := Row))
    (tail : Vector (F := F) (Row := Row) ≃ₗ[F] Vector (F := F) (Row := Row))
    (source : HNFSource (F := F) (Row := Row)) :
    tail.symm (invertibleTailKnapsackValue column tail source) =
      hnfValue (normalizedMask tail column) source := by
  ext row
  simp [invertibleTailKnapsackValue, hnfValue, normalizedMask]
  ring

/-- Public normalization of a first-column/output pair for a fixed invertible tail. -/
def publicNormalizationEquiv
    (tail : Vector (F := F) (Row := Row) ≃ₗ[F] Vector (F := F) (Row := Row)) :
    (Vector (F := F) (Row := Row) × Vector (F := F) (Row := Row)) ≃
      (Vector (F := F) (Row := Row) × Vector (F := F) (Row := Row)) where
  toFun pair := (normalizedMask tail pair.1, tail.symm pair.2)
  invFun pair := (-tail pair.1, tail pair.2)
  left_inv pair := by
    rcases pair with ⟨column, value⟩
    apply Prod.ext
    · simp [normalizedMask]
    · simp
  right_inv pair := by
    rcases pair with ⟨mask, value⟩
    apply Prod.ext
    · simp [normalizedMask]
    · simp

/-- The public normalization maps every real invertible-tail knapsack point to the corresponding
fixed-HNF point. -/
theorem publicNormalizationEquiv_real
    (column : Vector (F := F) (Row := Row))
    (tail : Vector (F := F) (Row := Row) ≃ₗ[F] Vector (F := F) (Row := Row))
    (source : HNFSource (F := F) (Row := Row)) :
    publicNormalizationEquiv tail
        (column, invertibleTailKnapsackValue column tail source) =
      (normalizedMask tail column, hnfValue (normalizedMask tail column) source) := by
  apply Prod.ext
  · rfl
  · exact normalize_invertibleTailKnapsackValue column tail source

/-- For every fixed invertible tail, public normalization preserves a fully uniform
first-column/output pair exactly. -/
theorem publicNormalizationEquiv_uniform_evalDist
    [Fintype F] [SampleableType F] [Fintype Row] [DecidableEq Row]
    (tail : Vector (F := F) (Row := Row) ≃ₗ[F] Vector (F := F) (Row := Row)) :
    evalDist (publicNormalizationEquiv tail <$>
      ($ᵗ (Vector (F := F) (Row := Row) × Vector (F := F) (Row := Row)))) =
      evalDist ($ᵗ (Vector (F := F) (Row := Row) × Vector (F := F) (Row := Row))) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Vector (F := F) (Row := Row) × Vector (F := F) (Row := Row))
    (β := Vector (F := F) (Row := Row) × Vector (F := F) (Row := Row))
    (publicNormalizationEquiv tail) (publicNormalizationEquiv tail).bijective

end HNFKnapsack

/-! ## Exact extension-field encoding -/

section ExtensionEncoding

variable {F E Row : Type} [Field F] [AddCommGroup E] [Module F E]
variable [Fintype Row]

/-- Encode the first column and every square-tail column through an `F`-linear equivalence. -/
def encodeWeights
    (encoding : (Row → F) ≃ₗ[F] E)
    (column : Row → F) (tail : Matrix Row Row F) : E × (Row → E) :=
  (encoding column, fun col ↦ encoding (fun row ↦ tail row col))

/-- Decode extension-field weights columnwise. -/
def decodeWeights
    (encoding : (Row → F) ≃ₗ[F] E)
    (weights : E × (Row → E)) : (Row → F) × Matrix Row Row F :=
  (encoding.symm weights.1,
    fun row col ↦ encoding.symm (weights.2 col) row)

/-- Matrix columns and extension-field weights are in explicit bijection. -/
def weightEncodingEquiv
    (encoding : (Row → F) ≃ₗ[F] E) :
    ((Row → F) × Matrix Row Row F) ≃ (E × (Row → E)) where
  toFun pair := encodeWeights encoding pair.1 pair.2
  invFun := decodeWeights encoding
  left_inv pair := by
    rcases pair with ⟨column, tail⟩
    apply Prod.ext
    · simp [encodeWeights, decodeWeights]
    · ext row col
      simp [encodeWeights, decodeWeights]
  right_inv weights := by
    rcases weights with ⟨first, rest⟩
    apply Prod.ext
    · simp [encodeWeights, decodeWeights]
    · funext col
      simp [encodeWeights, decodeWeights]

/-- Matrix-form knapsack evaluation. -/
def matrixKnapsackValue
    (column : Row → F) (tail : Matrix Row Row F)
    (source : F × (Row → F)) : Row → F :=
  source.1 • column + tail *ᵥ source.2

/-- Extension-field knapsack evaluation with coefficients in the base field. -/
def extensionKnapsackValue
    (weights : E × (Row → E)) (source : F × (Row → F)) : E :=
  source.1 • weights.1 + ∑ col, source.2 col • weights.2 col

/-- A linear extension-field encoding converts matrix knapsack to scalar extension-field
knapsack exactly. -/
theorem encode_matrixKnapsackValue
    (encoding : (Row → F) ≃ₗ[F] E)
    (column : Row → F) (tail : Matrix Row Row F)
    (source : F × (Row → F)) :
    encoding (matrixKnapsackValue column tail source) =
      extensionKnapsackValue (encodeWeights encoding column tail) source := by
  have hTail :
      tail *ᵥ source.2 =
        ∑ col, source.2 col • (fun row ↦ tail row col) := by
    ext row
    simp [Matrix.mulVec, dotProduct, mul_comm]
  simp [matrixKnapsackValue, extensionKnapsackValue, encodeWeights, hTail,
    map_add, map_sum]

/-- Independent uniform matrix columns encode to independent uniform extension-field weights. -/
theorem weightEncoding_uniform_evalDist
    [Fintype F] [SampleableType F] [Fintype E] [SampleableType E]
    [SampleableType (Row → F)] [SampleableType (Matrix Row Row F)]
    [SampleableType (Row → E)]
    (encoding : (Row → F) ≃ₗ[F] E) :
    evalDist (weightEncodingEquiv encoding <$>
      ($ᵗ ((Row → F) × Matrix Row Row F))) =
      evalDist ($ᵗ (E × (Row → E))) := by
  exact evalDist_map_bijective_uniform_cross
    (α := (Row → F) × Matrix Row Row F) (β := E × (Row → E))
    (weightEncodingEquiv encoding) (weightEncodingEquiv encoding).bijective

end ExtensionEncoding

/-! ## Exact finite-field conditioning term -/

section RankFailure

/-- Probability that the square tail in the HNF--knapsack bridge is singular. -/
noncomputable def squareTailFailureProbability
    (F : Type) [Field F] [Fintype F] [SampleableType F] (dimension : ℕ) : ENNReal :=
  Pr[(fun matrix : Matrix (Fin dimension) (Fin dimension) F ↦
      matrix.rank < dimension) |
    ($ᵗ Matrix (Fin dimension) (Fin dimension) F)]

/-- The conditioning loss is exactly the standard square-matrix rank-failure product. -/
theorem squareTailFailureProbability_toReal_eq
    (F : Type) [Field F] [Fintype F] [SampleableType F] (dimension : ℕ) :
    (squareTailFailureProbability F dimension).toReal =
      1 - ∏ i : Fin dimension,
        (1 - (Fintype.card F : ℝ) ^ i.val /
          (Fintype.card F : ℝ) ^ dimension) := by
  exact FormalProof4FHE.FiniteFieldRank.rankFailure_toReal_eq
    dimension dimension le_rfl

/-- A convenient checked upper bound on the square-tail conditioning loss. -/
theorem squareTailFailureProbability_le_two_div_card
    (F : Type) [Field F] [Fintype F] [SampleableType F] (dimension : ℕ) :
    squareTailFailureProbability F dimension ≤
      2 / (Fintype.card F : ENNReal) := by
  simpa [squareTailFailureProbability] using
    (FormalProof4FHE.FiniteFieldRank.rankFailure_le (F := F) dimension 0)

/-- The manuscript's sharper geometric-series bound on the real-valued singular-tail
probability. -/
theorem squareTailFailureProbability_toReal_le_inv_card_sub_one
    (F : Type) [Field F] [Fintype F] [SampleableType F] (dimension : ℕ) :
    (squareTailFailureProbability F dimension).toReal ≤
      ((Fintype.card F : ℝ) - 1)⁻¹ := by
  have hRank := FormalProof4FHE.FiniteFieldRank.rankFailure_toReal_le_sum
    (F := F) dimension dimension le_rfl
  apply hRank.trans
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ (Fintype.card F : ℝ) ^ i /
      (Fintype.card F : ℝ) ^ dimension) dimension, ← Finset.sum_div]
  have hCard : (1 : ℝ) < Fintype.card F := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  have hCardPos : (0 : ℝ) < Fintype.card F := lt_trans (by norm_num) hCard
  have hPowPos : (0 : ℝ) < (Fintype.card F : ℝ) ^ dimension :=
    pow_pos hCardPos dimension
  have hSubPos : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := sub_pos.mpr hCard
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hPowPos hSubPos).2
  have hGeom := geom_sum_mul (Fintype.card F : ℝ) dimension
  nlinarith [pow_pos hCardPos dimension]

end RankFailure

/-! ## Corrected black-box theorem interfaces -/

/-- Proof-carrying finite bound supplied by a correctly instantiated general-distribution HNF
theorem.  The separate M-SIS field records the second-preimage premise present in the cited
result. -/
structure GeneralDistributionHNFReduction where
  hnfOneWayBound : ℝ
  decisionMLWEBound : ℝ
  moduleSISBound : ℝ
  statisticalLoss : ℝ
  bound_nonneg : 0 ≤ hnfOneWayBound
  decisionMLWE_nonneg : 0 ≤ decisionMLWEBound
  moduleSIS_nonneg : 0 ≤ moduleSISBound
  statisticalLoss_nonneg : 0 ≤ statisticalLoss
  reduces :
    hnfOneWayBound ≤ decisionMLWEBound + moduleSISBound + statisticalLoss

/-- Proof-carrying interface for the actual number-ring one-wayness-to-pseudorandomness step.
`mediumFoldWitness` is intentionally present: it is an explicit hypothesis of Mandal--Singh
Theorem 3.1 and is not implied by one-wayness or by trivial small folds. -/
structure NumberRingKnapsackReduction (Fold : Type) where
  knapsackOneWayBound : ℝ
  knapsackPseudorandomBound : ℝ
  foldAdvantage : Fold → ℝ
  mediumFold : Fold
  mediumFoldWitness : 0 < foldAdvantage mediumFold
  knapsackOneWay_nonneg : 0 ≤ knapsackOneWayBound
  knapsackPseudorandom_nonneg : 0 ≤ knapsackPseudorandomBound

/-- If unit-fold reasoning makes every relevant folded game statistically identical to uniform,
the positive medium-fold witness required by the cited theorem cannot exist. -/
theorem no_numberRingReduction_of_all_fold_advantages_zero
    {Fold : Type} (certificate : NumberRingKnapsackReduction Fold)
    (hUnitFold : ∀ fold, certificate.foldAdvantage fold = 0) : False := by
  have hZero := hUnitFold certificate.mediumFold
  linarith [certificate.mediumFoldWitness]

/-- More abstractly, no family of zero distinguishing advantages has a positive witness. -/
theorem not_exists_positive_of_all_eq_zero
    {Fold : Type} (advantage : Fold → ℝ)
    (hzero : ∀ fold, advantage fold = 0) :
    ¬ ∃ fold, 0 < advantage fold := by
  rintro ⟨fold, hpositive⟩
  rw [hzero fold] at hpositive
  exact lt_irrefl 0 hpositive

/-- Arithmetic composition of a corrected HNF/knapsack proof.  Unlike the manuscript's claimed
endpoint, the result visibly retains the M-SIS, statistical, conditioning, and folded-knapsack
terms required by the imported theorems. -/
theorem corrected_hnfPseudorandomBound
    (generalDistribution : GeneralDistributionHNFReduction)
    (hnfToKnapsackLoss knapsackToHNFLoss foldedLoss : ℝ)
    (knapsackOneWayBound knapsackPseudorandomBound hnfPseudorandomBound : ℝ)
    (hHNFToKnapsack :
      knapsackOneWayBound ≤
        generalDistribution.hnfOneWayBound + hnfToKnapsackLoss)
    (hNumberRing :
      knapsackPseudorandomBound ≤ knapsackOneWayBound + foldedLoss)
    (hKnapsackToHNF :
      hnfPseudorandomBound ≤ knapsackPseudorandomBound + knapsackToHNFLoss) :
    hnfPseudorandomBound ≤
      generalDistribution.decisionMLWEBound +
        generalDistribution.moduleSISBound +
        generalDistribution.statisticalLoss +
        hnfToKnapsackLoss + foldedLoss + knapsackToHNFLoss := by
  linarith [generalDistribution.reduces]

/-- The manuscript's desired standard-assumption-only numerical conclusion follows only after
additional theorems absorb the M-SIS, statistical, and fold terms into the claimed bound.  This
lemma makes those additional proof obligations explicit. -/
theorem hnfPseudorandomBound_le_standard_of_absorption
    (generalDistribution : GeneralDistributionHNFReduction)
    (hnfToKnapsackLoss knapsackToHNFLoss foldedLoss : ℝ)
    (knapsackOneWayBound knapsackPseudorandomBound hnfPseudorandomBound standardBound : ℝ)
    (hHNFToKnapsack :
      knapsackOneWayBound ≤
        generalDistribution.hnfOneWayBound + hnfToKnapsackLoss)
    (hNumberRing :
      knapsackPseudorandomBound ≤ knapsackOneWayBound + foldedLoss)
    (hKnapsackToHNF :
      hnfPseudorandomBound ≤ knapsackPseudorandomBound + knapsackToHNFLoss)
    (hAbsorb :
      generalDistribution.decisionMLWEBound +
          generalDistribution.moduleSISBound +
          generalDistribution.statisticalLoss +
          hnfToKnapsackLoss + foldedLoss + knapsackToHNFLoss ≤
        standardBound) :
    hnfPseudorandomBound ≤ standardBound := by
  exact (corrected_hnfPseudorandomBound generalDistribution hnfToKnapsackLoss
    knapsackToHNFLoss foldedLoss knapsackOneWayBound knapsackPseudorandomBound
    hnfPseudorandomBound hHNFToKnapsack hNumberRing hKnapsackToHNF).trans hAbsorb

/-- Corrected finite BFV theorem obtained by composing the exact adjacent-difference hybrid with
the proof-carrying HNF/knapsack bounds.  The conclusion displays every term omitted by the
manuscript's `standard search M-LWE only` claim. -/
theorem stockKDMAdvantage_le_corrected_standard_terms
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (radix : R)
    (secretSampler : ProbComp R) (errorSampler : ProbComp (BFV.Batch R levels))
    (adversary : BFV.Distinguisher R levels)
    (generalDistribution : GeneralDistributionHNFReduction)
    (hnfToKnapsackLoss knapsackToHNFLoss foldedLoss : ℝ)
    (knapsackOneWayBound knapsackPseudorandomBound hnfPseudorandomBound
      ordinaryRLWEBound : ℝ)
    (hHNFToKnapsack :
      knapsackOneWayBound ≤
        generalDistribution.hnfOneWayBound + hnfToKnapsackLoss)
    (hNumberRing :
      knapsackPseudorandomBound ≤ knapsackOneWayBound + foldedLoss)
    (hKnapsackToHNF :
      hnfPseudorandomBound ≤ knapsackPseudorandomBound + knapsackToHNFLoss)
    (hRealHNF :
      BFV.correlatedHNFAdvantage levels radix secretSampler errorSampler
          (BFV.reverseDistinguisher levels radix adversary) ≤
        hnfPseudorandomBound)
    (hZeroRLWE :
      BFV.zeroUniformAdvantage levels secretSampler errorSampler adversary ≤
        ordinaryRLWEBound) :
    BFV.stockKDMAdvantage levels radix secretSampler errorSampler adversary ≤
      generalDistribution.decisionMLWEBound +
        generalDistribution.moduleSISBound +
        generalDistribution.statisticalLoss +
        hnfToKnapsackLoss + foldedLoss + knapsackToHNFLoss + ordinaryRLWEBound := by
  have hHybrid := BFV.stockKDMAdvantage_le_correlatedHNF_add_zero
    levels radix secretSampler errorSampler adversary
  have hHNF := corrected_hnfPseudorandomBound generalDistribution hnfToKnapsackLoss
    knapsackToHNFLoss foldedLoss knapsackOneWayBound knapsackPseudorandomBound
    hnfPseudorandomBound hHNFToKnapsack hNumberRing hKnapsackToHNF
  linarith

end

end FormalProof4FHE.RLWE.BFVStandardAssumptionCircularSecurity
