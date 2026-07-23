/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialGrowingNoiseEndToEnd
import FormalProof4FHE.TFHE.NativeDiagonalPairBinaryRank
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Constant Paired-Rank Tail in the Growing-Noise TFHE Family

The concrete growing-noise family has ring rank one and six gadget levels, hence exactly twelve
TGSW rows.  At exact capacity and even base, the paired binary residue matrix used by the direct
diagonal collision route is therefore a uniform `24 × 12` matrix over `ZMod 2` at every security
parameter.

This module records that specialization exactly.  Its rank-failure probability is a single fixed
finite-field constant, is at least `2⁻²⁴`, and is consequently not negligible in the security
parameter.  This is an obstruction only to treating residue full-rank failure itself as a
negligible loss.  It does not rule out a sharper higher-adic image calculation or direct use of
the exact retained-fiber collision sum.
-/

open Matrix OracleComp Filter Topology
open scoped ENNReal

namespace FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd

open Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView
open Native.ShiftedCandidateEvaluator.DiagonalNormalForm

/-- The paired residue matrix of the concrete rank-one, six-level family. -/
abbrev PairedBinaryMatrix := Matrix (Fin 24) (Fin 12) (ZMod 2)

/-- Rank-failure probability actually induced by the concrete difference-pair sampler. -/
noncomputable def pairedBinaryRankFailure (securityParameter : ℕ) : ℝ≥0∞ :=
  Pr[(fun matrix : PairedBinaryMatrix ↦ matrix.rank < 12) |
    differencePairBinaryTransposeSampler
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (decomposition securityParameter)]

/-- The parameter-independent uniform `24 × 12` binary rank tail. -/
noncomputable def fixedPairedBinaryRankFailure : ℝ≥0∞ :=
  Pr[(fun matrix : PairedBinaryMatrix ↦ matrix.rank < 12) |
    ($ᵗ PairedBinaryMatrix)]

@[simp]
theorem decomposition_levels (securityParameter : ℕ) :
    (decomposition securityParameter).levels = 6 := rfl

@[simp]
theorem paired_tgsw_rowCount (securityParameter : ℕ) :
    TGSW.rowCount 1 (decomposition securityParameter).levels = 12 := by
  rfl

/-- The concrete modulus is exactly the sixth power of the decomposition base. -/
theorem decomposition_exactCapacity (securityParameter : ℕ) :
    coefficientModulus securityParameter =
      (decomposition securityParameter).base ^
        (decomposition securityParameter).levels := by
  simp [coefficientModulus, decomposition]
  ring

/-- Every security parameter induces the same uniform `24 × 12` binary matrix law. -/
theorem pairedBinaryRankFailure_eq_fixed (securityParameter : ℕ) :
    pairedBinaryRankFailure securityParameter = fixedPairedBinaryRankFailure := by
  letI : NeZero (ringDegree securityParameter) :=
    ⟨Nat.ne_of_gt (ringDegree_pos securityParameter)⟩
  unfold pairedBinaryRankFailure fixedPairedBinaryRankFailure
  apply probEvent_congr' (fun _ _ ↦ Iff.rfl)
  exact differencePairBinaryTransposeSampler_uniform_evalDist
    (decomposition securityParameter)
    (decomposition_exactCapacity securityParameter)
    (ringDegree securityParameter)
    (by simp [decomposition, Nat.mul_comm])

/-- Exact finite-field formula for the constant rank tail. -/
theorem fixedPairedBinaryRankFailure_exact :
    fixedPairedBinaryRankFailure =
      ((2 ^ (24 * 12) - ∏ i : Fin 12, (2 ^ 24 - 2 ^ i.val) : ℕ) : ℝ≥0∞) /
        (2 ^ (24 * 12) : ℕ) := by
  simpa only [fixedPairedBinaryRankFailure, ZMod.card] using
    (FormalProof4FHE.FiniteFieldRank.rankFailure_exact
      (F := ZMod 2) 24 12 (by norm_num))

/-- The zero-first-column event supplies a positive, parameter-independent lower bound. -/
theorem fixedPairedBinaryRankFailure_ge :
    ((2 : ℝ≥0∞) ^ 24)⁻¹ ≤ fixedPairedBinaryRankFailure := by
  simpa only [fixedPairedBinaryRankFailure, ZMod.card, Nat.cast_ofNat] using
    (FormalProof4FHE.FiniteFieldRank.rankFailure_ge_inv_card_pow_rows
      (F := ZMod 2) 24 12 (by norm_num) (by norm_num))

/-- The concrete paired rank tail is uniformly bounded below by `2⁻²⁴`. -/
theorem pairedBinaryRankFailure_ge (securityParameter : ℕ) :
    ((2 : ℝ≥0∞) ^ 24)⁻¹ ≤ pairedBinaryRankFailure securityParameter := by
  rw [pairedBinaryRankFailure_eq_fixed]
  exact fixedPairedBinaryRankFailure_ge

/-- Because the number of TGSW rows is fixed at twelve, the residue-rank failure term is not a
negligible function of the security parameter. -/
theorem pairedBinaryRankFailure_not_negligible :
    ¬ negligible pairedBinaryRankFailure := by
  intro hnegligible
  have htendsto : Tendsto pairedBinaryRankFailure atTop (𝓝 0) := by
    simpa [negligible, Asymptotics.SuperpolynomialDecay] using hnegligible 0
  have hconstant : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞) ^ 24)⁻¹ := by
    norm_num
  have heventually : ∀ᶠ securityParameter in atTop,
      pairedBinaryRankFailure securityParameter < ((2 : ℝ≥0∞) ^ 24)⁻¹ :=
    (tendsto_order.1 htendsto).2 _ hconstant
  obtain ⟨securityParameter, hsmall⟩ := heventually.exists
  exact (not_lt_of_ge (pairedBinaryRankFailure_ge securityParameter)) hsmall

/-- The exact cyclotomic-RLWE end-to-end theorem and the paired-rank obstruction coexist.  The
former remains conditional on native auxiliary-input CircLWE and the displayed ordinary
post-cut assumptions; the latter proves that residue full-rank failure cannot discharge that
circular premise for this fixed-level family. -/
theorem
    secureAgainst_and_refreshCorrect_and_pairedRankObstruction_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (postCutCyclotomicIsPPT : PostCutCyclotomicRLWEAdversaryFamily → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealPostCutCyclotomicClosed : ∀ adversary, isPPT adversary →
      postCutCyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction
          (realRingBatchReduction family.parameters adversary)))
    (hZeroPostCutCyclotomicClosed : ∀ adversary, isPPT adversary →
      postCutCyclotomicIsPPT
        (postCutBinaryToCyclotomicReduction
          (zeroRingBatchReduction family.parameters adversary)))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hPostCutCyclotomic :
      postCutCyclotomicRLWESecurityGame.secureAgainst postCutCyclotomicIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    ((Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT ∧
        RefreshCorrect) ∧
      ¬ negligible pairedBinaryRankFailure := by
  constructor
  · exact secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE
      isPPT nativeCircularIsPPT ordinarySearchIsPPT postCutCyclotomicIsPPT
      inputBatchIsPPT hNativeCircularClosed hOrdinarySearchClosed
      hRealPostCutCyclotomicClosed hZeroPostCutCyclotomicClosed hInputBatchClosed
      hNativeCircular hOrdinarySearch hPostCutCyclotomic hInputBatch
  · exact pairedBinaryRankFailure_not_negligible

end FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd
