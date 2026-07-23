/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.LeftoverHash
import FormalProof4FHE.TFHE.NativeAdaptiveOffDiagonalSecurity

/-!
# Fiber Bounds for the Native TFHE Wrong-Control Map

The normalized wrong-control row map is identity plus the external product of the row's exact
base digits with the homogeneous part of one generated message-one TRGSW control.  Digit
decomposition makes this map nonlinear, and the production coefficient ring `ZMod q` need not
be a field.  Consequently a finite-field rank argument is not a sound generic way to analyze
this map.

This module instead uses the exact fibers of the deterministic map on the finite TLWE row
space.  Their second moment controls the image of a uniform row by a standard collision
argument over arbitrary finite types.  The resulting expected loss is lifted through the
existing whole-BRK and whole-key certificate interfaces.  No linearity, field structure, or
pointwise bijectivity is assumed.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

variable {q degree ringRank : ℕ}

/-- Finite state space on which one normalized message-one control acts. -/
abbrev MessageOneRow (q degree ringRank : ℕ) :=
  TLWE.Ciphertext (RLWE.Rq q degree) ringRank

noncomputable local instance messageOneRowFintype (q degree ringRank : ℕ) [NeZero q] :
    Fintype (MessageOneRow q degree ringRank) :=
  Fintype.ofEquiv
    ((Fin ringRank → RLWE.Rq q degree) × RLWE.Rq q degree)
    (Native.ShiftedCandidateEvaluator.tlweCiphertextEquiv
      (RLWE.Rq q degree) ringRank)

noncomputable local instance messageOneRowSampleableType
    (q degree ringRank : ℕ) [NeZero q] :
    SampleableType (MessageOneRow q degree ringRank) :=
  SampleableType.ofEquiv
    (Native.ShiftedCandidateEvaluator.tlweCiphertextEquiv
      (RLWE.Rq q degree) ringRank)

/-- Cardinality of the normalized TLWE row space. -/
noncomputable def messageOneRowCard (q degree ringRank : ℕ) [NeZero q] : ℝ :=
  Fintype.card (MessageOneRow q degree ringRank)

/-- Fiber-size second moment of the concrete identity-plus-digit map selected by a fixed
message-one control. -/
noncomputable def messageOneControlFiberSecondMoment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  FormalProof4FHE.LeftoverHash.fiberSecondMoment
    (Native.ShiftedCandidateEvaluator.oneMessageRowTransform params false control)

/-- Exact collision/fiber upper bound for the normalized defect of a fixed message-one
control. -/
noncomputable def messageOneControlFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  Real.sqrt
      (messageOneControlFiberSecondMoment params control /
          messageOneRowCard q degree ringRank - 1) /
    2

/-- The collision bound capped by the universal unit bound on total-variation distance.
This cap is important when averaging: a rare control with a very large fiber may contribute at
most its probability, rather than its uncapped square-root fiber estimate. -/
noncomputable def messageOneControlCappedFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  min 1 (messageOneControlFiberLoss params control)

/-- Expected exact fiber loss under the canonical generated message-one control law. -/
noncomputable def averagedCanonicalMessageOneControlFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) : ℝ :=
  ∑' control : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= control |
      canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
        params eta].toReal *
      messageOneControlFiberLoss (degree := degree + 1) params control

/-- Expected capped fiber loss under the canonical generated message-one control law. -/
noncomputable def averagedCanonicalMessageOneControlCappedFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) : ℝ :=
  ∑' control : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= control |
      canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
        params eta].toReal *
      messageOneControlCappedFiberLoss (degree := degree + 1) params control

/-- The direct one-row statistical defect is bounded by the exact relative fiber-second-moment
excess of the production identity-plus-digit map. -/
theorem messageOneControlDistance_le_fiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    messageOneControlDistance params control ≤
      messageOneControlFiberLoss params control := by
  have h := FormalProof4FHE.LeftoverHash.tvDist_map_uniform_le_sqrt_fiberExcess
    (Native.ShiftedCandidateEvaluator.oneMessageRowTransform params false control)
  unfold messageOneControlDistance
    Native.ShiftedCandidateEvaluator.controlBranchDistance
    messageOneControlFiberLoss messageOneControlFiberSecondMoment messageOneRowCard
  rw [Native.ShiftedCandidateEvaluator.controlBranchTransform_eq_oneMessageRowTransform]
  exact h

/-- The exact one-row defect is bounded simultaneously by one and by the collision estimate. -/
theorem messageOneControlDistance_le_cappedFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    messageOneControlDistance params control ≤
      messageOneControlCappedFiberLoss params control := by
  unfold messageOneControlCappedFiberLoss
  apply le_min
  · exact tvDist_le_one _ _
  · exact messageOneControlDistance_le_fiberLoss params control

theorem messageOneControlFiberLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    0 ≤ messageOneControlFiberLoss params control := by
  unfold messageOneControlFiberLoss
  positivity

theorem messageOneControlCappedFiberLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    0 ≤ messageOneControlCappedFiberLoss params control := by
  unfold messageOneControlCappedFiberLoss
  exact le_min (by norm_num) (messageOneControlFiberLoss_nonneg params control)

/-- A concrete second-moment estimate for one fixed control yields the familiar
`sqrt ε / 2` distance bound. -/
theorem messageOneControlDistance_le_of_fiberSecondMoment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) (ε : ℝ)
    (hsecond : messageOneControlFiberSecondMoment params control ≤
      messageOneRowCard q degree ringRank * (1 + ε)) :
    messageOneControlDistance params control ≤ Real.sqrt ε / 2 := by
  have h := FormalProof4FHE.LeftoverHash.tvDist_map_uniform_le_of_fiberSecondMoment
    (Native.ShiftedCandidateEvaluator.oneMessageRowTransform params false control) ε
    (by simpa [messageOneControlFiberSecondMoment, messageOneRowCard] using hsecond)
  unfold messageOneControlDistance
    Native.ShiftedCandidateEvaluator.controlBranchDistance
  rw [Native.ShiftedCandidateEvaluator.controlBranchTransform_eq_oneMessageRowTransform]
  exact h

/-- The raw square-root fiber estimate itself obeys the same `sqrt ε / 2` bound under a
second-moment hypothesis. -/
theorem messageOneControlFiberLoss_le_of_fiberSecondMoment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) (ε : ℝ)
    (hsecond : messageOneControlFiberSecondMoment params control ≤
      messageOneRowCard q degree ringRank * (1 + ε)) :
    messageOneControlFiberLoss params control ≤ Real.sqrt ε / 2 := by
  have hcard : 0 < messageOneRowCard q degree ringRank := by
    unfold messageOneRowCard
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (MessageOneRow q degree ringRank))
  have hexcess :
      messageOneControlFiberSecondMoment params control /
          messageOneRowCard q degree ringRank - 1 ≤ ε := by
    have hdiv :
        messageOneControlFiberSecondMoment params control /
            messageOneRowCard q degree ringRank ≤ 1 + ε := by
      apply (div_le_iff₀ hcard).2
      simpa [mul_comm] using hsecond
    linarith
  unfold messageOneControlFiberLoss
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hexcess) (by norm_num)

/-- Averaging over the nonuniform generated-control law preserves the pointwise fiber bound. -/
theorem averagedCanonicalMessageOneControlDistance_le_fiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) :
    averagedCanonicalMessageOneControlDistance (degree := degree)
        (ringRank := ringRank) params eta ≤
      averagedCanonicalMessageOneControlFiberLoss (degree := degree)
        (ringRank := ringRank) params eta := by
  unfold averagedCanonicalMessageOneControlDistance
    averagedCanonicalMessageOneControlFiberLoss
  apply Summable.tsum_le_tsum
  · intro control
    exact mul_le_mul_of_nonneg_left
      (messageOneControlDistance_le_fiberLoss params control)
      ENNReal.toReal_nonneg
  · exact Summable.of_finite
  · exact Summable.of_finite

/-- Averaging preserves the capped pointwise fiber bound. -/
theorem averagedCanonicalMessageOneControlDistance_le_cappedFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) :
    averagedCanonicalMessageOneControlDistance (degree := degree)
        (ringRank := ringRank) params eta ≤
      averagedCanonicalMessageOneControlCappedFiberLoss (degree := degree)
        (ringRank := ringRank) params eta := by
  unfold averagedCanonicalMessageOneControlDistance
    averagedCanonicalMessageOneControlCappedFiberLoss
  apply Summable.tsum_le_tsum
  · intro control
    exact mul_le_mul_of_nonneg_left
      (messageOneControlDistance_le_cappedFiberLoss params control)
      ENNReal.toReal_nonneg
  · exact Summable.of_finite
  · exact Summable.of_finite

theorem averagedCanonicalMessageOneControlCappedFiberLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) :
    0 ≤ averagedCanonicalMessageOneControlCappedFiberLoss (degree := degree)
      (ringRank := ringRank) params eta := by
  unfold averagedCanonicalMessageOneControlCappedFiberLoss
  exact tsum_nonneg fun control ↦
    mul_nonneg ENNReal.toReal_nonneg
      (messageOneControlCappedFiberLoss_nonneg params control)

/-- Split the generated-control average into controls satisfying an analytic fiber estimate and
a bad event.  On bad controls the cap charges only one, so their entire contribution is exactly
bounded by their probability. -/
theorem averagedCanonicalMessageOneControlCappedFiberLoss_le_good_add_badProbability
    [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ)
    (Good : RingGSWCiphertext q (degree + 1) ringRank params.levels → Prop)
    (goodError : ℝ) (goodError_nonneg : 0 ≤ goodError)
    (hgood : ∀ control ∈ support
      (canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
        params eta),
      Good control →
        messageOneControlCappedFiberLoss (degree := degree + 1) params control ≤
          goodError) :
    averagedCanonicalMessageOneControlCappedFiberLoss (degree := degree)
        (ringRank := ringRank) params eta ≤
      goodError +
        Pr[(fun control ↦ ¬ Good control) |
          canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
            params eta].toReal := by
  classical
  let Control := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let sampler : ProbComp Control :=
    canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
      params eta
  letI : Fintype Control := Fintype.ofFinite Control
  have hmass : (∑ control : Control, Pr[= control | sampler].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  have hbadMass :
      (∑ control : Control,
          if ¬ Good control then Pr[= control | sampler].toReal else 0) =
        Pr[(fun control ↦ ¬ Good control) | sampler].toReal := by
    rw [probEvent_eq_sum_fintype_ite, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro control _
      by_cases hcontrol : ¬ Good control <;> simp [hcontrol]
    · intro control _
      by_cases hcontrol : ¬ Good control
      · simp [hcontrol, probOutput_ne_top]
      · simp [hcontrol]
  unfold averagedCanonicalMessageOneControlCappedFiberLoss
  rw [tsum_fintype]
  calc
    ∑ control : Control,
        Pr[= control | sampler].toReal *
          messageOneControlCappedFiberLoss params control ≤
      ∑ control : Control,
        Pr[= control | sampler].toReal *
          (goodError + if ¬ Good control then 1 else 0) := by
        apply Finset.sum_le_sum
        intro control _
        by_cases hsupport : control ∈ support sampler
        · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          by_cases hcontrol : Good control
          · simpa [hcontrol] using
              hgood control (by simpa [sampler, Control] using hsupport) hcontrol
          · have hcap :
                messageOneControlCappedFiberLoss params control ≤ 1 :=
              min_le_left _ _
            simpa [hcontrol] using hcap.trans (by linarith)
        · have hzero : Pr[= control | sampler] = 0 :=
            probOutput_eq_zero_of_not_mem_support hsupport
          simp [hzero]
    _ = goodError +
        ∑ control : Control,
          if ¬ Good control then Pr[= control | sampler].toReal else 0 := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hconstant :
          (∑ control : Control, Pr[= control | sampler].toReal * goodError) =
            goodError := by
        rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      apply Finset.sum_congr rfl
      intro control _
      by_cases hcontrol : ¬ Good control <;> simp [hcontrol]
    _ = goodError + Pr[(fun control ↦ ¬ Good control) | sampler].toReal := by
      rw [hbadMass]

/-- A support-wise second-moment estimate on good controls plus the probability of its failure
gives a robust expected fiber bound. -/
theorem averagedCanonicalMessageOneControlCappedFiberLoss_le_of_goodFiberSecondMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ)
    (Good : RingGSWCiphertext q (degree + 1) ringRank params.levels → Prop)
    (ε : ℝ)
    (hsecond : ∀ control ∈ support
      (canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
        params eta),
      Good control →
        messageOneControlFiberSecondMoment (degree := degree + 1) params control ≤
          messageOneRowCard q (degree + 1) ringRank * (1 + ε)) :
    averagedCanonicalMessageOneControlCappedFiberLoss (degree := degree)
        (ringRank := ringRank) params eta ≤
      Real.sqrt ε / 2 +
        Pr[(fun control ↦ ¬ Good control) |
          canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
            params eta].toReal := by
  apply averagedCanonicalMessageOneControlCappedFiberLoss_le_good_add_badProbability
    params eta Good (Real.sqrt ε / 2) (by positivity)
  intro control hsupport hcontrol
  exact (min_le_right _ _).trans
    (messageOneControlFiberLoss_le_of_fiberSecondMoment params control ε
      (hsecond control hsupport hcontrol))

/-- A uniform fiber-second-moment estimate on the support of the generated-control law bounds
its expected one-row defect.  Controls outside the support carry zero weight. -/
theorem averagedCanonicalMessageOneControlDistance_le_of_fiberSecondMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) (ε : ℝ)
    (hsecond : ∀ control ∈ support
      (canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
        params eta),
      messageOneControlFiberSecondMoment (degree := degree + 1) params control ≤
        messageOneRowCard q (degree + 1) ringRank * (1 + ε)) :
    averagedCanonicalMessageOneControlDistance (degree := degree)
        (ringRank := ringRank) params eta ≤
      Real.sqrt ε / 2 := by
  let Control := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let sampler : ProbComp Control :=
    canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
      params eta
  letI : Fintype Control := Fintype.ofFinite Control
  have hmass : (∑ control : Control, Pr[= control | sampler].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold averagedCanonicalMessageOneControlDistance
  rw [tsum_fintype]
  calc
    ∑ control : Control,
        Pr[= control | sampler].toReal * messageOneControlDistance params control ≤
      ∑ control : Control, Pr[= control | sampler].toReal * (Real.sqrt ε / 2) := by
        apply Finset.sum_le_sum
        intro control _
        by_cases hcontrol : control ∈ support sampler
        · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          apply messageOneControlDistance_le_of_fiberSecondMoment params control ε
          exact hsecond control (by simpa [sampler, Control] using hcontrol)
        · have hzero : Pr[= control | sampler] = 0 :=
            probOutput_eq_zero_of_not_mem_support hcontrol
          simp [hzero]
    _ = (∑ control : Control, Pr[= control | sampler].toReal) *
        (Real.sqrt ε / 2) := by rw [Finset.sum_mul]
    _ = Real.sqrt ε / 2 := by rw [hmass, one_mul]

/-- Complete native wrong-view distance bounded by the number of transformed BRK data rows
times the expected fiber loss of one canonical generated message-one control. -/
theorem
    tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlFiberLoss (degree := degree)
          (ringRank := ringRank) params eta := by
  calc
    _ ≤ (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlDistance (degree := degree)
          (ringRank := ringRank) params eta :=
      tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlDistance
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (averagedCanonicalMessageOneControlDistance_le_fiberLoss
        (degree := degree) (ringRank := ringRank) params eta)
      (Nat.cast_nonneg _)

/-- Complete native wrong-view distance bounded by the row count times the expected capped fiber
loss.  Unlike the uncapped collision expression, an exceptional generated control contributes at
most its probability. -/
theorem
    tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlCappedFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlCappedFiberLoss (degree := degree)
          (ringRank := ringRank) params eta := by
  calc
    _ ≤ (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlDistance (degree := degree)
          (ringRank := ringRank) params eta :=
      tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlDistance
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (averagedCanonicalMessageOneControlDistance_le_cappedFiberLoss
        (degree := degree) (ringRank := ringRank) params eta)
      (Nat.cast_nonneg _)

namespace WholeKeyRankCertificate

/-- Build the whole-key statistical certificate from the capped expected fiber loss of the
nonlinear message-one map. -/
noncomputable def ofMessageOneControlCappedFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlCappedFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlCappedFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlDistance params targetRingErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget diagonalError offDiagonalError freshnessError
    diagonalError_nonneg offDiagonalError_nonneg freshnessError_nonneg
    diagonalDistance_le offDiagonalDistance_le (by
      exact
        (mul_le_mul_of_nonneg_left
          (averagedCanonicalMessageOneControlDistance_le_cappedFiberLoss
            (degree := degree) (ringRank := ringRank) params eta)
          (Nat.cast_nonneg _)).trans
        messageOneControlCappedFiberLoss_le)

/-- Build the whole-key statistical certificate from the exact expected fiber loss of the
nonlinear message-one map.  The premise can in turn be discharged by a direct fiber count or by
`averagedCanonicalMessageOneControlDistance_le_of_fiberSecondMoment`. -/
noncomputable def ofMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (diagonalError : Fin lweDimension → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (diagonalError_nonneg : ∀ coordinate, 0 ≤ diagonalError coordinate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (diagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret coordinate) ≤
          diagonalError coordinate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlDistance params targetRingErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget diagonalError offDiagonalError freshnessError
    diagonalError_nonneg offDiagonalError_nonneg freshnessError_nonneg
    diagonalDistance_le offDiagonalDistance_le (by
      exact
        (mul_le_mul_of_nonneg_left
          (averagedCanonicalMessageOneControlDistance_le_fiberLoss
            (degree := degree) (ringRank := ringRank) params eta)
          (Nat.cast_nonneg _)).trans
        messageOneControlFiberLoss_le)

end WholeKeyRankCertificate

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
