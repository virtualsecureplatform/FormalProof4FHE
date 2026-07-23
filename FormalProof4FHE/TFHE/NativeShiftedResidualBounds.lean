/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.NoiseBounds

/-!
# Quantitative Bounds for the Native Shifted-Candidate Residual

The correct shifted-candidate CMux residual is already known exactly: one retained source-row
error plus one digit-weighted external-product error of the zero-message candidate control.  This
file converts that identity into a deterministic centered-coefficient infinity-norm budget for
the executable base digitizer.

The bound is deliberately conservative and uses the checked `N²` negacyclic-convolution estimate
from `TFHE.NoiseBounds`.  It is nevertheless construction-specific: exact gadget decomposition
has zero cost, the executable digit bound is `base - 1`, and every remaining factor is explicit.
-/

open Matrix

namespace FormalProof4FHE.TFHE.Native.ShiftedResidualBounds

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-! ## Secret-bit toggling preserves row-error size -/

/-- Negating every component of a TGSW ciphertext negates its complete vector of TLWE phases. -/
theorem batchPhase_negateCiphertext {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TLWE.batchPhase secret
        (ScalarSecretRandomization.negateCiphertext ciphertext) =
      -TLWE.batchPhase secret ciphertext := by
  funext row
  simp [TLWE.batchPhase, ScalarSecretRandomization.negateCiphertext,
    Matrix.vecMul, dotProduct]
  abel

/-- Toggling a TGSW ciphertext by a bit preserves every row error up to the public sign selected
by that bit.  The identity holds for arbitrary ciphertexts; no structured-encryption normal form
is needed. -/
theorem rowError_toggleTGSW {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (bit mask : Bool) (ciphertext : TGSW.Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) :
    TGSW.rowError secret gadget
        (embedBit (LWE.MultiKeyAffine.maskedBit bit mask))
        (ScalarSecretRandomization.toggleTGSW gadget mask ciphertext) index =
      if mask then
        -TGSW.rowError secret gadget (embedBit bit) ciphertext index
      else TGSW.rowError secret gadget (embedBit bit) ciphertext index := by
  cases mask with
  | false =>
      simp [ScalarSecretRandomization.toggleTGSW,
        LWE.MultiKeyAffine.maskedBit]
  | true =>
      simp only [ScalarSecretRandomization.toggleTGSW, if_true]
      unfold TGSW.rowError
      rw [TLWE.phase_entry, TGSW.batchPhase_addGadget,
        batchPhase_negateCiphertext]
      rw [TLWE.phase_entry]
      simp only [Pi.add_apply, Pi.neg_apply]
      have hzero : TGSW.gadgetPhase secret gadget (0 : R)
          (finProdFinEquiv index) = 0 := by
        simpa using (TGSW.gadgetPhase_sub secret gadget
          (0 : R) 0 (finProdFinEquiv index)).symm
      cases bit with
      | false =>
          simp [LWE.MultiKeyAffine.maskedBit, embedBit, hzero]
      | true =>
          simp [LWE.MultiKeyAffine.maskedBit, embedBit, hzero]
          abel

/-- For the correct candidate, the toggled control encrypts zero and its row error is exactly the
source row error up to proof-facing negation. -/
theorem rowError_candidateControl_correct
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : Bool)
    (ciphertext : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    TGSW.rowError secret (Gadget.Base.ringGadget params)
        ShiftedCandidateEvaluator.proofZero
        (ShiftedCandidateEvaluator.candidateControl params hidden ciphertext) index =
      if hidden then
        ShiftedCandidateEvaluator.proofNeg
          (TGSW.rowError secret (Gadget.Base.ringGadget params)
            (embedBit hidden) ciphertext index)
      else
        TGSW.rowError secret (Gadget.Base.ringGadget params)
          (embedBit hidden) ciphertext index := by
  rw [ShiftedCandidateEvaluator.proofZero_eq_zero]
  simpa [ShiftedCandidateEvaluator.candidateControl,
      ShiftedCandidateEvaluator.maskedBit_self,
      ShiftedCandidateEvaluator.proofNeg, embedBit] using
    rowError_toggleTGSW secret (Gadget.Base.ringGadget params)
      hidden hidden ciphertext index

/-- The proof-facing negation used by the shifted evaluator preserves the executable centered
coefficient infinity norm. -/
@[simp]
theorem cInfNorm_proofNeg
    {q degree : ℕ} [NeZero q] (value : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm (ShiftedCandidateEvaluator.proofNeg value) =
      LatticeCrypto.cInfNorm value := by
  calc
    LatticeCrypto.cInfNorm (ShiftedCandidateEvaluator.proofNeg value) =
        LatticeCrypto.cInfNorm (-value) :=
      congrArg LatticeCrypto.cInfNorm
        (ShiftedCandidateEvaluator.proofNeg_eq_neg value)
    _ = LatticeCrypto.cInfNorm value := LatticeCrypto.cInfNorm_neg value

/-- Consequently, a bound for the original secret-bit row also bounds every row of its
zero-message correct-candidate control. -/
theorem cInfNorm_candidateControl_correct_le
    {q degree ringRank lweDimension eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension) (coordinate : Fin lweDimension)
    (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (hsource : ∀ index : Fin (ringRank + 1) × Fin params.levels,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) (embedBit (hidden coordinate))
          (source coordinate) index) ≤ eta) :
    ∀ index : Fin (ringRank + 1) × Fin params.levels,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) ShiftedCandidateEvaluator.proofZero
          (ShiftedCandidateEvaluator.candidateControl params
            (hidden coordinate) (source coordinate)) index) ≤ eta := by
  intro index
  rw [rowError_candidateControl_correct params secret (hidden coordinate)
    (source coordinate) index]
  split_ifs
  · simpa only [cInfNorm_proofNeg] using hsource index
  · exact hsource index

/-- Worst-case norm budget for one row of the correct shifted-candidate BRK residual. -/
def correctResidualBound {q : ℕ} (params : Gadget.Base.Parameters q)
    (ringDegree ringRank sourceRowErrorBound controlRowErrorBound : ℕ) : ℕ :=
  sourceRowErrorBound +
    ((ringRank + 1) * params.levels) *
      ((ringDegree * ringDegree) * ((params.base - 1) * controlRowErrorBound))

/-- If the retained source row and every zero-control row have the stated norm bounds, then the
actual executable correct residual satisfies `correctResidualBound`. -/
theorem cInfNorm_correctBootstrappingResidual_le
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels)
    (sourceRowErrorBound controlRowErrorBound : ℕ)
    (hsource : LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
        (source outputCoordinate) index) ≤ sourceRowErrorBound)
    (hcontrol : ∀ controlIndex, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params)
        ShiftedCandidateEvaluator.proofZero
        (ShiftedCandidateEvaluator.candidateControl params
          (hidden coordinate) (source coordinate)) controlIndex) ≤
      controlRowErrorBound) :
    LatticeCrypto.cInfNorm
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch outputCoordinate (finProdFinEquiv index)) ≤
      correctResidualBound params (degree + 1) ringRank
        sourceRowErrorBound controlRowErrorBound := by
  rw [ShiftedCandidateEvaluator.correctBootstrappingResidual_eq_rowError_add_externalProductError]
  change LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
          (source outputCoordinate) index +
        TGSW.externalProductError secret (Gadget.Base.ringGadget params)
          ShiftedCandidateEvaluator.proofZero
          (ShiftedCandidateEvaluator.differenceDigits params
            (trueBranch outputCoordinate) (source outputCoordinate)
            (finProdFinEquiv index))
          (ShiftedCandidateEvaluator.candidateControl params
            (hidden coordinate) (source coordinate))) ≤ _
  refine (NoiseBounds.cInfNorm_add_le _ _).trans (Nat.add_le_add hsource ?_)
  simpa only [correctResidualBound, ShiftedCandidateEvaluator.differenceDigits] using
    (NoiseBounds.cInfNorm_externalProductError_ringDigits_le params secret
      ShiftedCandidateEvaluator.proofZero
      (TLWE.entry (TGSW.sub (trueBranch outputCoordinate)
        (source outputCoordinate)) (finProdFinEquiv index))
      (ShiftedCandidateEvaluator.candidateControl params
        (hidden coordinate) (source coordinate))
      controlRowErrorBound hcontrol)

/-- Centered-binomial specialization when both source and zero-control row errors are bounded by
the same support width `eta`. -/
def centeredBinomialResidualBound {q : ℕ} (params : Gadget.Base.Parameters q)
    (ringDegree ringRank eta : ℕ) : ℕ :=
  correctResidualBound params ringDegree ringRank eta eta

/-- Pointwise fallback budget when the proof boundary compares the public source against an
independently sampled scalar and ring secret.  Every modular polynomial has centered infinity
norm at most `q / 2`, so this bound requires no coupling or support hypothesis. -/
def universalResidualBound {q : ℕ} (params : Gadget.Base.Parameters q)
    (ringDegree ringRank : ℕ) : ℕ :=
  correctResidualBound params ringDegree ringRank (q / 2) (q / 2)

/-- Equal source/control row bounds instantiate the centered-binomial residual budget directly. -/
theorem cInfNorm_correctBootstrappingResidual_le_centeredBinomialBound
    {q degree ringRank lweDimension eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels)
    (hsource : LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params) (embedBit (hidden outputCoordinate))
        (source outputCoordinate) index) ≤ eta)
    (hcontrol : ∀ controlIndex, LatticeCrypto.cInfNorm
      (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
        (Gadget.Base.ringGadget params)
        ShiftedCandidateEvaluator.proofZero
        (ShiftedCandidateEvaluator.candidateControl params
          (hidden coordinate) (source coordinate)) controlIndex) ≤ eta) :
    LatticeCrypto.cInfNorm
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch outputCoordinate (finProdFinEquiv index)) ≤
      centeredBinomialResidualBound params (degree + 1) ringRank eta := by
  exact cInfNorm_correctBootstrappingResidual_le params secret hidden coordinate
    outputCoordinate source trueBranch index eta eta hsource hcontrol

/-- A uniform bound on the transported source BRK alone suffices: correct-candidate toggling
derives the zero-control row bound without a second probabilistic support obligation. -/
theorem cInfNorm_correctBootstrappingResidual_le_centeredBinomialBound_of_source
    {q degree ringRank lweDimension eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels)
    (hsource : ∀ sourceCoordinate sourceIndex,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) secret
          (Gadget.Base.ringGadget params) (embedBit (hidden sourceCoordinate))
          (source sourceCoordinate) sourceIndex) ≤ eta) :
    LatticeCrypto.cInfNorm
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch outputCoordinate (finProdFinEquiv index)) ≤
      centeredBinomialResidualBound params (degree + 1) ringRank eta := by
  exact cInfNorm_correctBootstrappingResidual_le_centeredBinomialBound
    params secret hidden coordinate outputCoordinate source trueBranch index
    (hsource outputCoordinate index)
    (cInfNorm_candidateControl_correct_le params secret hidden coordinate source
      (hsource coordinate))

/-- The complete correct residual is always bounded pointwise, even when the target scalar and
ring secrets are independent of the source BRK.  This conservative fallback is the sound bound
consumed by the present fresh-secret sampled-residual interface. -/
theorem cInfNorm_correctBootstrappingResidual_le_universalBound
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source trueBranch :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels) :
    LatticeCrypto.cInfNorm
        (ShiftedCandidateEvaluator.correctBootstrappingResidual params secret hidden
          coordinate source trueBranch outputCoordinate (finProdFinEquiv index)) ≤
      universalResidualBound params (degree + 1) ringRank := by
  exact cInfNorm_correctBootstrappingResidual_le params secret hidden coordinate
    outputCoordinate source trueBranch index (q / 2) (q / 2)
    (LatticeCrypto.cInfNorm_le_halfq _)
    (fun _ ↦ LatticeCrypto.cInfNorm_le_halfq _)

end

end FormalProof4FHE.TFHE.Native.ShiftedResidualBounds
