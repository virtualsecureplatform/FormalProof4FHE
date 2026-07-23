/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveCircularLWE
import FormalProof4FHE.TFHE.NativeShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSecretRandomizationDiscreteGaussian

set_option autoImplicit false

/-!
# Lifting Evaluation-Material Randomization to the Complete Adaptive TFHE View

The direct public FHE CircLWE view contains an input-ciphertext tape together with the source BRK
and source-to-target ring-extension table.  This file proves that the tape is not part of the
remaining shifted-evaluation obstruction.  Once the BRK/extension pair can be transported from a
nested secret to its coefficientwise XOR shift, the target-key tape follows by the exact public
scalar-secret transport, with no additional statistical loss and for an arbitrary scalar error
sampler.

Consequently the open native certificate is narrowed from the complete
`(tape, BRK, extension)` distribution to the evaluation material `(BRK, extension)` alone.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

/-- The scalar XOR mask induced on `KeyExtract(S_source || S_suffix)` by a nested ring mask. -/
def targetScalarMask
    {sourceRank suffixRank degree : ℕ}
    (mask : Mask sourceRank suffixRank degree) :
    BinarySecret (targetScalarDimension sourceRank suffixRank degree) :=
  targetMessages mask.1 mask.2

/-- Coefficientwise XOR of the two nested ring-key blocks is exactly coefficientwise XOR of the
extracted, concatenated scalar target key. -/
theorem targetMessages_act
    {sourceRank suffixRank degree : ℕ}
    (secret : Secret sourceRank suffixRank degree)
    (mask : Mask sourceRank suffixRank degree) :
    targetMessages (act secret mask).1 (act secret mask).2 =
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        (targetMessages secret.1 secret.2) (targetScalarMask mask) := by
  rcases secret with ⟨sourceSecret, suffixSecret⟩
  rcases mask with ⟨sourceMask, suffixMask⟩
  funext coordinate
  obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
  refine Fin.addCases ?_ ?_ component
  · intro sourceComponent
    simp [act, targetScalarMask, maskedRingSecret,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]
  · intro suffixComponent
    simp [act, targetScalarMask, maskedRingSecret,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]

/-! ## Exact target-tape transport -/

/-- Publicly transport every tape row to the scalar key induced by a nested XOR mask. -/
def transformTargetTape
    {q degree sourceRank suffixRank queryCount : ℕ}
    (mask : Mask sourceRank suffixRank degree)
    (tape : Challenge q degree sourceRank suffixRank queryCount) :
    Challenge q degree sourceRank suffixRank queryCount :=
  FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBatch
    (targetScalarMask mask) tape

/-- Fixed-secret target-key tape sampler, separated from the circular evaluation material. -/
def sampleTargetTape
    (q degree sourceRank suffixRank queryCount : ℕ) [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (secret : Secret sourceRank suffixRank degree) :
    ProbComp (Challenge q degree sourceRank suffixRank queryCount) :=
  TLWE.batchEncrypt (targetScalarDimension sourceRank suffixRank degree) queryCount
    inputErrorSampler (embedBinarySecret (targetMessages secret.1 secret.2)) 0

/-- Arbitrary nested coefficientwise XOR is an exact public transport of the complete target-key
tape.  Neither symmetry nor widening of the scalar error distribution is needed. -/
theorem transformTargetTape_sampleTargetTape_evalDist
    (q degree sourceRank suffixRank queryCount : ℕ) [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (secret : Secret sourceRank suffixRank degree)
    (mask : Mask sourceRank suffixRank degree) :
    evalDist (transformTargetTape mask <$>
        sampleTargetTape q degree sourceRank suffixRank queryCount inputErrorSampler secret) =
      evalDist (sampleTargetTape q degree sourceRank suffixRank queryCount inputErrorSampler
        (act secret mask)) := by
  unfold transformTargetTape sampleTargetTape
  rw [FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBatch_batchEncrypt_evalDist]
  rw [← targetMessages_act secret mask]

/-! ## Evaluation-material-only shifted evaluator -/

/-- Fixed-secret source BRK and ring-extension table, without the independent input tape. -/
def sampleEvaluationMaterial
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (secret : Secret sourceRank suffixRank degree) :
    ProbComp (Auxiliary q degree sourceRank suffixRank tgswLevels) := do
  let sourceBootstrappingKey ← generateSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels bootstrapErrorSampler gadget secret.1 secret.2
  let ringExtensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels extensionErrorSampler gadget secret.1 secret.2
  return (sourceBootstrappingKey, ringExtensionKey)

/-- The complete real view is the independent pairing of its tape and evaluation material once
the nested secret is fixed. -/
theorem sampleRealView_eq_independentPair
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (secret : Secret sourceRank suffixRank degree) :
    sampleRealView q degree sourceRank suffixRank tgswLevels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret =
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair
        (sampleTargetTape q degree sourceRank suffixRank queryCount inputErrorSampler secret)
        (sampleEvaluationMaterial q degree sourceRank suffixRank tgswLevels
          bootstrapErrorSampler extensionErrorSampler gadget secret)
        (fun tape auxiliary ↦ (tape, auxiliary)) := by
  simp [sampleRealView, problem, sampleTargetTape, sampleEvaluationMaterial,
    FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
    map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- The genuinely ring-specific certificate after removing the exactly transportable target tape.
It transforms only the source BRK and correlated ring-extension table. -/
structure ShiftedEvaluationMaterialEvaluator
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree) where
  evaluateAndSmudge :
    Mask sourceRank suffixRank degree →
      Auxiliary q degree sourceRank suffixRank tgswLevels →
        ProbComp (Auxiliary q degree sourceRank suffixRank tgswLevels)
  error : ℝ
  error_nonneg : 0 ≤ error
  materialDistance_le : ∀ secret mask,
    tvDist
        (sampleEvaluationMaterial q degree sourceRank suffixRank tgswLevels
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluateAndSmudge mask)
        (sampleEvaluationMaterial q degree sourceRank suffixRank tgswLevels
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget
          (act secret mask)) ≤ error

namespace ShiftedEvaluationMaterialEvaluator

/-- Lift a material-only evaluator to the complete view by applying the exact scalar-key XOR
transport to the tape. -/
def evaluateCompleteView
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (mask : Mask sourceRank suffixRank degree)
    (view : View q degree sourceRank suffixRank tgswLevels queryCount) :
    ProbComp (View q degree sourceRank suffixRank tgswLevels queryCount) := do
  let auxiliary ← evaluator.evaluateAndSmudge mask view.2
  return (transformTargetTape mask view.1, auxiliary)

/-- The lifted source experiment factors into the exactly transformed tape and the evaluated
material experiment. -/
theorem evaluatedCompleteView_eq_independentPair
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (secret : Secret sourceRank suffixRank degree)
    (mask : Mask sourceRank suffixRank degree) :
    (sampleRealView q degree sourceRank suffixRank tgswLevels queryCount
        narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
        gadget secret >>= evaluator.evaluateCompleteView mask) =
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair
        (transformTargetTape mask <$>
          sampleTargetTape q degree sourceRank suffixRank queryCount inputErrorSampler
            secret)
        (sampleEvaluationMaterial q degree sourceRank suffixRank tgswLevels
            narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
          evaluator.evaluateAndSmudge mask)
        (fun tape auxiliary ↦ (tape, auxiliary)) := by
  simp [sampleRealView, problem, sampleTargetTape, sampleEvaluationMaterial,
    evaluateCompleteView,
    FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
    map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- Transporting the target tape adds exactly zero to the material evaluator's TV budget. -/
theorem completeViewDistance_le
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (secret : Secret sourceRank suffixRank degree)
    (mask : Mask sourceRank suffixRank degree) :
    tvDist
        (sampleRealView q degree sourceRank suffixRank tgswLevels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>= evaluator.evaluateCompleteView mask)
        (sampleRealView q degree sourceRank suffixRank tgswLevels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          (act secret mask)) ≤ evaluator.error := by
  let transformedTape := transformTargetTape mask <$>
    sampleTargetTape q degree sourceRank suffixRank queryCount inputErrorSampler secret
  let targetTape := sampleTargetTape q degree sourceRank suffixRank queryCount
    inputErrorSampler (act secret mask)
  let evaluatedMaterial :=
    sampleEvaluationMaterial q degree sourceRank suffixRank tgswLevels
        narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret >>=
      evaluator.evaluateAndSmudge mask
  let targetMaterial :=
    sampleEvaluationMaterial q degree sourceRank suffixRank tgswLevels
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget (act secret mask)
  rw [evaluator.evaluatedCompleteView_eq_independentPair inputErrorSampler secret mask,
    sampleRealView_eq_independentPair]
  have htape : tvDist transformedTape targetTape = 0 := by
    unfold transformedTape targetTape tvDist
    rw [transformTargetTape_sampleTargetTape_evalDist]
    exact SPMF.tvDist_self _
  calc
    tvDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair transformedTape
          evaluatedMaterial (fun tape auxiliary ↦ (tape, auxiliary)))
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair targetTape
          targetMaterial (fun tape auxiliary ↦ (tape, auxiliary))) ≤
      tvDist transformedTape targetTape + tvDist evaluatedMaterial targetMaterial :=
        FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
          transformedTape targetTape evaluatedMaterial targetMaterial
          (fun tape auxiliary ↦ (tape, auxiliary))
    _ ≤ 0 + evaluator.error := add_le_add (le_of_eq htape)
      (evaluator.materialDistance_le secret mask)
    _ = evaluator.error := zero_add _

/-- Canonical lift from an evaluation-material-only certificate to the complete direct FHE
shifted-view certificate.  The same scalar input-error sampler is used before and after the shift
because target-tape key transport is exact. -/
def toShiftedViewEvaluator
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q)) :
    ShiftedViewEvaluator q degree sourceRank suffixRank tgswLevels queryCount
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget where
  evaluateAndSmudge := evaluator.evaluateCompleteView
  error := evaluator.error
  error_nonneg := evaluator.error_nonneg
  viewDistance_le := evaluator.completeViewDistance_le inputErrorSampler

@[simp]
theorem toShiftedViewEvaluator_error
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q)) :
    (evaluator.toShiftedViewEvaluator
      (queryCount := queryCount) inputErrorSampler).error = evaluator.error := rfl

/-- The material-only certificate therefore supplies the paper-aligned fresh-secret
`ViewRandomization` for the complete adaptive TFHE public view. -/
def toViewRandomization
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q)) :=
  (evaluator.toShiftedViewEvaluator
    (queryCount := queryCount) inputErrorSampler).toViewRandomization

@[simp]
theorem toViewRandomization_error
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q)) :
    (evaluator.toViewRandomization
      (queryCount := queryCount) inputErrorSampler).error = evaluator.error := rfl

/-- After sampling a complete nested mask, the transformed full view is within exactly the
material evaluator's pointwise error of a fresh-secret wide view. -/
theorem randomizedCompleteView_tvDist_freshWideView_le
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q degree)}
    {gadget : Fin tgswLevels → RLWE.Rq q degree}
    (evaluator : ShiftedEvaluationMaterialEvaluator q degree sourceRank suffixRank
      tgswLevels narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (secret : Secret sourceRank suffixRank degree) :
    tvDist
        ((evaluator.toViewRandomization
          (queryCount := queryCount) inputErrorSampler).randomizedView secret)
        (evaluator.toViewRandomization
          (queryCount := queryCount) inputErrorSampler).freshWideView ≤ evaluator.error := by
  simpa only [toViewRandomization_error] using
    (evaluator.toViewRandomization
      (queryCount := queryCount) inputErrorSampler)
      |>.randomizedView_tvDist_freshWideView_le secret

end ShiftedEvaluationMaterialEvaluator

/-! ## Exact BRK-message transport -/

/-- Publicly update every source-BRK plaintext bit according to the nested target-key XOR mask,
while temporarily leaving the source ring encryption key unchanged. -/
def transformSourceBootstrappingKeyMessages
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (mask : Mask sourceRank suffixRank degree)
    (bootstrappingKey :
      SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels) :
    SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels :=
  FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey
    gadget (targetScalarMask mask) bootstrappingKey

/-- For positive negacyclic degree and centered-binomial ring noise, the complete target-message
update is distributionally exact.  The resulting BRK already contains
`KeyExtract(act(S_source,S_suffix))`; only transport of its ring encryption key from `S_source`
to the masked source key remains. -/
theorem transformSourceBootstrappingKeyMessages_generate_evalDist
    {q degree sourceRank suffixRank tgswLevels eta : ℕ} [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (secret : Secret sourceRank suffixRank (degree + 1))
    (mask : Mask sourceRank suffixRank (degree + 1)) :
    evalDist (transformSourceBootstrappingKeyMessages gadget mask <$>
        generateSourceBootstrappingKey q (degree + 1) sourceRank suffixRank
          tgswLevels (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          gadget secret.1 secret.2) =
      evalDist (Native.generateBootstrappingKey q (degree + 1) sourceRank
        tgswLevels (targetScalarDimension sourceRank suffixRank (degree + 1))
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) gadget
        (targetMessages (act secret mask).1 (act secret mask).2) secret.1) := by
  unfold transformSourceBootstrappingKeyMessages generateSourceBootstrappingKey
  have h :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformBootstrappingKey_generate_centeredBinomial_evalDist
      (eta := eta) gadget (targetMessages secret.1 secret.2) (targetScalarMask mask)
      secret.1
  rw [← targetMessages_act secret mask] at h
  exact h

/-! ## Exact global-complement transport for the ring extension table -/

/-- The coefficientwise all-true mask for every component of a binary ring key. -/
def allTrueRingMask (rank degree : ℕ) : RingBinarySecret rank degree :=
  fun _ ↦ allTruePolynomial degree

/-- Embedded all-coefficient complementation is the public scalar-affine ring-key map
`s ↦ -s + 1⃗`, component by component. -/
theorem embedRingSecret_masked_allTrue
    (q : ℕ) {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) :
    embedRingSecret q (maskedRingSecret secret (allTrueRingMask rank degree)) =
      fun component ↦ embedBinaryPolynomial q degree (allTruePolynomial degree) -
        embedRingSecret q secret component := by
  funext component
  rw [show embedRingSecret q
      (maskedRingSecret secret (allTrueRingMask rank degree)) component =
    embedBinaryPolynomial q degree
      (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        (secret component) (allTruePolynomial degree)) by rfl]
  rw [embedBinaryPolynomial_masked_allTrue]
  apply LatticeCrypto.NegacyclicRing.poly_ext
  intro coefficient
  simp only [LatticeCrypto.NegacyclicRing.coeff_add,
    LatticeCrypto.NegacyclicRing.coeff_neg,
    LatticeCrypto.NegacyclicRing.coeff_sub, embedRingSecret]
  abel

/-- The generic scalar-affine TLWE transport with multiplier `-1` and all-one offset has exactly
the embedded globally complemented ring key as its target. -/
theorem scalarAffineRingSecret_negOne_allTrue
    (q : ℕ) {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) :
    scalarAffineSecret (-1)
        (fun _ ↦ embedBinaryPolynomial q degree (allTruePolynomial degree))
        (embedRingSecret q secret) =
      embedRingSecret q (maskedRingSecret secret (allTrueRingMask rank degree)) := by
  rw [embedRingSecret_masked_allTrue]
  funext component
  have h := congrFun
    (scalarAffineSecret_negOne_constant
      (embedBinaryPolynomial q degree (allTruePolynomial degree))
      (embedRingSecret q secret component)) (0 : Fin 1)
  calc
    scalarAffineSecret (-1)
        (fun _ ↦ embedBinaryPolynomial q degree (allTruePolynomial degree))
        (embedRingSecret q secret) component =
      @HSub.hSub (RLWE.Rq q degree) (RLWE.Rq q degree) (RLWE.Rq q degree)
        (@instHSub (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toAddGroupWithOne.toAddGroup.toSub)
        (embedBinaryPolynomial q degree (allTruePolynomial degree))
        (embedRingSecret q secret component) := by
      simpa only [scalarAffineSecret] using h
    _ = embedBinaryPolynomial q degree (allTruePolynomial degree) -
        embedRingSecret q secret component :=
      FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofSub_eq_sub _ _

/-- Complementing every coefficient of every suffix polynomial changes the extension message
table from `S_suffix[j] * g_l` to `1⃗ * g_l - S_suffix[j] * g_l`. -/
theorem ringKeySwitchMessages_masked_allTrue
    (q degree suffixRank levels : ℕ)
    (gadget : Fin levels → RLWE.Rq q degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q degree suffixRank levels gadget
        (maskedRingSecret suffixSecret (allTrueRingMask suffixRank degree)) =
      FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
          q degree suffixRank levels gadget (allTrueRingMask suffixRank degree) -
        FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
          q degree suffixRank levels gadget suffixSecret := by
  funext row
  obtain ⟨⟨component, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  simp only [FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages,
    Pi.sub_apply, Equiv.symm_apply_apply]
  change embedBinaryPolynomial q degree
      (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        (suffixSecret component) (allTruePolynomial degree)) * gadget level =
    embedBinaryPolynomial q degree (allTruePolynomial degree) * gadget level -
      embedBinaryPolynomial q degree (suffixSecret component) * gadget level
  rw [embedBinaryPolynomial_masked_allTrue]
  let sourceValue := embedBinaryPolynomial q degree (suffixSecret component)
  let oneValue := embedBinaryPolynomial q degree (allTruePolynomial degree)
  let gadgetValue := gadget level
  have hreorder : -sourceValue + oneValue = oneValue - sourceValue := by
    apply LatticeCrypto.NegacyclicRing.poly_ext
    intro coefficient
    simp only [LatticeCrypto.NegacyclicRing.coeff_add,
      LatticeCrypto.NegacyclicRing.coeff_neg,
      LatticeCrypto.NegacyclicRing.coeff_sub]
    abel
  rw [show -embedBinaryPolynomial q degree (suffixSecret component) +
      embedBinaryPolynomial q degree (allTruePolynomial degree) =
      oneValue - sourceValue by exact hreorder]
  calc
    (oneValue - sourceValue) * gadgetValue =
        gadgetValue * (oneValue - sourceValue) := by
      exact LatticeCrypto.vectorRing_mul_comm _ _
    _ = gadgetValue * oneValue - gadgetValue * sourceValue := by
      exact LatticeCrypto.vectorRing_mul_sub_right _ _ _
    _ = oneValue * gadgetValue - sourceValue * gadgetValue := by
      congr 1
      · exact LatticeCrypto.vectorRing_mul_comm _ _
      · exact LatticeCrypto.vectorRing_mul_comm _ _

/-- Public global-complement action on the native ring-valued extension table.  It first
complements every suffix-polynomial message and then applies the scalar-affine map
`S_source ↦ 1⃗ - S_source` to its ring encryption key. -/
def transformRingExtensionGlobalComplement
    {q degree sourceRank suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (ringExtensionKey : RingExtensionKey q degree sourceRank suffixRank levels) :
    RingExtensionKey q degree sourceRank suffixRank levels :=
  let shift :=
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
      q degree suffixRank levels gadget (allTrueRingMask suffixRank degree)
  let offset := fun _ : Fin sourceRank ↦
    embedBinaryPolynomial q degree (allTruePolynomial degree)
  scalarAffineTranslateBatch (-1) offset
    (complementBatchMessage shift ringExtensionKey)

/-- Under any negation-symmetric ring-noise law, global complementation of both nested key blocks
is an exact distributional transport of the full native extension table. -/
theorem transformRingExtensionGlobalComplement_generate_evalDist
    {q degree sourceRank suffixRank levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    evalDist (transformRingExtensionGlobalComplement gadget <$>
        generateRingExtensionKey q degree sourceRank suffixRank levels errorSampler
          gadget sourceSecret suffixSecret) =
      evalDist (generateRingExtensionKey q degree sourceRank suffixRank levels
        errorSampler gadget
        (maskedRingSecret sourceSecret (allTrueRingMask sourceRank degree))
        (maskedRingSecret suffixSecret (allTrueRingMask suffixRank degree))) := by
  let sourceKey := embedRingSecret q sourceSecret
  let sourceMessage :=
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
      q degree suffixRank levels gadget suffixSecret
  let shift :=
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
      q degree suffixRank levels gadget (allTrueRingMask suffixRank degree)
  let targetMessage :=
    FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
      q degree suffixRank levels gadget
        (maskedRingSecret suffixSecret (allTrueRingMask suffixRank degree))
  let offset := fun _ : Fin sourceRank ↦
    embedBinaryPolynomial q degree (allTruePolynomial degree)
  let affine : RingExtensionKey q degree sourceRank suffixRank levels →
      RingExtensionKey q degree sourceRank suffixRank levels :=
    scalarAffineTranslateBatch (-1 : (RLWE.Rq q degree)ˣ) offset
  let complement : RingExtensionKey q degree sourceRank suffixRank levels →
      RingExtensionKey q degree sourceRank suffixRank levels :=
    complementBatchMessage shift
  have hmessage : targetMessage = shift - sourceMessage := by
    exact ringKeySwitchMessages_masked_allTrue q degree suffixRank levels gadget
      suffixSecret
  let proofDifference : Fin (suffixRank * levels) → RLWE.Rq q degree :=
    fun row ↦ @Sub.sub (RLWE.Rq q degree)
      (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toSub
      (shift row) (sourceMessage row)
  have hproofDifference : proofDifference = targetMessage := by
    funext row
    calc
      proofDifference row = shift row - sourceMessage row :=
        FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofSub_eq_sub _ _
      _ = targetMessage row := congrFun hmessage.symm row
  have hsymmetricProof :
      @FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        (RLWE.Rq q degree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) degree).toAddCommGroup.toNeg errorSampler := by
    intro error
    change Pr[= FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofNeg error |
      errorSampler] = Pr[= error | errorSampler]
    rw [FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofNeg_eq_neg]
    exact hsymmetric error
  have hcomplement :
      evalDist (complement <$>
          TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler sourceKey
            sourceMessage) =
        evalDist (TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler
          sourceKey targetMessage) := by
    have h := complementBatchMessage_batchEncrypt_evalDist errorSampler hsymmetricProof
      sourceKey sourceMessage shift
    change evalDist (complement <$>
        TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler sourceKey
          sourceMessage) =
      evalDist (TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler
        sourceKey proofDifference) at h
    rw [hproofDifference] at h
    exact h
  have haffine :
      evalDist (affine <$>
          TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler sourceKey
            targetMessage) =
        evalDist (TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler
          (embedRingSecret q
            (maskedRingSecret sourceSecret (allTrueRingMask sourceRank degree)))
          targetMessage) := by
    have h := scalarAffineTranslateBatch_batchEncrypt_evalDist errorSampler
      (-1 : (RLWE.Rq q degree)ˣ) offset sourceKey targetMessage
    rw [scalarAffineRingSecret_negOne_allTrue q sourceSecret] at h
    exact h
  unfold transformRingExtensionGlobalComplement generateRingExtensionKey
  change evalDist ((fun ciphertext ↦ affine (complement ciphertext)) <$>
      TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler sourceKey
        sourceMessage) = _
  calc
    _ = evalDist (affine <$> (complement <$>
        TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler sourceKey
          sourceMessage)) := by
      rw [Functor.map_map]
    _ = evalDist (affine <$>
        TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler sourceKey
          targetMessage) := evalDist_map_eq_of_evalDist_eq hcomplement affine
    _ = evalDist (TLWE.batchEncrypt sourceRank (suffixRank * levels) errorSampler
        (embedRingSecret q
          (maskedRingSecret sourceSecret (allTrueRingMask sourceRank degree)))
        targetMessage) := haffine
    _ = _ := by
      simp [targetMessage,
        FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateRingKeySwitchKey]

/-- Executable centered-binomial specialization of exact global-complement extension transport. -/
theorem transformRingExtensionGlobalComplement_centeredBinomial_evalDist
    {q degree sourceRank suffixRank levels eta : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree)
    (sourceSecret : RingBinarySecret sourceRank degree)
    (suffixSecret : RingBinarySecret suffixRank degree) :
    evalDist (transformRingExtensionGlobalComplement gadget <$>
        generateRingExtensionKey q degree sourceRank suffixRank levels
          (RLWE.CenteredBinomial.sampler q degree eta) gadget sourceSecret
          suffixSecret) =
      evalDist (generateRingExtensionKey q degree sourceRank suffixRank levels
        (RLWE.CenteredBinomial.sampler q degree eta) gadget
        (maskedRingSecret sourceSecret (allTrueRingMask sourceRank degree))
        (maskedRingSecret suffixSecret (allTrueRingMask suffixRank degree))) :=
  transformRingExtensionGlobalComplement_generate_evalDist
    (RLWE.CenteredBinomial.sampler q degree eta)
    (RLWE.CenteredBinomial.probOutput_neg q degree eta) gadget sourceSecret
    suffixSecret

/-! ## Joint rank-one evaluation-material global complement -/

/-- Complement every coefficient of both nested ring-key blocks. -/
def nestedGlobalMask (sourceRank suffixRank degree : ℕ) :
    Mask sourceRank suffixRank degree :=
  (allTrueRingMask sourceRank degree, allTrueRingMask suffixRank degree)

/-- The scalar target-key mask induced by the complete nested complement is itself all true. -/
theorem targetScalarMask_nestedGlobalMask
    (sourceRank suffixRank degree : ℕ) :
    targetScalarMask (nestedGlobalMask sourceRank suffixRank degree) =
      allTruePolynomial (targetScalarDimension sourceRank suffixRank degree) := by
  funext coordinate
  obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
  refine Fin.addCases ?_ ?_ component
  · intro sourceComponent
    simp [targetScalarMask, nestedGlobalMask, allTrueRingMask, allTruePolynomial]
  · intro suffixComponent
    simp [targetScalarMask, nestedGlobalMask, allTrueRingMask, allTruePolynomial]

/-- Acting by the complete nested complement globally complements every extracted target-key
message bit. -/
theorem targetMessages_act_nestedGlobalMask
    {sourceRank suffixRank degree : ℕ}
    (secret : Secret sourceRank suffixRank degree) :
    targetMessages
        (act secret (nestedGlobalMask sourceRank suffixRank degree)).1
        (act secret (nestedGlobalMask sourceRank suffixRank degree)).2 =
      globalComplementAction (targetMessages secret.1 secret.2) true := by
  rw [targetMessages_act, targetScalarMask_nestedGlobalMask]
  funext coordinate
  simp [globalComplementAction, allTruePolynomial,
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]

/-- Public global-complement action on the full rank-one BRK plus extension material. -/
def transformEvaluationMaterialGlobalComplement
    {q degree suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (material : Auxiliary q degree 1 suffixRank levels) :
    Auxiliary q degree 1 suffixRank levels :=
  (globalComplementBootstrappingKey
      (embedBinaryPolynomial q degree (allTruePolynomial degree)) gadget material.1,
    transformRingExtensionGlobalComplement gadget material.2)

/-- The rank-one BRK part of the target-message material has exactly the established complement
shear loss; the fact that its plaintext vector is the complete nested target key introduces no
additional term. -/
theorem transformSourceBootstrappingKeyGlobalComplement_tvDist_le
    {q degree suffixRank levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    tvDist
        (globalComplementBootstrappingKey
            (embedBinaryPolynomial q (degree + 1)
              (allTruePolynomial (degree + 1))) gadget <$>
          generateSourceBootstrappingKey q (degree + 1) 1 suffixRank levels
            errorSampler gadget secret.1 secret.2)
        (generateSourceBootstrappingKey q (degree + 1) 1 suffixRank levels
          errorSampler gadget
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1))).1
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1))).2) ≤
      (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
        rankOneComplementNoiseDistance (levels := levels) errorSampler
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) := by
  have h := globalComplementBootstrappingKey_generate_tvDist_le errorSampler gadget
    (targetMessages secret.1 secret.2) secret.1
  rw [← targetMessages_act_nestedGlobalMask secret] at h
  exact h

/-- **Joint material theorem.**  For rank-one source GLWE, the complete BRK/extension public
material transports under global complementation of both nested key blocks.  The extension table
is exact, so the only loss is the already isolated BRK complement-shear distance. -/
theorem transformEvaluationMaterialGlobalComplement_tvDist_le
    {q degree suffixRank levels : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        extensionErrorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    tvDist
        (transformEvaluationMaterialGlobalComplement gadget <$>
          sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
            bootstrapErrorSampler extensionErrorSampler gadget secret)
        (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
          bootstrapErrorSampler extensionErrorSampler gadget
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1)))) ≤
      (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
        rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) := by
  let targetSecret := act secret (nestedGlobalMask 1 suffixRank (degree + 1))
  let sourceBootstrappingKey :=
    generateSourceBootstrappingKey q (degree + 1) 1 suffixRank levels
      bootstrapErrorSampler gadget secret.1 secret.2
  let targetBootstrappingKey :=
    generateSourceBootstrappingKey q (degree + 1) 1 suffixRank levels
      bootstrapErrorSampler gadget targetSecret.1 targetSecret.2
  let transformedBootstrappingKey :=
    globalComplementBootstrappingKey
        (embedBinaryPolynomial q (degree + 1)
          (allTruePolynomial (degree + 1))) gadget <$>
      sourceBootstrappingKey
  let sourceExtensionKey :=
    generateRingExtensionKey q (degree + 1) 1 suffixRank levels
      extensionErrorSampler gadget secret.1 secret.2
  let targetExtensionKey :=
    generateRingExtensionKey q (degree + 1) 1 suffixRank levels
      extensionErrorSampler gadget targetSecret.1 targetSecret.2
  let transformedExtensionKey :=
    transformRingExtensionGlobalComplement gadget <$> sourceExtensionKey
  let combine := fun
      (bootstrappingKey : SourceBootstrappingKey q (degree + 1) 1 suffixRank levels)
      (extensionKey : RingExtensionKey q (degree + 1) 1 suffixRank levels) ↦
    (bootstrappingKey, extensionKey)
  have hbootstrappingKey :
      tvDist transformedBootstrappingKey targetBootstrappingKey ≤
        (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
          rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
            (embedBinaryPolynomial q (degree + 1)
              (allTruePolynomial (degree + 1))) := by
    exact transformSourceBootstrappingKeyGlobalComplement_tvDist_le
      bootstrapErrorSampler gadget secret
  have hextensionEvalDist :
      evalDist transformedExtensionKey = evalDist targetExtensionKey := by
    have h := transformRingExtensionGlobalComplement_generate_evalDist
      extensionErrorSampler hextensionSymmetric gadget secret.1 secret.2
    simpa only [transformedExtensionKey, sourceExtensionKey, targetExtensionKey,
      targetSecret, act, nestedGlobalMask] using h
  have hextension : tvDist transformedExtensionKey targetExtensionKey = 0 := by
    unfold tvDist
    rw [hextensionEvalDist]
    exact SPMF.tvDist_self _
  have hsource :
      transformEvaluationMaterialGlobalComplement gadget <$>
          sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
            bootstrapErrorSampler extensionErrorSampler gadget secret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedBootstrappingKey transformedExtensionKey combine := by
    simp [sampleEvaluationMaterial, transformEvaluationMaterialGlobalComplement,
      sourceBootstrappingKey, sourceExtensionKey, transformedBootstrappingKey,
      transformedExtensionKey, combine,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]
  have htarget :
      sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
          bootstrapErrorSampler extensionErrorSampler gadget targetSecret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetBootstrappingKey targetExtensionKey combine := by
    simp [sampleEvaluationMaterial, targetBootstrappingKey, targetExtensionKey,
      combine, FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, monad_norm]
  rw [hsource, show act secret (nestedGlobalMask 1 suffixRank (degree + 1)) =
      targetSecret by rfl, htarget]
  calc
    tvDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedBootstrappingKey transformedExtensionKey combine)
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetBootstrappingKey targetExtensionKey combine) ≤
      tvDist transformedBootstrappingKey targetBootstrappingKey +
        tvDist transformedExtensionKey targetExtensionKey :=
      FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
        transformedBootstrappingKey targetBootstrappingKey transformedExtensionKey
        targetExtensionKey combine
    _ ≤ (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
          rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
            (embedBinaryPolynomial q (degree + 1)
              (allTruePolynomial (degree + 1))) + 0 :=
      add_le_add hbootstrappingKey (le_of_eq hextension)
    _ = _ := add_zero _

/-- Public global-complement action on the complete adaptive view, including the query-counted
target-key tape. -/
def transformCompleteViewGlobalComplement
    {q degree suffixRank levels queryCount : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (view : View q degree 1 suffixRank levels queryCount) :
    View q degree 1 suffixRank levels queryCount :=
  (transformTargetTape (nestedGlobalMask 1 suffixRank degree) view.1,
    transformEvaluationMaterialGlobalComplement gadget view.2)

/-- **Complete-view anchor theorem.**  The target tape and extension table contribute zero loss
to global complementation.  For rank-one source GLWE, the complete adaptive public view therefore
pays exactly the BRK complement-shear bound. -/
theorem transformCompleteViewGlobalComplement_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        extensionErrorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    tvDist
        (transformCompleteViewGlobalComplement gadget <$>
          sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret)
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1)))) ≤
      (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
        rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) := by
  let mask := nestedGlobalMask 1 suffixRank (degree + 1)
  let targetSecret := act secret mask
  let transformedTape := transformTargetTape mask <$>
    sampleTargetTape q (degree + 1) 1 suffixRank queryCount inputErrorSampler secret
  let targetTape := sampleTargetTape q (degree + 1) 1 suffixRank queryCount
    inputErrorSampler targetSecret
  let transformedMaterial := transformEvaluationMaterialGlobalComplement gadget <$>
    sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
      bootstrapErrorSampler extensionErrorSampler gadget secret
  let targetMaterial := sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
    bootstrapErrorSampler extensionErrorSampler gadget targetSecret
  let combine := fun
      (tape : Challenge q (degree + 1) 1 suffixRank queryCount)
      (material : Auxiliary q (degree + 1) 1 suffixRank levels) ↦
    (tape, material)
  have htape : tvDist transformedTape targetTape = 0 := by
    unfold transformedTape targetTape targetSecret mask tvDist
    rw [transformTargetTape_sampleTargetTape_evalDist]
    exact SPMF.tvDist_self _
  have hmaterial :
      tvDist transformedMaterial targetMaterial ≤
        (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
          rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
            (embedBinaryPolynomial q (degree + 1)
              (allTruePolynomial (degree + 1))) := by
    exact transformEvaluationMaterialGlobalComplement_tvDist_le
      bootstrapErrorSampler extensionErrorSampler hextensionSymmetric gadget secret
  have hsource :
      transformCompleteViewGlobalComplement gadget <$>
          sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape transformedMaterial combine := by
    simp [sampleRealView, problem, sampleTargetTape, sampleEvaluationMaterial,
      transformCompleteViewGlobalComplement, transformedTape, transformedMaterial,
      mask, combine, FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]
  have htarget :
      sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget targetSecret =
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetTape targetMaterial combine := by
    simp [sampleRealView, problem, sampleTargetTape, sampleEvaluationMaterial,
      targetTape, targetMaterial, combine,
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      map_eq_bind_pure_comp, monad_norm]
  rw [hsource, show act secret (nestedGlobalMask 1 suffixRank (degree + 1)) =
      targetSecret by rfl, htarget]
  calc
    tvDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedTape transformedMaterial combine)
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetTape targetMaterial combine) ≤
      tvDist transformedTape targetTape + tvDist transformedMaterial targetMaterial :=
      FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
        transformedTape targetTape transformedMaterial targetMaterial combine
    _ ≤ 0 +
        (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
          rankOneComplementNoiseDistance (levels := levels) bootstrapErrorSampler
            (embedBinaryPolynomial q (degree + 1)
              (allTruePolynomial (degree + 1))) :=
      add_le_add (le_of_eq htape) hmaterial
    _ = _ := zero_add _

/-- Centered-binomial specialization of the complete-view anchor theorem. -/
theorem transformCompleteViewGlobalComplement_centeredBinomial_tvDist_le
    {q degree suffixRank levels queryCount bootstrapEta extensionEta : ℕ} [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    tvDist
        (transformCompleteViewGlobalComplement gadget <$>
          sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            (RLWE.CenteredBinomial.sampler q (degree + 1) bootstrapEta)
            (RLWE.CenteredBinomial.sampler q (degree + 1) extensionEta)
            inputErrorSampler gadget secret)
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          (RLWE.CenteredBinomial.sampler q (degree + 1) bootstrapEta)
          (RLWE.CenteredBinomial.sampler q (degree + 1) extensionEta)
          inputErrorSampler gadget
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1)))) ≤
      (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
        rankOneComplementNoiseDistance (levels := levels)
          (RLWE.CenteredBinomial.sampler q (degree + 1) bootstrapEta)
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) :=
  transformCompleteViewGlobalComplement_tvDist_le
    (RLWE.CenteredBinomial.sampler q (degree + 1) bootstrapEta)
    (RLWE.CenteredBinomial.sampler q (degree + 1) extensionEta)
    inputErrorSampler
    (RLWE.CenteredBinomial.probOutput_neg q (degree + 1) extensionEta)
    gadget secret

/-- Certified discrete-Gaussian complete-view anchor bound.  Global complementation of the
nested key contributes at most the explicit scalar translation envelope inherited from the
rank-one BRK shear analysis; the tape and extension table remain exact. -/
theorem transformCompleteViewGlobalComplement_discreteGaussian_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (hsymmetric : DiscreteGaussianSampler.TicketNegationSymmetric certificate)
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    tvDist
        (transformCompleteViewGlobalComplement gadget <$>
          sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            inputErrorSampler gadget secret)
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          inputErrorSampler gadget
          (act secret (nestedGlobalMask 1 suffixRank (degree + 1)))) ≤
      (targetScalarDimension 1 suffixRank (degree + 1) : ℝ) *
        ((levels : ℝ) *
          (((degree + 1 : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound certificate (q / 2))) := by
  have hview := transformCompleteViewGlobalComplement_tvDist_le
    (queryCount := queryCount)
    (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    inputErrorSampler
    (DiscreteGaussianSampler.ringSampler_negationSymmetric
      (degree + 1) certificate hsymmetric)
    gadget secret
  have hnoise := rankOneComplementNoiseDistance_discreteGaussian_le
    (levels := levels) certificate hsymmetric
    (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
  exact hview.trans
    (mul_le_mul_of_nonneg_left hnoise (Nat.cast_nonneg _))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
