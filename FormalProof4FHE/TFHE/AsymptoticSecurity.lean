/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveEncryptionSecurity
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Asymptotic Adaptive TFHE Encryption Security

This module packages the finite query-bounded adaptive TFHE reduction as an asymptotic
negligible-advantage theorem. Adversary families carry explicit polynomial encryption-query
bounds. The general result retains distinct key-switch and input error samplers in one exact
heterogeneous joint-LWE game; the equal-noise specialization flattens it to ordinary batch LWE.
The native direct-bilinear circular/KDM premise remains explicit and is paid once.
-/

open ENNReal OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic

/-- A security-parameter-indexed family of native TFHE parameters and samplers. Messages stay in
one fixed type, while every cryptographic dimension and modulus may grow with the parameter. -/
structure Parameters (Message : Type) where
  q : ℕ → ℕ
  degree : ℕ → ℕ
  ringRank : ℕ → ℕ
  tgswLevels : ℕ → ℕ
  lweDimension : ℕ → ℕ
  keySwitchLevels : ℕ → ℕ
  ringErrorSampler : (securityParameter : ℕ) →
    ProbComp (RLWE.Rq (q securityParameter) (degree securityParameter))
  keySwitchErrorSampler : (securityParameter : ℕ) → ProbComp (ZMod (q securityParameter))
  inputErrorSampler : (securityParameter : ℕ) → ProbComp (ZMod (q securityParameter))
  tgswGadget : (securityParameter : ℕ) →
    Fin (tgswLevels securityParameter) →
      RLWE.Rq (q securityParameter) (degree securityParameter)
  keySwitchGadget : (securityParameter : ℕ) →
    Fin (keySwitchLevels securityParameter) → ZMod (q securityParameter)
  encode : (securityParameter : ℕ) → Message → ZMod (q securityParameter)

/-- A family of native adaptive TFHE adversaries before adding its query-bound witness. -/
abbrev NativeAdversaryFamily {Message : Type} (params : Parameters Message) :=
  (securityParameter : ℕ) → NativeAdversary Message
    (params.q securityParameter)
    (params.degree securityParameter)
    (params.ringRank securityParameter)
    (params.tgswLevels securityParameter)
    (params.lweDimension securityParameter)
    (params.keySwitchLevels securityParameter)

/-- A parameter-indexed adaptive adversary with an explicit polynomial encryption-query bound.
The computational-efficiency predicate remains separate so callers can add their cost model. -/
structure PolynomialQueryAdversary {Message : Type} (params : Parameters Message) where
  run : NativeAdversaryFamily params
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  isQueryBound : ∀ securityParameter,
    Adaptive.IsQueryBound (run securityParameter) (queryCount securityParameter)

/-! ### Public evaluation is security-preserving postprocessing -/

/-- A parameter-indexed public evaluator.  It receives the same native cloud key exposed by the
security game and maps one scalar ciphertext to an arbitrary public output type. -/
abbrev PublicEvaluatorFamily {Message Output : Type} (params : Parameters Message) :=
  (securityParameter : ℕ) →
    Encryption.NativeCloudKey
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter) →
    TLWE.Ciphertext (ZMod (params.q securityParameter))
      (params.lweDimension securityParameter) → Output

/-- An adversary for the oracle obtained by publicly evaluating every returned ciphertext.  As in
the base game, the polynomial encryption-query witness is separate from the caller's computational
cost predicate. -/
structure PolynomialQueryEvaluationAdversary {Message Output : Type}
    (params : Parameters Message) where
  run : (securityParameter : ℕ) →
    Adaptive.Adversary Message
      (Encryption.NativeCloudKey
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter)
        (params.keySwitchLevels securityParameter))
      Output
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  isQueryBound : ∀ securityParameter,
    Adaptive.IsQueryBound (run securityParameter) (queryCount securityParameter)

/-- Compile public evaluation into the unrestricted native TFHE adversary.  The query polynomial
and its witness are preserved literally. -/
def compileEvaluationAdversary {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (adversary : PolynomialQueryEvaluationAdversary (Output := Output) params) :
    PolynomialQueryAdversary params where
  run securityParameter :=
    Adaptive.compilePublicEvaluation
      (evaluate securityParameter) (adversary.run securityParameter)
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  isQueryBound securityParameter := by
    letI : IsUniformSpec
        ((Message × Message) →ₒ
          TLWE.Ciphertext (ZMod (params.q securityParameter))
            (params.lweDimension securityParameter)) :=
      IsUniformSpec.ofFintypeInhabited _
    exact Adaptive.compilePublicEvaluation_isQueryBound
      (evaluate securityParameter) (adversary.run securityParameter)
      (adversary.queryCount securityParameter)
      (adversary.isQueryBound securityParameter)

/-- Polynomial growth witnesses for the three parameters that determine the number of KSK rows.
Together with `PolynomialQueryAdversary.queryPolynomial`, these show that the complete batch-LWE
transcript used by the reduction has polynomially many samples. -/
structure PolynomialKeySwitchGrowth {Message : Type} (params : Parameters Message) where
  ringRankPolynomial : Polynomial ℕ
  degreePolynomial : Polynomial ℕ
  keySwitchLevelsPolynomial : Polynomial ℕ
  ringRank_le : ∀ securityParameter,
    params.ringRank securityParameter ≤ ringRankPolynomial.eval securityParameter
  degree_le : ∀ securityParameter,
    params.degree securityParameter ≤ degreePolynomial.eval securityParameter
  keySwitchLevels_le : ∀ securityParameter,
    params.keySwitchLevels securityParameter ≤
      keySwitchLevelsPolynomial.eval securityParameter

/-- A polynomial bounding every KSK row and every adaptive encryption row consumed by the
ordinary LWE reduction. -/
noncomputable def batchSamplePolynomial {Message : Type} {params : Parameters Message}
    (growth : PolynomialKeySwitchGrowth params)
    (adversary : PolynomialQueryAdversary params) : Polynomial ℕ :=
  (growth.ringRankPolynomial * growth.degreePolynomial) *
      growth.keySwitchLevelsPolynomial + adversary.queryPolynomial

/-- Exact row accounting plus the componentwise polynomial witnesses imply polynomial total
sample growth for the batch-LWE target. -/
theorem batchSampleCount_le_polynomial {Message : Type} {params : Parameters Message}
    (growth : PolynomialKeySwitchGrowth params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    Encryption.Security.keySwitchSamples
          (params.ringRank securityParameter)
          (params.degree securityParameter)
          (params.keySwitchLevels securityParameter) +
        adversary.queryCount securityParameter ≤
      (batchSamplePolynomial growth adversary).eval securityParameter := by
  simp only [batchSamplePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Encryption.Security.keySwitchSamples]
  exact Nat.add_le_add
    (Nat.mul_le_mul
      (Nat.mul_le_mul (growth.ringRank_le securityParameter)
        (growth.degree_le securityParameter))
      (growth.keySwitchLevels_le securityParameter))
    (adversary.queryCount_le securityParameter)

/-- The native continuation family produced by the cloud-key/circular reduction. -/
abbrev ContinuationFamily {Message : Type} (params : Parameters Message) :=
  (securityParameter : ℕ) → Circular.Continuation
    (BinarySecret (params.lweDimension securityParameter))
    (RingBinarySecret (params.ringRank securityParameter) (params.degree securityParameter))
    (Native.BootstrappingKey
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter))
    (Native.KeySwitchKey
      (params.q securityParameter)
      (params.lweDimension securityParameter)
      (params.ringRank securityParameter * params.degree securityParameter)
      (params.keySwitchLevels securityParameter))

/-- The pointwise native circular/KDM reduction for an adaptive adversary family. -/
noncomputable def continuationReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : ContinuationFamily params :=
  fun securityParameter ↦
    Adaptive.continuation
      (adversary.queryCount securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)

/-- A security game for the native direct-bilinear cross-key KDM distribution. -/
noncomputable def directBilinearSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.BootstrapSecurity.directBilinearAdvantage
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- The heterogeneous shared-secret LWE adversary type at one parameter and query count. -/
abbrev JointLWEAdversaryAt {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Adaptive.jointLweProblem
      (params.q securityParameter)
      (params.lweDimension securityParameter)
      (Encryption.Security.keySwitchSamples
        (params.ringRank securityParameter)
        (params.degree securityParameter)
        (params.keySwitchLevels securityParameter))
      (queryCount securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter))

/-- A heterogeneous joint-LWE attack family with the source polynomial query witness. -/
structure JointLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    JointLWEAdversaryAt params queryCount securityParameter

/-- The exact two-noise shared-secret joint-LWE security game. -/
noncomputable def jointLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (JointLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Adaptive.jointLweProblem
        (params.q securityParameter)
        (params.lweDimension securityParameter)
        (Encryption.Security.keySwitchSamples
          (params.ringRank securityParameter)
          (params.degree securityParameter)
          (params.keySwitchLevels securityParameter))
        (adversary.queryCount securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter))
      (adversary.run securityParameter))

/-- The exact heterogeneous joint-LWE reduction induced at every security parameter. -/
noncomputable def jointLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : JointLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    Adaptive.keySwitchMessageReduction
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (Adaptive.nativeKeySwitchMessage (params.keySwitchGadget securityParameter))
      (params.encode securityParameter)
      (adversary.run securityParameter)

/-- The type of the ordinary batch-LWE adversary at one parameter and one query count. -/
abbrev BatchLWEAdversaryAt {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Native.KeySwitchSecurity.binaryLweProblem
      (params.q securityParameter)
      (params.lweDimension securityParameter)
      (Encryption.Security.keySwitchSamples
          (params.ringRank securityParameter)
          (params.degree securityParameter)
          (params.keySwitchLevels securityParameter) +
        queryCount securityParameter)
      (params.keySwitchErrorSampler securityParameter))

/-- A batch-LWE attack family retains the source polynomial sample-growth witness. Its problem
has exactly the KSK rows plus one row per adaptive encryption query. -/
structure BatchLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    BatchLWEAdversaryAt params queryCount securityParameter

/-- The exact query-counted ordinary binary-secret batch-LWE security game. -/
noncomputable def batchLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (BatchLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.KeySwitchSecurity.binaryLweProblem
        (params.q securityParameter)
        (params.lweDimension securityParameter)
        (Encryption.Security.keySwitchSamples
            (params.ringRank securityParameter)
            (params.degree securityParameter)
            (params.keySwitchLevels securityParameter) +
          adversary.queryCount securityParameter)
        (params.keySwitchErrorSampler securityParameter))
      (adversary.run securityParameter))

/-- The ordinary batch-LWE reduction for the equal-noise specialization at every parameter. -/
noncomputable def batchLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : BatchLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    FormalProof4FHE.LWE.TwoBlock.reduction
      (Adaptive.keySwitchMessageReduction
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (Adaptive.nativeKeySwitchMessage (params.keySwitchGadget securityParameter))
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The honest query-bounded adaptive TFHE left-or-right security game. -/
noncomputable def securityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    |Encryption.signedAdvantage
      (Adaptive.realGame
        (adversary.queryCount securityParameter)
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))|

/-- The adaptive TFHE game observed only through a public evaluator.  Its advantage is the base
security-game advantage of the compiled adversary, so public evaluation introduces exactly zero
cryptographic loss. -/
noncomputable def evaluationSecurityGame {Message Output : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params) :
    SecurityGame (PolynomialQueryEvaluationAdversary (Output := Output) params) where
  advantage adversary securityParameter :=
    (securityGame params).advantage
      (compileEvaluationAdversary params evaluate adversary) securityParameter

/-- Public evaluation preserves the exact pointwise advantage of its compiled base-game
adversary. -/
theorem evaluationSecurityGame_advantage_eq {Message Output : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (adversary : PolynomialQueryEvaluationAdversary (Output := Output) params)
    (securityParameter : ℕ) :
    (evaluationSecurityGame params evaluate).advantage adversary securityParameter =
      (securityGame params).advantage
        (compileEvaluationAdversary params evaluate adversary) securityParameter := rfl

/-- The finite two-noise native theorem lifted pointwise to `ℝ≥0∞`. This version exactly
preserves distinct key-switch and input error samplers. -/
theorem securityGame_advantage_le_directBilinear_add_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter := by
  have h := Adaptive.abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    (adversary.queryCount securityParameter)
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (params.encode securityParameter)
    (adversary.run securityParameter)
    (adversary.isQueryBound securityParameter)
  rw [Adaptive.bootstrapReplacementAdvantage_eq_directBilinear] at h
  have hCircularNonneg : 0 ≤
      Native.BootstrapSecurity.directBilinearAdvantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (Adaptive.continuation
          (adversary.queryCount securityParameter)
          (params.inputErrorSampler securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)) := by
    unfold Native.BootstrapSecurity.directBilinearAdvantage ProbComp.boolDistAdvantage
    exact abs_nonneg _
  have hLWENonneg : 0 ≤
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (Encryption.Security.keySwitchSamples
            (params.ringRank securityParameter)
            (params.degree securityParameter)
            (params.keySwitchLevels securityParameter))
          (adversary.queryCount securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.inputErrorSampler securityParameter))
        (Adaptive.keySwitchMessageReduction
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.inputErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (Adaptive.nativeKeySwitchMessage (params.keySwitchGadget securityParameter))
          (params.encode securityParameter)
          (adversary.run securityParameter)) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hLift := ENNReal.ofReal_le_ofReal h
  have hSum := hLift.trans_eq (ENNReal.ofReal_add hCircularNonneg hLWENonneg)
  simpa only [securityGame, directBilinearSecurityGame, jointLWESecurityGame,
    continuationReduction, jointLWEReduction] using hSum

/-- The finite native theorem lifted pointwise to `ℝ≥0∞`. One direct-bilinear term and one
ordinary batch-LWE term bound the honest advantage at every security parameter. -/
theorem securityGame_advantage_le_directBilinear_add_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter := by
  have h := Adaptive.abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
    (adversary.queryCount securityParameter)
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (params.encode securityParameter)
    (adversary.run securityParameter)
    (adversary.isQueryBound securityParameter)
  rw [Adaptive.bootstrapReplacementAdvantage_eq_directBilinear] at h
  have hCircularNonneg : 0 ≤
      Native.BootstrapSecurity.directBilinearAdvantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (Adaptive.continuation
          (adversary.queryCount securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)) := by
    unfold Native.BootstrapSecurity.directBilinearAdvantage ProbComp.boolDistAdvantage
    exact abs_nonneg _
  have hLWENonneg : 0 ≤
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (Encryption.Security.keySwitchSamples
              (params.ringRank securityParameter)
              (params.degree securityParameter)
              (params.keySwitchLevels securityParameter) +
            adversary.queryCount securityParameter)
          (params.keySwitchErrorSampler securityParameter))
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (Adaptive.keySwitchMessageReduction
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (Adaptive.nativeKeySwitchMessage (params.keySwitchGadget securityParameter))
            (params.encode securityParameter)
            (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hLift := ENNReal.ofReal_le_ofReal h
  have hSum := hLift.trans_eq (ENNReal.ofReal_add hCircularNonneg hLWENonneg)
  simpa only [securityGame, directBilinearSecurityGame, batchLWESecurityGame,
    continuationReduction, batchLWEReduction, hEqualNoise securityParameter] using hSum

/-- **Asymptotic adaptive native TFHE security with distinct scalar noises.**

Negligibility of the exact direct-bilinear KDM game and the exact heterogeneous shared-secret
joint-LWE game implies negligible honest adaptive TFHE advantage. -/
theorem secureAgainst_of_directBilinear_and_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction params adversary))
    (hCircular : (directBilinearSecurityGame params).secureAgainst continuationIsPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_directBilinear_add_jointLWE params adversary)
    (negligible_add
      (hCircular _ (hContinuationClosed adversary hadversary))
      (hJointLWE _ (hJointLWEClosed adversary hadversary)))

/-- **Equal-noise asymptotic adaptive native TFHE security, including the circular-key term.**

If the exact direct-bilinear KDM game and the exact query-counted ordinary batch-LWE game are
secure for the reduced efficient families, then the honest adaptive TFHE game has negligible
advantage. The closure premises are the efficiency obligations for the concrete reductions. -/
theorem secureAgainst_of_directBilinear_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hCircular : (directBilinearSecurityGame params).secureAgainst continuationIsPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_directBilinear_add_batchLWE params hEqualNoise adversary)
    (negligible_add
      (hCircular _ (hContinuationClosed adversary hadversary))
      (hBatchLWE _ (hBatchLWEClosed adversary hadversary)))

/-- **Publicly evaluated TFHE security from base TFHE security.**

Any public evaluator using the exposed cloud key preserves adaptive confidentiality.  The sole
closure premise is computational: an efficient evaluated-output adversary must compile to an
efficient base-game adversary.  No decryption, noise bound, or refresh-correctness statement is
used. -/
theorem evaluationSecureAgainst_of_security
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hSecurity : (securityGame params).secureAgainst baseIsPPT) :
    (evaluationSecurityGame params evaluate).secureAgainst evaluationIsPPT := by
  intro adversary hadversary
  exact hSecurity _ (hEvaluationClosed adversary hadversary)

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic
