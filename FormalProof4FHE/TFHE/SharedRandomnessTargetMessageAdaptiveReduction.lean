/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageCloudReduction
import FormalProof4FHE.TFHE.SharedRandomnessTargetMessagePrefixCircLWE
import FormalProof4FHE.TFHE.SampleExtraction
import FormalProof4FHE.TFHE.ScalarSecretRandomization
import FormalProof4FHE.TFHE.CoefficientStructuredLWE

set_option autoImplicit false

/-!
# Joint Module-LWE Reduction for the Target-Message Cloud and Adaptive Input Tape

For positive ring degree, one fresh source-ring module-LWE row can be sample-extracted into one
scalar-LWE row under `KeyExtract(S_source)`.  The reduction samples the independent suffix key and
a fresh suffix mask, appends that mask to the source row, and adds its known suffix inner product
to the body.  Sample extraction then gives a correctly distributed zero-message scalar row under
the complete key `KeyExtract(S_source || S_suffix)`.

Consequently the suffix-only BRK rows, ring-extension rows, and a query-counted adaptive input tape
can all be drawn from one ordinary same-source-secret blocked module-LWE transcript.  The scalar
input error is the constant-coefficient image of the common ring-error sampler.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveReduction

noncomputable section

open FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.CloudReduction

/-! ## Sample-extraction challenge equivalences -/

/-- Applying reciprocal coefficients twice recovers the original positive-degree polynomial. -/
@[simp]
theorem reciprocalCoefficients_involutive
    {R : Type} [AddGroup R] {degree : ℕ}
    (polynomial : Fin (degree + 1) → R) :
    SampleExtraction.reciprocalCoefficients
        (SampleExtraction.reciprocalCoefficients polynomial) = polynomial := by
  funext coefficient
  refine Fin.cases ?_ (fun positive ↦ ?_) coefficient
  · rfl
  · simp [SampleExtraction.reciprocalCoefficients]

/-- A ring mask row is equivalent to its flattened sample-extraction mask. -/
def extractedMaskEquiv (q degree rank : ℕ) :
    (Fin rank → RLWE.Rq q (degree + 1)) ≃
      (Fin (rank * (degree + 1)) → ZMod q) where
  toFun mask := fun coordinate ↦
    let indexed := finProdFinEquiv.symm coordinate
    SampleExtraction.reciprocalCoefficients
      (LatticeCrypto.Poly.toPi (mask indexed.1)) indexed.2
  invFun mask := fun component ↦
    LatticeCrypto.Poly.ofPi
      (SampleExtraction.reciprocalCoefficients fun coefficient ↦
        mask (finProdFinEquiv (component, coefficient)))
  left_inv mask := by
    funext component
    apply LatticeCrypto.Poly.ext_get_eq
    intro coefficient
    simp [LatticeCrypto.Poly.ofPi, LatticeCrypto.Poly.toPi, Vector.get]
  right_inv mask := by
    funext coordinate
    obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
    simp only [LatticeCrypto.Poly.toPi_ofPi, reciprocalCoefficients_involutive,
      Equiv.symm_apply_apply]

/-- Applying `extractedMaskEquiv` is exactly the mask component of native sample extraction. -/
theorem extractedMaskEquiv_apply
    (q degree rank : ℕ)
    (mask : Fin rank → RLWE.Rq q (degree + 1)) :
    extractedMaskEquiv q degree rank mask =
      (SampleExtraction.apply
        (⟨mask, 0⟩ : RingCiphertext q (degree + 1) rank)).mask := by
  rfl

/-- Apply the mask equivalence independently to every column of a batched ring challenge. -/
def extractedChallengeEquiv (q degree rank samples : ℕ) :
    Matrix (Fin rank) (Fin samples) (RLWE.Rq q (degree + 1)) ≃
      Matrix (Fin (rank * (degree + 1))) (Fin samples) (ZMod q) where
  toFun challenge := fun coordinate sample ↦
    extractedMaskEquiv q degree rank (fun component ↦ challenge component sample) coordinate
  invFun challenge := fun component sample ↦
    (extractedMaskEquiv q degree rank).symm
      (fun coordinate ↦ challenge coordinate sample) component
  left_inv challenge := by
    funext component sample
    change ((extractedMaskEquiv q degree rank).symm
      (extractedMaskEquiv q degree rank (fun component ↦ challenge component sample)))
        component = challenge component sample
    exact congrFun ((extractedMaskEquiv q degree rank).symm_apply_apply
      (fun component ↦ challenge component sample)) component
  right_inv challenge := by
    funext coordinate sample
    change (extractedMaskEquiv q degree rank
      ((extractedMaskEquiv q degree rank).symm
        (fun coordinate ↦ challenge coordinate sample))) coordinate =
      challenge coordinate sample
    exact congrFun ((extractedMaskEquiv q degree rank).apply_symm_apply
      (fun coordinate ↦ challenge coordinate sample)) coordinate

/-- Extracting every column of a uniform ring challenge gives a uniform scalar challenge. -/
theorem extractedChallengeEquiv_uniform_evalDist
    (q degree rank samples : ℕ) [NeZero q] :
    evalDist (extractedChallengeEquiv q degree rank samples <$>
      ($ᵗ Matrix (Fin rank) (Fin samples) (RLWE.Rq q (degree + 1)))) =
      evalDist ($ᵗ Matrix (Fin (rank * (degree + 1))) (Fin samples) (ZMod q)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin rank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (β := Matrix (Fin (rank * (degree + 1))) (Fin samples) (ZMod q))
    (extractedChallengeEquiv q degree rank samples)
    (extractedChallengeEquiv q degree rank samples).bijective

/-! ## Batched target-key sample extraction -/

/-- Append source and suffix ring-mask blocks columnwise. -/
def appendChallenge
    {q degree sourceRank suffixRank samples : ℕ}
    (source : Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (suffix : Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))) :
    Matrix (Fin (sourceRank + suffixRank)) (Fin samples) (RLWE.Rq q (degree + 1)) :=
  FormalProof4FHE.SharedRandomness.appendRows source suffix

/-- Appending the two row blocks is an equivalence of finite challenge spaces. -/
def appendChallengeEquiv
    (q degree sourceRank suffixRank samples : ℕ) :
    (Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)) ×
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))) ≃
      Matrix (Fin (sourceRank + suffixRank)) (Fin samples)
        (RLWE.Rq q (degree + 1)) :=
  Equiv.ofBijective
    (fun challenges ↦ appendChallenge challenges.1 challenges.2)
    FormalProof4FHE.SharedRandomness.appendRows_bijective

/-- Appending source/suffix ring masks and sample-extracting is one challenge equivalence. -/
def targetChallengeEquiv
    (q degree sourceRank suffixRank samples : ℕ) :
    (Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)) ×
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))) ≃
      Matrix (Fin ((sourceRank + suffixRank) * (degree + 1)))
        (Fin samples) (ZMod q) :=
  (appendChallengeEquiv q degree sourceRank suffixRank samples).trans
    (extractedChallengeEquiv q degree (sourceRank + suffixRank) samples)

/-- Independently uniform source and suffix ring masks become a uniform target scalar mask. -/
theorem targetChallengeEquiv_uniform_evalDist
    (q degree sourceRank suffixRank samples : ℕ) [NeZero q] :
    evalDist (targetChallengeEquiv q degree sourceRank suffixRank samples <$>
      ($ᵗ (Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)) ×
        Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))))) =
      evalDist ($ᵗ Matrix (Fin ((sourceRank + suffixRank) * (degree + 1)))
        (Fin samples) (ZMod q)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)) ×
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (β := Matrix (Fin ((sourceRank + suffixRank) * (degree + 1)))
      (Fin samples) (ZMod q))
    (targetChallengeEquiv q degree sourceRank suffixRank samples)
    (targetChallengeEquiv q degree sourceRank suffixRank samples).bijective

/-- Complete source-ring rows with a sampled suffix mask and its known suffix-key contribution. -/
def augmentTape
    {q degree sourceRank suffixRank samples : ℕ}
    (suffixSecret : RingBinarySecret suffixRank (degree + 1))
    (suffixChallenge :
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (sourceTape : TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) sourceRank samples) :
    TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) (sourceRank + suffixRank) samples :=
  (appendChallenge sourceTape.1 suffixChallenge,
    sourceTape.2 + vecMul (embedRingSecret q suffixSecret) suffixChallenge)

/-- Sample-extract every row of a target-ring tape. -/
def extractTape
    {q degree rank samples : ℕ}
    (tape : TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) rank samples) :
    TLWE.BatchCiphertext (ZMod q) (rank * (degree + 1)) samples :=
  TLWE.batchOfRows fun sample ↦ SampleExtraction.apply (TLWE.entry tape sample)

/-- Coefficient-zero image of a vector of ring errors. -/
def extractErrors
    {q degree samples : ℕ}
    (errors : Fin samples → RLWE.Rq q (degree + 1)) : Fin samples → ZMod q :=
  fun sample ↦ SampleExtraction.constantCoefficient (errors sample)

/-- Coefficient-zero image of a ring-error sampler. -/
def extractedErrorSampler
    {q degree : ℕ}
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1))) : ProbComp (ZMod q) :=
  SampleExtraction.constantCoefficient <$> errorSampler

/-- Mapping coefficient zero over IID ring errors gives IID extracted scalar errors. -/
theorem extractErrors_sampleIID_evalDist
    {q degree samples : ℕ}
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    evalDist (extractErrors <$> ProbComp.sampleIID samples errorSampler) =
      evalDist (ProbComp.sampleIID samples (extractedErrorSampler errorSampler)) := by
  change evalDist ((fun values coordinate ↦
      SampleExtraction.constantCoefficient (values coordinate)) <$>
        Fin.mOfFn samples (fun _ ↦ errorSampler)) =
    evalDist (Fin.mOfFn samples (fun _ ↦
      SampleExtraction.constantCoefficient <$> errorSampler))
  exact
    (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
      samples (fun _ ↦ errorSampler)
      (fun _ ↦ SampleExtraction.constantCoefficient <$> errorSampler)
      (fun _ ↦ SampleExtraction.constantCoefficient)
      (fun _ ↦ rfl))

/-- Split a positive-degree ring element into its constant coefficient and remaining
coefficients. -/
def constantCoefficientEquiv (q degree : ℕ) :
    RLWE.Rq q (degree + 1) ≃ ZMod q × (Fin degree → ZMod q) :=
  (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q (degree + 1)).trans
    (Fin.consEquiv (fun _ : Fin (degree + 1) ↦ ZMod q)).symm

@[simp]
theorem constantCoefficientEquiv_fst
    (q degree : ℕ) (value : RLWE.Rq q (degree + 1)) :
    (constantCoefficientEquiv q degree value).1 =
      SampleExtraction.constantCoefficient value := by
  rfl

/-- Split every ring output into its scalar constant-coefficient vector and residual vectors. -/
def outputDecompositionEquiv (q degree samples : ℕ) :
    (Fin samples → RLWE.Rq q (degree + 1)) ≃
      (Fin samples → ZMod q) × (Fin samples → Fin degree → ZMod q) where
  toFun output :=
    (fun sample ↦ (constantCoefficientEquiv q degree (output sample)).1,
      fun sample ↦ (constantCoefficientEquiv q degree (output sample)).2)
  invFun output := fun sample ↦
    (constantCoefficientEquiv q degree).symm (output.1 sample, output.2 sample)
  left_inv output := by
    funext sample
    exact (constantCoefficientEquiv q degree).symm_apply_apply (output sample)
  right_inv output := by
    apply Prod.ext
    · funext sample
      exact congrArg Prod.fst
        ((constantCoefficientEquiv q degree).apply_symm_apply
          (output.1 sample, output.2 sample))
    · funext sample
      exact congrArg Prod.snd
        ((constantCoefficientEquiv q degree).apply_symm_apply
          (output.1 sample, output.2 sample))

/-- Constant-coefficient projection of a uniform ring-output vector is uniform. -/
theorem extractErrors_uniform_evalDist
    (q degree samples : ℕ) [NeZero q] :
    evalDist (extractErrors <$>
      ($ᵗ (Fin samples → RLWE.Rq q (degree + 1)))) =
      evalDist ($ᵗ (Fin samples → ZMod q)) := by
  calc
    _ = evalDist (Prod.fst <$> (outputDecompositionEquiv q degree samples <$>
          ($ᵗ (Fin samples → RLWE.Rq q (degree + 1))))) := by
      congr 1
      rw [Functor.map_map]
      apply congrArg (fun transform ↦ transform <$>
        ($ᵗ (Fin samples → RLWE.Rq q (degree + 1))))
      funext output sample
      rfl
    _ = evalDist (Prod.fst <$>
        ($ᵗ ((Fin samples → ZMod q) ×
          (Fin samples → Fin degree → ZMod q)))) := by
      exact evalDist_map_eq_of_evalDist_eq
        (evalDist_map_bijective_uniform_cross
          (α := Fin samples → RLWE.Rq q (degree + 1))
          (β := (Fin samples → ZMod q) ×
            (Fin samples → Fin degree → ZMod q))
          (outputDecompositionEquiv q degree samples)
          (outputDecompositionEquiv q degree samples).bijective) Prod.fst
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- Translation by a fixed ring-output vector is an equivalence. -/
def addOutputEquiv
    {q degree samples : ℕ}
    (shift : Fin samples → RLWE.Rq q (degree + 1)) :
    (Fin samples → RLWE.Rq q (degree + 1)) ≃
      (Fin samples → RLWE.Rq q (degree + 1)) where
  toFun output := output + shift
  invFun output := output - shift
  left_inv output := by
    funext sample
    exact @add_sub_cancel_right (RLWE.Rq q (degree + 1))
      (LatticeCrypto.NegacyclicRing.instAddCommGroupPoly
        (RLWE.negacyclicRing q (degree + 1))).toAddGroup
      (output sample) (shift sample)
  right_inv output := by
    funext sample
    exact @sub_add_cancel (RLWE.Rq q (degree + 1))
      (LatticeCrypto.NegacyclicRing.instAddCommGroupPoly
        (RLWE.negacyclicRing q (degree + 1))).toAddGroup
      (output sample) (shift sample)

/-- A fixed body translation followed by coefficient extraction is still uniform. -/
theorem extractErrors_add_uniform_evalDist
    (q degree samples : ℕ) [NeZero q]
    (shift : Fin samples → RLWE.Rq q (degree + 1)) :
    evalDist (extractErrors <$> (addOutputEquiv shift <$>
      ($ᵗ (Fin samples → RLWE.Rq q (degree + 1))))) =
      evalDist ($ᵗ (Fin samples → ZMod q)) := by
  calc
    _ = evalDist (extractErrors <$>
        ($ᵗ (Fin samples → RLWE.Rq q (degree + 1)))) := by
      exact evalDist_map_eq_of_evalDist_eq
        (evalDist_map_bijective_uniform_cross
          (α := Fin samples → RLWE.Rq q (degree + 1))
          (β := Fin samples → RLWE.Rq q (degree + 1))
          (addOutputEquiv shift) (addOutputEquiv shift).bijective) extractErrors
    _ = _ := extractErrors_uniform_evalDist q degree samples

/-- Selecting a row after batched sample extraction gives native one-row sample extraction. -/
@[simp]
theorem entry_extractTape
    {q degree rank samples : ℕ}
    (tape : TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) rank samples)
    (sample : Fin samples) :
    TLWE.entry (extractTape tape) sample =
      SampleExtraction.apply (TLWE.entry tape sample) := by
  rfl

/-- Coordinate form of augmenting an arbitrary source tape and sample-extracting it. -/
theorem extractTape_augmentTape
    {q degree sourceRank suffixRank samples : ℕ}
    (suffixSecret : RingBinarySecret suffixRank (degree + 1))
    (suffixChallenge :
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (sourceTape :
      TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) sourceRank samples) :
    extractTape (augmentTape suffixSecret suffixChallenge sourceTape) =
      (extractedChallengeEquiv q degree (sourceRank + suffixRank) samples
          (appendChallenge sourceTape.1 suffixChallenge),
        extractErrors
          (sourceTape.2 + vecMul (embedRingSecret q suffixSecret) suffixChallenge)) := by
  rfl

/-- Completing real source rows with a suffix mask gives ordinary zero-message target-ring rows. -/
theorem augmentTape_real
    {q degree sourceRank suffixRank samples : ℕ} [NeZero q]
    (sourceSecret : RingBinarySecret sourceRank (degree + 1))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1))
    (sourceChallenge :
      Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (suffixChallenge :
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (errors : Fin samples → RLWE.Rq q (degree + 1)) :
    augmentTape suffixSecret suffixChallenge
        (sourceChallenge,
          vecMul (embedRingSecret q sourceSecret) sourceChallenge + errors) =
      TLWE.batchAssemble
        (embedRingSecret q (targetRingSecret sourceSecret suffixSecret))
        (appendChallenge sourceChallenge suffixChallenge) 0 errors := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [augmentTape, TLWE.batchAssemble, Pi.add_apply]
    rw [show embedRingSecret q (targetRingSecret sourceSecret suffixSecret) =
        Fin.append (embedRingSecret q sourceSecret) (embedRingSecret q suffixSecret) by
      exact FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.embedRingSecret_appendRingSecret
        q sourceSecret suffixSecret]
    simp only [appendChallenge]
    rw [FormalProof4FHE.SharedRandomness.vecMul_appendRows]
    simp only [Pi.add_apply, Pi.zero_apply]
    abel

/-- Sample extraction maps a deterministic zero-message target-ring batch to the corresponding
scalar batch under `KeyExtract(targetRingSecret)`, with coefficient-zero errors. -/
theorem extractTape_batchAssemble_zero
    {q degree rank samples : ℕ} [NeZero q]
    (secret : RingBinarySecret rank (degree + 1))
    (challenge : Matrix (Fin rank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (errors : Fin samples → RLWE.Rq q (degree + 1)) :
    extractTape (TLWE.batchAssemble (embedRingSecret q secret) challenge 0 errors) =
      TLWE.batchAssemble (embedBinarySecret (keyExtract secret))
        (extractedChallengeEquiv q degree rank samples challenge) 0
        (extractErrors errors) := by
  apply Prod.ext
  · funext coordinate sample
    rfl
  · funext sample
    let ringCiphertext := TLWE.entry
      (TLWE.batchAssemble (embedRingSecret q secret) challenge 0 errors) sample
    have hphase := SampleExtraction.phase_apply_embedRingSecret
      secret ringCiphertext
    have hringPhase :
        TLWE.phase (embedRingSecret q secret) ringCiphertext = errors sample := by
      simp [ringCiphertext, TLWE.batchPhase]
    rw [hringPhase] at hphase
    change (SampleExtraction.apply ringCiphertext).body =
      dotProduct (embedBinarySecret (keyExtract secret))
          (SampleExtraction.apply ringCiphertext).mask + 0 +
        SampleExtraction.constantCoefficient (errors sample)
    unfold TLWE.phase at hphase
    calc
      _ = SampleExtraction.constantCoefficient (errors sample) +
          dotProduct (embedBinarySecret (keyExtract secret))
            (SampleExtraction.apply ringCiphertext).mask :=
        (sub_eq_iff_eq_add.mp hphase)
      _ = _ := by abel

/-- Jointly augmenting and extracting real source rows gives the exact target-key scalar tape. -/
theorem extractTape_augmentTape_real
    {q degree sourceRank suffixRank samples : ℕ} [NeZero q]
    (sourceSecret : RingBinarySecret sourceRank (degree + 1))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1))
    (sourceChallenge :
      Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (suffixChallenge :
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1)))
    (errors : Fin samples → RLWE.Rq q (degree + 1)) :
    extractTape
        (augmentTape suffixSecret suffixChallenge
          (sourceChallenge,
            vecMul (embedRingSecret q sourceSecret) sourceChallenge + errors)) =
      TLWE.batchAssemble
        (embedBinarySecret (targetMessages sourceSecret suffixSecret))
        (extractedChallengeEquiv q degree (sourceRank + suffixRank) samples
          (appendChallenge sourceChallenge suffixChallenge))
        0 (extractErrors errors) := by
  rw [augmentTape_real sourceSecret suffixSecret sourceChallenge suffixChallenge errors]
  exact extractTape_batchAssemble_zero
    (targetRingSecret sourceSecret suffixSecret)
    (appendChallenge sourceChallenge suffixChallenge) errors

/-- Sampling, completing, and extracting source-ring rows gives the native target-key scalar
encryption tape exactly. -/
theorem extractedTargetTape_evalDist_eq_batchEncrypt
    {q degree sourceRank suffixRank samples : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (do
      let sourceChallenge ←
        $ᵗ Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1))
      let suffixChallenge ←
        $ᵗ Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))
      let errors ← ProbComp.sampleIID samples errorSampler
      return extractTape
        (augmentTape suffixSecret suffixChallenge
          (sourceChallenge,
            vecMul (embedRingSecret q sourceSecret) sourceChallenge + errors))) =
      evalDist (TLWE.batchEncrypt
        ((sourceRank + suffixRank) * (degree + 1)) samples
        (extractedErrorSampler errorSampler)
        (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0) := by
  let RingChallenges :=
    Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)) ×
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))
  let ScalarChallenge := Matrix
    (Fin ((sourceRank + suffixRank) * (degree + 1))) (Fin samples) (ZMod q)
  let ringChallenges : ProbComp RingChallenges := do
    let sourceChallenge ←
      $ᵗ Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1))
    let suffixChallenge ←
      $ᵗ Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))
    return (sourceChallenge, suffixChallenge)
  let scalarChallenges : ProbComp ScalarChallenge := $ᵗ ScalarChallenge
  let ringErrors := ProbComp.sampleIID samples errorSampler
  let scalarErrors := ProbComp.sampleIID samples (extractedErrorSampler errorSampler)
  let finish : ScalarChallenge → (Fin samples → ZMod q) →
      ProbComp (TLWE.BatchCiphertext (ZMod q)
        ((sourceRank + suffixRank) * (degree + 1)) samples) :=
    fun challenge errors ↦
    pure (TLWE.batchAssemble
      (embedBinarySecret (targetMessages sourceSecret suffixSecret))
      challenge 0 errors)
  have hChallenges :
      evalDist (targetChallengeEquiv q degree sourceRank suffixRank samples <$>
        ringChallenges) = evalDist scalarChallenges := by
    have uniformProduct :
        ($ᵗ RingChallenges : ProbComp RingChallenges) =
          Prod.mk <$>
            ($ᵗ Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1))) <*>
            ($ᵗ Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))) := rfl
    have hRingChallenges : evalDist ringChallenges =
        evalDist ($ᵗ RingChallenges) := by
      rw [uniformProduct]
      simp [ringChallenges, monad_norm]
    calc
      _ = evalDist (targetChallengeEquiv q degree sourceRank suffixRank samples <$>
          ($ᵗ RingChallenges)) :=
        evalDist_map_eq_of_evalDist_eq hRingChallenges _
      _ = _ := by
        simpa [scalarChallenges, RingChallenges, ScalarChallenge] using
          (targetChallengeEquiv_uniform_evalDist q degree sourceRank suffixRank samples)
  have hErrors : evalDist (extractErrors <$> ringErrors) = evalDist scalarErrors := by
    simpa [ringErrors, scalarErrors] using
      (extractErrors_sampleIID_evalDist (samples := samples) errorSampler)
  calc
    _ = evalDist (ringChallenges >>= fun challenges ↦
        ringErrors >>= fun errors ↦
        finish (targetChallengeEquiv q degree sourceRank suffixRank samples challenges)
          (extractErrors errors)) := by
      simp_rw [extractTape_augmentTape_real]
      simp [ringChallenges, ringErrors, finish, RingChallenges,
        targetChallengeEquiv, appendChallengeEquiv, monad_norm]
    _ = evalDist ((targetChallengeEquiv q degree sourceRank suffixRank samples <$>
          ringChallenges) >>= fun challenge ↦
        (extractErrors <$> ringErrors) >>= fun errors ↦ finish challenge errors) := by
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      rfl
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        (extractErrors <$> ringErrors) >>= fun errors ↦ finish challenge errors) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hChallenges (fun challenge ↦
          (extractErrors <$> ringErrors) >>= fun errors ↦ finish challenge errors)
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        scalarErrors >>= fun errors ↦ finish challenge errors) := by
      refine evalDist_bind_congr' scalarChallenges fun challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hErrors (finish challenge)
    _ = _ := by
      simp [TLWE.batchEncrypt, scalarChallenges, scalarErrors, finish, ScalarChallenge]

/-- Uniform source masks and bodies, completed by a fresh suffix mask and then sample-extracted,
give a uniform target-key scalar tape. -/
theorem augmentExtract_uniform_evalDist
    (q degree sourceRank suffixRank samples : ℕ) [NeZero q]
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (do
      let sourceChallenge ←
        $ᵗ Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1))
      let suffixChallenge ←
        $ᵗ Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))
      let sourceOutput ← $ᵗ (Fin samples → RLWE.Rq q (degree + 1))
      return extractTape
        (augmentTape suffixSecret suffixChallenge (sourceChallenge, sourceOutput))) =
      evalDist ($ᵗ (TLWE.BatchCiphertext (ZMod q)
        ((sourceRank + suffixRank) * (degree + 1)) samples)) := by
  let RingChallenges :=
    Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1)) ×
      Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))
  let ScalarChallenge := Matrix
    (Fin ((sourceRank + suffixRank) * (degree + 1))) (Fin samples) (ZMod q)
  let ScalarOutput := Fin samples → ZMod q
  let ringChallenges : ProbComp RingChallenges := do
    let sourceChallenge ←
      $ᵗ Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1))
    let suffixChallenge ←
      $ᵗ Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))
    return (sourceChallenge, suffixChallenge)
  let sourceOutputs : ProbComp (Fin samples → RLWE.Rq q (degree + 1)) :=
    $ᵗ (Fin samples → RLWE.Rq q (degree + 1))
  let scalarChallenges : ProbComp ScalarChallenge := $ᵗ ScalarChallenge
  let scalarOutputs : ProbComp ScalarOutput := $ᵗ ScalarOutput
  let finish : ScalarChallenge → ScalarOutput →
      ProbComp (ScalarChallenge × ScalarOutput) :=
    fun challenge output ↦ pure (challenge, output)
  have hChallenges :
      evalDist (targetChallengeEquiv q degree sourceRank suffixRank samples <$>
        ringChallenges) = evalDist scalarChallenges := by
    have uniformProduct :
        ($ᵗ RingChallenges : ProbComp RingChallenges) =
          Prod.mk <$>
            ($ᵗ Matrix (Fin sourceRank) (Fin samples) (RLWE.Rq q (degree + 1))) <*>
            ($ᵗ Matrix (Fin suffixRank) (Fin samples) (RLWE.Rq q (degree + 1))) := rfl
    have hRingChallenges : evalDist ringChallenges =
        evalDist ($ᵗ RingChallenges) := by
      rw [uniformProduct]
      simp [ringChallenges, monad_norm]
    calc
      _ = evalDist (targetChallengeEquiv q degree sourceRank suffixRank samples <$>
          ($ᵗ RingChallenges)) := evalDist_map_eq_of_evalDist_eq hRingChallenges _
      _ = _ := by
        simpa [scalarChallenges, RingChallenges, ScalarChallenge] using
          (targetChallengeEquiv_uniform_evalDist q degree sourceRank suffixRank samples)
  have hOutputs (challenges : RingChallenges) :
      evalDist ((fun output ↦ extractErrors
          (addOutputEquiv
            (vecMul (embedRingSecret q suffixSecret) challenges.2) output)) <$>
        sourceOutputs) = evalDist scalarOutputs := by
    simpa [sourceOutputs, scalarOutputs, ScalarOutput] using
      (extractErrors_add_uniform_evalDist q degree samples
        (vecMul (embedRingSecret q suffixSecret) challenges.2))
  calc
    _ = evalDist (ringChallenges >>= fun challenges ↦
        sourceOutputs >>= fun sourceOutput ↦
        finish (targetChallengeEquiv q degree sourceRank suffixRank samples challenges)
          (extractErrors (addOutputEquiv
            (vecMul (embedRingSecret q suffixSecret) challenges.2) sourceOutput))) := by
      simp_rw [extractTape_augmentTape]
      congr 1
      simp [ringChallenges, sourceOutputs, finish, targetChallengeEquiv,
        appendChallengeEquiv, addOutputEquiv, monad_norm]
    _ = evalDist (ringChallenges >>= fun challenges ↦
        ((fun sourceOutput ↦ extractErrors (addOutputEquiv
          (vecMul (embedRingSecret q suffixSecret) challenges.2) sourceOutput)) <$>
            sourceOutputs) >>= fun output ↦
        finish (targetChallengeEquiv q degree sourceRank suffixRank samples challenges)
          output) := by
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (ringChallenges >>= fun challenges ↦
        scalarOutputs >>= fun output ↦
        finish (targetChallengeEquiv q degree sourceRank suffixRank samples challenges)
          output) := by
      refine evalDist_bind_congr' ringChallenges fun challenges ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (hOutputs challenges)
        (fun output ↦ finish
          (targetChallengeEquiv q degree sourceRank suffixRank samples challenges) output)
    _ = evalDist ((targetChallengeEquiv q degree sourceRank suffixRank samples <$>
          ringChallenges) >>= fun challenge ↦
        scalarOutputs >>= fun output ↦ finish challenge output) := by
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      rfl
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        scalarOutputs >>= fun output ↦ finish challenge output) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hChallenges (fun challenge ↦
          scalarOutputs >>= fun output ↦ finish challenge output)
    _ = _ := by
      have uniformProduct :
          ($ᵗ (ScalarChallenge × ScalarOutput) :
            ProbComp (ScalarChallenge × ScalarOutput)) =
            Prod.mk <$> scalarChallenges <*> scalarOutputs := rfl
      rw [uniformProduct]
      simp [finish, monad_norm]

/-! ## One joint module-LWE problem -/

/-- Source-ring challenge block reserved for the query-counted input tape. -/
abbrev TapeChallenge
    (q degree sourceRank queryCount : ℕ) :=
  Matrix (Fin sourceRank) (Fin queryCount) (RLWE.Rq q (degree + 1))

/-- Source-ring right-hand sides reserved for the query-counted input tape. -/
abbrev TapeOutput
    (q degree queryCount : ℕ) :=
  Fin queryCount → RLWE.Rq q (degree + 1)

/-- The cloud challenge blocks and input-tape block under one source ring key. -/
abbrev JointChallenge
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  CloudReduction.Challenge q (degree + 1) sourceRank suffixRank tgswLevels ×
    TapeChallenge q degree sourceRank queryCount

/-- The cloud right-hand sides and input-tape right-hand sides. -/
abbrev JointOutput
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  CloudReduction.Output q (degree + 1) sourceRank suffixRank tgswLevels ×
    TapeOutput q degree queryCount

/-- Complete blocked transcript used by the adaptive suffix reductions. -/
abbrev JointTranscript
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  JointChallenge q degree sourceRank suffixRank tgswLevels queryCount ×
    JointOutput q degree sourceRank suffixRank tgswLevels queryCount

/-- Regroup a joint transcript into its cloud and source-tape transcript components. -/
def jointTranscriptRegroupEquiv
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :
    JointTranscript q degree sourceRank suffixRank tgswLevels queryCount ≃
      CloudReduction.Transcript q (degree + 1) sourceRank suffixRank tgswLevels ×
        TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) sourceRank queryCount where
  toFun transcript :=
    ((transcript.1.1, transcript.2.1), (transcript.1.2, transcript.2.2))
  invFun transcripts :=
    ((transcripts.1.1, transcripts.2.1), (transcripts.1.2, transcripts.2.2))
  left_inv transcript := by
    rcases transcript with ⟨⟨cloudChallenge, tapeChallenge⟩,
      cloudOutput, tapeOutput⟩
    rfl
  right_inv transcripts := by
    rcases transcripts with ⟨⟨cloudChallenge, cloudOutput⟩,
      tapeChallenge, tapeOutput⟩
    rfl

/-- Ordinary same-source-secret module-LWE simultaneously supplying every acyclic cloud row and
every adaptive input-tape row.  All three blocks use the same ring-error sampler. -/
def problem
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    LearningWithErrors.Problem
      (JointChallenge q degree sourceRank suffixRank tgswLevels queryCount)
      (RingBinarySecret sourceRank (degree + 1))
      (JointOutput q degree sourceRank suffixRank tgswLevels queryCount) where
  sampleChallenge :=
    $ᵗ (JointChallenge q degree sourceRank suffixRank tgswLevels queryCount)
  sampleSecret := Native.sampleRingSecret sourceRank (degree + 1)
  sampleError := do
    let bootstrapError ← Fin.mOfFn
      (targetScalarDimension sourceRank suffixRank (degree + 1)) fun _ ↦
        ProbComp.sampleIID (TGSW.rowCount sourceRank tgswLevels) errorSampler
    let extensionError ←
      ProbComp.sampleIID (suffixRank * tgswLevels) errorSampler
    let tapeError ← ProbComp.sampleIID queryCount errorSampler
    return ((bootstrapError, extensionError), tapeError)
  noiseless := fun sourceSecret challenge ↦
    ((fun coordinate ↦
        vecMul (embedRingSecret q sourceSecret) (challenge.1.1 coordinate),
      vecMul (embedRingSecret q sourceSecret) challenge.1.2),
      vecMul (embedRingSecret q sourceSecret) challenge.2)
  sampleUniform :=
    $ᵗ (JointOutput q degree sourceRank suffixRank tgswLevels queryCount)

/-- Public output of the joint conversion: source BRK, extension table, and extracted target-key
input tape. -/
abbrev AdaptiveView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) :=
  (SourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels ×
      RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels) ×
    TLWE.BatchCiphertext (ZMod q)
      (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount

/-- Convert one homogeneous joint transcript using only sampled suffix data. -/
def convertView
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ)
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (messages : BinarySecret
      (targetScalarDimension sourceRank suffixRank (degree + 1)))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1))
    (suffixChallenge : Matrix (Fin suffixRank) (Fin queryCount)
      (RLWE.Rq q (degree + 1)))
    (transcript : JointTranscript q degree sourceRank suffixRank tgswLevels queryCount) :
    AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount :=
  let split := jointTranscriptRegroupEquiv q degree sourceRank suffixRank
    tgswLevels queryCount transcript
  let cloud := CloudReduction.cloudViewEquiv q (degree + 1) sourceRank suffixRank
    tgswLevels gadget messages
    (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
      q (degree + 1) suffixRank tgswLevels gadget suffixSecret) split.1
  (cloud, extractTape (augmentTape suffixSecret suffixChallenge split.2))

/-- Execute the actual adaptive adversary from a fully public converted view. -/
def adaptiveViewContinuation
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels)
    (view : AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount) :
    ProbComp Bool := do
  let cloudKey : CloudKey q (degree + 1) sourceRank suffixRank tgswLevels :=
    ⟨deriveBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels
      decompose view.1.1 view.1.2⟩
  let bit ← $ᵗ Bool
  let guess ← runFromTranscript bit encode adversary cloudKey view.2
  return bit == guess

/-- Joint module-LWE reduction for the suffix-only BRK branch. -/
def suffixReduction
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    LearningWithErrors.Adversary
      (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler) :=
  fun transcript ↦ do
    let suffixSecret ← Native.sampleRingSecret suffixRank (degree + 1)
    let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
      (RLWE.Rq q (degree + 1))
    adaptiveViewContinuation decompose encode adversary
      (convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
        (suffixOnlyMessages suffixSecret) suffixSecret suffixChallenge transcript)

/-- Joint module-LWE reduction for the all-zero source-BRK branch. -/
def zeroReduction
    {Message : Type}
    {q degree sourceRank suffixRank tgswLevels queryCount : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    LearningWithErrors.Adversary
      (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler) :=
  fun transcript ↦ do
    let suffixSecret ← Native.sampleRingSecret suffixRank (degree + 1)
    let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
      (RLWE.Rq q (degree + 1))
    adaptiveViewContinuation decompose encode adversary
      (convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
        (fun _ ↦ false) suffixSecret suffixChallenge transcript)

/-! ## Uniform endpoint -/

/-- The blocked uniform branch of the joint problem is the canonical uniform transcript. -/
theorem problem_uniformDistr_eq_uniformSample
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    LearningWithErrors.uniformDistr
        (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler) =
      ($ᵗ (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)) := by
  unfold LearningWithErrors.uniformDistr problem
  have uniformProduct :
      ($ᵗ (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount) :
        ProbComp
          (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)) =
      Prod.mk <$>
        ($ᵗ (JointChallenge q degree sourceRank suffixRank tgswLevels queryCount)) <*>
        ($ᵗ (JointOutput q degree sourceRank suffixRank tgswLevels queryCount)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- Sampling a uniform source-ring tape as one product, completing it with an independent suffix
mask, and sample-extracting is the same uniform scalar tape proved above. -/
theorem augmentExtract_uniformTape_evalDist
    (q degree sourceRank suffixRank queryCount : ℕ) [NeZero q]
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (do
      let sourceTape ← $ᵗ (TLWE.BatchCiphertext
        (RLWE.Rq q (degree + 1)) sourceRank queryCount)
      let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1))
      return extractTape (augmentTape suffixSecret suffixChallenge sourceTape)) =
      evalDist ($ᵗ (TLWE.BatchCiphertext (ZMod q)
        ((sourceRank + suffixRank) * (degree + 1)) queryCount)) := by
  let SourceChallenge :=
    Matrix (Fin sourceRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let SourceOutput := Fin queryCount → RLWE.Rq q (degree + 1)
  let sourceChallenges : ProbComp SourceChallenge := $ᵗ SourceChallenge
  let sourceOutputs : ProbComp SourceOutput := $ᵗ SourceOutput
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let finish := fun (sourceChallenge : SourceChallenge)
      (suffixChallenge : Matrix (Fin suffixRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1))) (sourceOutput : SourceOutput) ↦
    (pure (extractTape
      (augmentTape suffixSecret suffixChallenge (sourceChallenge, sourceOutput))) :
      ProbComp (TLWE.BatchCiphertext (ZMod q)
        ((sourceRank + suffixRank) * (degree + 1)) queryCount))
  have uniformSourceTape :
      ($ᵗ (TLWE.BatchCiphertext
          (RLWE.Rq q (degree + 1)) sourceRank queryCount) :
        ProbComp (TLWE.BatchCiphertext
          (RLWE.Rq q (degree + 1)) sourceRank queryCount)) =
        Prod.mk <$> sourceChallenges <*> sourceOutputs := rfl
  calc
    _ = evalDist (sourceChallenges >>= fun sourceChallenge ↦
        sourceOutputs >>= fun sourceOutput ↦
        suffixChallenges >>= fun suffixChallenge ↦
        finish sourceChallenge suffixChallenge sourceOutput) := by
      rw [uniformSourceTape]
      simp [sourceChallenges, sourceOutputs, suffixChallenges, finish, monad_norm]
    _ = evalDist (sourceChallenges >>= fun sourceChallenge ↦
        suffixChallenges >>= fun suffixChallenge ↦
        sourceOutputs >>= fun sourceOutput ↦
        finish sourceChallenge suffixChallenge sourceOutput) := by
      refine evalDist_bind_congr' sourceChallenges fun sourceChallenge ↦ ?_
      exact evalDist_bind_bind_swap sourceOutputs suffixChallenges
        (fun sourceOutput suffixChallenge ↦
          finish sourceChallenge suffixChallenge sourceOutput)
    _ = _ := by
      simpa [sourceChallenges, sourceOutputs, suffixChallenges, finish] using
        (augmentExtract_uniform_evalDist q degree sourceRank suffixRank queryCount
          suffixSecret)

/-- For fixed suffix data, the complete public conversion maps the joint uniform module-LWE
transcript to an independent uniform cloud view and uniform target-key scalar tape. -/
theorem convertView_uniform_evalDist
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (messages : BinarySecret
      (targetScalarDimension sourceRank suffixRank (degree + 1)))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (do
      let transcript ←
        $ᵗ (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)
      let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1))
      return convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
        messages suffixSecret suffixChallenge transcript) =
      evalDist ($ᵗ (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount)) := by
  let CloudTranscript :=
    CloudReduction.Transcript q (degree + 1) sourceRank suffixRank tgswLevels
  let SourceTape :=
    TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) sourceRank queryCount
  let CloudView :=
    SourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels ×
      RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
  let ScalarTape := TLWE.BatchCiphertext (ZMod q)
    ((sourceRank + suffixRank) * (degree + 1)) queryCount
  let transcripts : ProbComp
      (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount) :=
    $ᵗ (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)
  let splitTranscripts : ProbComp (CloudTranscript × SourceTape) :=
    $ᵗ (CloudTranscript × SourceTape)
  let cloudTranscripts : ProbComp CloudTranscript := $ᵗ CloudTranscript
  let sourceTapes : ProbComp SourceTape := $ᵗ SourceTape
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let cloudViews : ProbComp CloudView := $ᵗ CloudView
  let scalarTapes : ProbComp ScalarTape := $ᵗ ScalarTape
  let cloudMap := CloudReduction.cloudViewEquiv q (degree + 1) sourceRank suffixRank
    tgswLevels gadget messages
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q (degree + 1) suffixRank tgswLevels gadget suffixSecret)
  let tapeSampler : ProbComp ScalarTape := do
    let sourceTape ← sourceTapes
    let suffixChallenge ← suffixChallenges
    return extractTape (augmentTape suffixSecret suffixChallenge sourceTape)
  let finish := fun (cloud : CloudView) (tape : ScalarTape) ↦
    (pure (cloud, tape) : ProbComp (CloudView × ScalarTape))
  have hSplit : evalDist
      (jointTranscriptRegroupEquiv q degree sourceRank suffixRank tgswLevels queryCount <$>
        transcripts) = evalDist splitTranscripts := by
    exact evalDist_map_bijective_uniform_cross
      (α := JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)
      (β := CloudTranscript × SourceTape)
      (jointTranscriptRegroupEquiv q degree sourceRank suffixRank tgswLevels queryCount)
      (jointTranscriptRegroupEquiv q degree sourceRank suffixRank tgswLevels
        queryCount).bijective
  have hCloud : evalDist (cloudMap <$> cloudTranscripts) = evalDist cloudViews := by
    simpa [cloudMap, cloudTranscripts, cloudViews, CloudTranscript, CloudView] using
      (CloudReduction.cloudViewEquiv_uniform_evalDist q (degree + 1) sourceRank
        suffixRank tgswLevels gadget messages
        (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
          q (degree + 1) suffixRank tgswLevels gadget suffixSecret))
  have hTape : evalDist tapeSampler = evalDist scalarTapes := by
    simpa [tapeSampler, sourceTapes, suffixChallenges, scalarTapes, SourceTape,
      ScalarTape] using
      (augmentExtract_uniformTape_evalDist q degree sourceRank suffixRank queryCount
        suffixSecret)
  have uniformSplit : splitTranscripts =
      Prod.mk <$> cloudTranscripts <*> sourceTapes := rfl
  have uniformView :
      ($ᵗ (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount) :
        ProbComp (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount)) =
      Prod.mk <$> cloudViews <*> scalarTapes := rfl
  calc
    _ = evalDist ((jointTranscriptRegroupEquiv q degree sourceRank suffixRank
          tgswLevels queryCount <$> transcripts) >>= fun split ↦
        suffixChallenges >>= fun suffixChallenge ↦
        finish (cloudMap split.1)
          (extractTape (augmentTape suffixSecret suffixChallenge split.2))) := by
      simp [transcripts, suffixChallenges, finish, convertView, cloudMap,
        map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (splitTranscripts >>= fun split ↦
        suffixChallenges >>= fun suffixChallenge ↦
        finish (cloudMap split.1)
          (extractTape (augmentTape suffixSecret suffixChallenge split.2))) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSplit _
    _ = evalDist (cloudTranscripts >>= fun cloudTranscript ↦
        tapeSampler >>= fun tape ↦ finish (cloudMap cloudTranscript) tape) := by
      rw [uniformSplit]
      simp [tapeSampler, finish, bind_assoc, monad_norm]
    _ = evalDist ((cloudMap <$> cloudTranscripts) >>= fun cloud ↦
        tapeSampler >>= fun tape ↦ finish cloud tape) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
      rfl
    _ = evalDist (cloudViews >>= fun cloud ↦
        tapeSampler >>= fun tape ↦ finish cloud tape) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hCloud _
    _ = evalDist (cloudViews >>= fun cloud ↦
        scalarTapes >>= fun tape ↦ finish cloud tape) := by
      refine evalDist_bind_congr' cloudViews fun cloud ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hTape
        (finish cloud)
    _ = _ := by
      rw [uniformView]
      simp [finish, monad_norm]

/-- Common fully uniform cloud-plus-target-tape endpoint. -/
def uniformGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ProbComp Bool := do
  let view ← $ᵗ (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount)
  adaptiveViewContinuation decompose encode adversary view

/-- The suffix-only reduction has the common fully uniform endpoint. -/
theorem suffixReduction_game1_evalDist_eq_uniform
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist (LearningWithErrors.game1
        (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
        (suffixReduction gadget decompose encode adversary)) =
      evalDist (uniformGame q degree sourceRank suffixRank tgswLevels queryCount
        decompose encode adversary) := by
  rw [LearningWithErrors.game1,
    problem_uniformDistr_eq_uniformSample q degree sourceRank suffixRank tgswLevels
      queryCount]
  let transcripts : ProbComp
      (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount) :=
    $ᵗ (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)
  let suffixes := Native.sampleRingSecret suffixRank (degree + 1)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let views : ProbComp
      (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount) :=
    $ᵗ (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount)
  let finish :
      AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount → ProbComp Bool :=
    adaptiveViewContinuation decompose encode adversary
  calc
    evalDist (transcripts >>= suffixReduction gadget decompose encode adversary) =
        evalDist (suffixes >>= fun suffixSecret ↦
          transcripts >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
            (suffixOnlyMessages suffixSecret) suffixSecret suffixChallenge transcript)) := by
      simpa [transcripts, suffixes, suffixChallenges, finish, suffixReduction] using
        (evalDist_bind_bind_swap transcripts suffixes
          (fun transcript suffixSecret ↦
            suffixChallenges >>= fun suffixChallenge ↦
            finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
              gadget (suffixOnlyMessages suffixSecret) suffixSecret suffixChallenge
              transcript)))
    _ = evalDist (suffixes >>= fun _ ↦ views >>= finish) := by
      refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
      simpa [transcripts, suffixChallenges, views, bind_assoc, monad_norm] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (convertView_uniform_evalDist q degree sourceRank suffixRank tgswLevels
            queryCount gadget (suffixOnlyMessages suffixSecret) suffixSecret)
          finish)
    _ = evalDist (views >>= finish) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        suffixes (by simp [suffixes]) (views >>= finish)
    _ = _ := by
      simp [uniformGame, views, finish]

/-- The zero-BRK reduction has the identical fully uniform endpoint. -/
theorem zeroReduction_game1_evalDist_eq_uniform
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist (LearningWithErrors.game1
        (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
        (zeroReduction gadget decompose encode adversary)) =
      evalDist (uniformGame q degree sourceRank suffixRank tgswLevels queryCount
        decompose encode adversary) := by
  rw [LearningWithErrors.game1,
    problem_uniformDistr_eq_uniformSample q degree sourceRank suffixRank tgswLevels
      queryCount]
  let transcripts : ProbComp
      (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount) :=
    $ᵗ (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount)
  let suffixes := Native.sampleRingSecret suffixRank (degree + 1)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let views : ProbComp
      (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount) :=
    $ᵗ (AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount)
  let finish :
      AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount → ProbComp Bool :=
    adaptiveViewContinuation decompose encode adversary
  calc
    evalDist (transcripts >>= zeroReduction gadget decompose encode adversary) =
        evalDist (suffixes >>= fun suffixSecret ↦
          transcripts >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
            (fun _ ↦ false) suffixSecret suffixChallenge transcript)) := by
      simpa [transcripts, suffixes, suffixChallenges, finish, zeroReduction] using
        (evalDist_bind_bind_swap transcripts suffixes
          (fun transcript suffixSecret ↦
            suffixChallenges >>= fun suffixChallenge ↦
            finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
              gadget (fun _ ↦ false) suffixSecret suffixChallenge transcript)))
    _ = evalDist (suffixes >>= fun _ ↦ views >>= finish) := by
      refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
      simpa [transcripts, suffixChallenges, views, bind_assoc, monad_norm] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (convertView_uniform_evalDist q degree sourceRank suffixRank tgswLevels
            queryCount gadget (fun _ ↦ false) suffixSecret)
          finish)
    _ = evalDist (views >>= finish) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        suffixes (by simp [suffixes]) (views >>= finish)
    _ = _ := by
      simp [uniformGame, views, finish]

/-! ## Fixed-secret real conversion -/

/-- Fixed-source real cloud transcript before its public message translations. -/
def fixedCloudRealTranscript
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1)) :
    ProbComp
      (CloudReduction.Transcript q (degree + 1) sourceRank suffixRank tgswLevels) := do
  let challenge ←
    (CloudReduction.problem q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler).sampleChallenge
  let error ←
    (CloudReduction.problem q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler).sampleError
  return (challenge,
    (CloudReduction.problem q (degree + 1) sourceRank suffixRank tgswLevels
      errorSampler).noiseless sourceSecret challenge + error)

/-- At fixed nested keys, translating the homogeneous real cloud transcript produces exactly the
native source BRK with the selected message vector and the real ring-extension table. -/
theorem cloudViewEquiv_fixedReal_evalDist
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (messages : BinarySecret
      (targetScalarDimension sourceRank suffixRank (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (CloudReduction.cloudViewEquiv q (degree + 1) sourceRank suffixRank
        tgswLevels gadget messages
        (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
          q (degree + 1) suffixRank tgswLevels gadget suffixSecret) <$>
      fixedCloudRealTranscript q degree sourceRank suffixRank tgswLevels
        errorSampler sourceSecret) =
      evalDist (do
        let bootstrappingKey ← Native.generateBootstrappingKey q (degree + 1)
          sourceRank tgswLevels
          (targetScalarDimension sourceRank suffixRank (degree + 1))
          errorSampler gadget messages sourceSecret
        let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank
          suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret
        return (bootstrappingKey, extensionKey)) := by
  let FirstChallenge := CloudReduction.BootstrapChallenge q (degree + 1)
    sourceRank suffixRank tgswLevels
  let FirstError := CloudReduction.BootstrapOutput q (degree + 1)
    sourceRank suffixRank tgswLevels
  let SecondChallenge := CloudReduction.ExtensionChallenge q (degree + 1)
    sourceRank suffixRank tgswLevels
  let SecondError := CloudReduction.ExtensionOutput q (degree + 1)
    suffixRank tgswLevels
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let nativeFirstChallenges : ProbComp FirstChallenge := Fin.mOfFn
    (targetScalarDimension sourceRank suffixRank (degree + 1)) fun _ ↦
      $ᵗ Matrix (Fin sourceRank) (Fin (TGSW.rowCount sourceRank tgswLevels))
        (RLWE.Rq q (degree + 1))
  let firstErrors : ProbComp FirstError := Fin.mOfFn
    (targetScalarDimension sourceRank suffixRank (degree + 1)) fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount sourceRank tgswLevels) errorSampler
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID (suffixRank * tgswLevels) errorSampler
  let finish := fun (firstChallenge : FirstChallenge) (firstError : FirstError)
      (secondChallenge : SecondChallenge) (secondError : SecondError) ↦
    let firstTranscript : Native.BootstrapCutSecurity.ParallelTranscript
        (RLWE.Rq q (degree + 1)) sourceRank tgswLevels
        (targetScalarDimension sourceRank suffixRank (degree + 1)) :=
      (firstChallenge, fun coordinate ↦
        Native.BootstrapCutSecurity.semiringRqPiAdd q (degree + 1)
          (vecMul (embedRingSecret q sourceSecret) (firstChallenge coordinate))
          (firstError coordinate))
    let bootstrappingKey := fun coordinate ↦ TGSW.addGadget gadget
      (embedConstantBit q (degree + 1) (messages coordinate))
      (Native.BootstrapCutSecurity.transcriptToBootstrappingKey
        firstTranscript coordinate)
    let extensionKey := TLWE.batchAssemble (embedRingSecret q sourceSecret)
      secondChallenge
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q (degree + 1) suffixRank tgswLevels gadget suffixSecret) secondError
    (pure (bootstrappingKey, extensionKey) :
      ProbComp
        (SourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels ×
          RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels))
  have hFirstChallenges : evalDist nativeFirstChallenges = evalDist firstChallenges := by
    simpa [nativeFirstChallenges, firstChallenges, FirstChallenge,
      CloudReduction.BootstrapChallenge, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin sourceRank) (Fin (TGSW.rowCount sourceRank tgswLevels))
          (RLWE.Rq q (degree + 1)))
        (targetScalarDimension sourceRank suffixRank (degree + 1)))
  have hRight : evalDist (do
        let bootstrappingKey ← Native.generateBootstrappingKey q (degree + 1)
          sourceRank tgswLevels
          (targetScalarDimension sourceRank suffixRank (degree + 1))
          errorSampler gadget messages sourceSecret
        let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank
          suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret
        return (bootstrappingKey, extensionKey)) =
      evalDist (firstChallenges >>= fun firstChallenge ↦
        firstErrors >>= fun firstError ↦
        secondChallenges >>= fun secondChallenge ↦
        secondErrors >>= fun secondError ↦
        finish firstChallenge firstError secondChallenge secondError) := by
    calc
      _ = evalDist (Native.BootstrapCutSecurity.sampleParallelRealBootstrap q
            (degree + 1) sourceRank tgswLevels
            (targetScalarDimension sourceRank suffixRank (degree + 1))
            errorSampler gadget messages sourceSecret >>= fun bootstrappingKey ↦
          generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
              errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
            pure (bootstrappingKey, extensionKey)) := by
        rw [evalDist_bind, evalDist_bind,
          Native.BootstrapCutSecurity.generateBootstrappingKey_evalDist_eq_parallel
            q (degree + 1) sourceRank tgswLevels
            (targetScalarDimension sourceRank suffixRank (degree + 1))
            errorSampler gadget messages sourceSecret]
      _ = evalDist (nativeFirstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish firstChallenge firstError secondChallenge secondError) := by
        simp [Native.BootstrapCutSecurity.sampleParallelRealBootstrap,
          Native.BootstrapCutSecurity.sampleParallelHomogeneous,
          generateRingExtensionKey,
          FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateRingKeySwitchKey,
          TLWE.batchEncrypt, nativeFirstChallenges, firstErrors, secondChallenges,
          secondErrors, finish, FirstChallenge, FirstError, SecondChallenge, SecondError,
          Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add, bind_assoc, monad_norm]
      _ = _ := by
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          hFirstChallenges (fun firstChallenge ↦
            firstErrors >>= fun firstError ↦
            secondChallenges >>= fun secondChallenge ↦
            secondErrors >>= fun secondError ↦
            finish firstChallenge firstError secondChallenge secondError)
  have hLeft : evalDist
      (CloudReduction.cloudViewEquiv q (degree + 1) sourceRank suffixRank
          tgswLevels gadget messages
          (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
            q (degree + 1) suffixRank tgswLevels gadget suffixSecret) <$>
        fixedCloudRealTranscript q degree sourceRank suffixRank tgswLevels
          errorSampler sourceSecret) =
      evalDist (firstChallenges >>= fun firstChallenge ↦
        secondChallenges >>= fun secondChallenge ↦
        firstErrors >>= fun firstError ↦
        secondErrors >>= fun secondError ↦
        finish firstChallenge firstError secondChallenge secondError) := by
    have uniformChallengeProduct :
        ($ᵗ (CloudReduction.Challenge q (degree + 1) sourceRank suffixRank
            tgswLevels) :
          ProbComp (CloudReduction.Challenge q (degree + 1) sourceRank suffixRank
            tgswLevels)) =
          Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    unfold fixedCloudRealTranscript
    simp only [CloudReduction.problem]
    rw [uniformChallengeProduct]
    simp [CloudReduction.cloudViewEquiv, CloudReduction.regroupEquiv,
      CloudReduction.bootstrappingKeyEquiv_apply, CloudReduction.extensionKeyEquiv_real,
      firstChallenges, firstErrors, secondChallenges, secondErrors, finish,
      FirstChallenge, FirstError, SecondChallenge, SecondError,
      Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add,
      Native.BootstrapCutSecurity.pointwiseAdd_eq_add, bind_assoc, monad_norm]
  rw [hLeft, hRight]
  refine evalDist_bind_congr' firstChallenges fun firstChallenge ↦ ?_
  exact evalDist_bind_bind_swap secondChallenges firstErrors
    (fun secondChallenge firstError ↦
      secondErrors >>= fun secondError ↦
      finish firstChallenge firstError secondChallenge secondError)

/-- The source-tape sampler may be packaged before sampling the independent suffix mask without
changing the exact sample-extraction identity. -/
theorem augmentExtract_realTape_evalDist
    (q degree sourceRank suffixRank queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (do
      let sourceTape ← TLWE.batchEncrypt sourceRank queryCount errorSampler
        (embedRingSecret q sourceSecret) 0
      let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1))
      return extractTape (augmentTape suffixSecret suffixChallenge sourceTape)) =
      evalDist (TLWE.batchEncrypt
        ((sourceRank + suffixRank) * (degree + 1)) queryCount
        (extractedErrorSampler errorSampler)
        (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0) := by
  let sourceChallenges : ProbComp
      (Matrix (Fin sourceRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin sourceRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let errors := ProbComp.sampleIID queryCount errorSampler
  let finish := fun
      (sourceChallenge : Matrix (Fin sourceRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1)))
      (suffixChallenge : Matrix (Fin suffixRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1)))
      (error : Fin queryCount → RLWE.Rq q (degree + 1)) ↦
    (pure (extractTape
      (augmentTape suffixSecret suffixChallenge
        (sourceChallenge,
          vecMul (embedRingSecret q sourceSecret) sourceChallenge + error))) :
      ProbComp (TLWE.BatchCiphertext (ZMod q)
        ((sourceRank + suffixRank) * (degree + 1)) queryCount))
  calc
    _ = evalDist (sourceChallenges >>= fun sourceChallenge ↦
        errors >>= fun error ↦
        suffixChallenges >>= fun suffixChallenge ↦
        finish sourceChallenge suffixChallenge error) := by
      simp [TLWE.batchEncrypt, sourceChallenges, suffixChallenges, errors, finish,
        bind_assoc, monad_norm]
    _ = evalDist (sourceChallenges >>= fun sourceChallenge ↦
        suffixChallenges >>= fun suffixChallenge ↦
        errors >>= fun error ↦ finish sourceChallenge suffixChallenge error) := by
      refine evalDist_bind_congr' sourceChallenges fun sourceChallenge ↦ ?_
      exact evalDist_bind_bind_swap errors suffixChallenges
        (fun error suffixChallenge ↦ finish sourceChallenge suffixChallenge error)
    _ = _ := by
      simpa [sourceChallenges, suffixChallenges, errors, finish] using
        (extractedTargetTape_evalDist_eq_batchEncrypt
          (q := q) (degree := degree) (sourceRank := sourceRank)
          (suffixRank := suffixRank) (samples := queryCount)
          errorSampler sourceSecret suffixSecret)

/-- Fixed-source real transcript for the complete cloud and source-tape blocks. -/
def fixedJointRealTranscript
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1)) :
    ProbComp
      (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount) := do
  let challenge ←
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler).sampleChallenge
  let error ←
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler).sampleError
  return (challenge,
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler).noiseless sourceSecret challenge + error)

/-- Regrouping the fixed-source joint real transcript exposes independent cloud and source-tape
samplers, still correlated through the same fixed source secret. -/
theorem jointTranscriptRegroup_fixedReal_evalDist
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1)) :
    evalDist (jointTranscriptRegroupEquiv q degree sourceRank suffixRank tgswLevels
        queryCount <$>
      fixedJointRealTranscript q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler sourceSecret) =
      evalDist (do
        let cloudTranscript ← fixedCloudRealTranscript q degree sourceRank suffixRank
          tgswLevels errorSampler sourceSecret
        let sourceTape ← TLWE.batchEncrypt sourceRank queryCount errorSampler
          (embedRingSecret q sourceSecret) 0
        return (cloudTranscript, sourceTape)) := by
  let CloudChallenge := CloudReduction.Challenge q (degree + 1) sourceRank suffixRank
    tgswLevels
  let CloudError := CloudReduction.Output q (degree + 1) sourceRank suffixRank
    tgswLevels
  let TapeChallenge := Matrix (Fin sourceRank) (Fin queryCount)
    (RLWE.Rq q (degree + 1))
  let TapeError := Fin queryCount → RLWE.Rq q (degree + 1)
  let cloudChallenges : ProbComp CloudChallenge := $ᵗ CloudChallenge
  let tapeChallenges : ProbComp TapeChallenge := $ᵗ TapeChallenge
  let cloudErrors : ProbComp CloudError := do
    let bootstrapError ← Fin.mOfFn
      (targetScalarDimension sourceRank suffixRank (degree + 1)) fun _ ↦
        ProbComp.sampleIID (TGSW.rowCount sourceRank tgswLevels) errorSampler
    let extensionError ← ProbComp.sampleIID (suffixRank * tgswLevels) errorSampler
    return (bootstrapError, extensionError)
  let tapeErrors : ProbComp TapeError := ProbComp.sampleIID queryCount errorSampler
  let finish := fun (cloudChallenge : CloudChallenge) (cloudError : CloudError)
      (tapeChallenge : TapeChallenge) (tapeError : TapeError) ↦
    let cloudOutput :=
      (CloudReduction.problem q (degree + 1) sourceRank suffixRank tgswLevels
        errorSampler).noiseless sourceSecret cloudChallenge + cloudError
    let tapeOutput :=
      vecMul (embedRingSecret q sourceSecret) tapeChallenge + tapeError
    (pure ((cloudChallenge, cloudOutput), (tapeChallenge, tapeOutput)) :
      ProbComp
        (CloudReduction.Transcript q (degree + 1) sourceRank suffixRank tgswLevels ×
          TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) sourceRank queryCount))
  have uniformChallengeProduct :
      ($ᵗ (JointChallenge q degree sourceRank suffixRank tgswLevels queryCount) :
        ProbComp (JointChallenge q degree sourceRank suffixRank tgswLevels queryCount)) =
      Prod.mk <$> cloudChallenges <*> tapeChallenges := rfl
  have leftExpanded : evalDist
      (jointTranscriptRegroupEquiv q degree sourceRank suffixRank tgswLevels
          queryCount <$>
        fixedJointRealTranscript q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler sourceSecret) =
      evalDist (cloudChallenges >>= fun cloudChallenge ↦
        tapeChallenges >>= fun tapeChallenge ↦
        cloudErrors >>= fun cloudError ↦
        tapeErrors >>= fun tapeError ↦
        finish cloudChallenge cloudError tapeChallenge tapeError) := by
    unfold fixedJointRealTranscript
    simp only [problem]
    rw [uniformChallengeProduct]
    simp [CloudReduction.problem, jointTranscriptRegroupEquiv,
      cloudChallenges, tapeChallenges, cloudErrors, tapeErrors, finish,
      CloudChallenge, CloudError, TapeChallenge, TapeError, bind_assoc, monad_norm]
  have rightExpanded : evalDist (do
        let cloudTranscript ← fixedCloudRealTranscript q degree sourceRank suffixRank
          tgswLevels errorSampler sourceSecret
        let sourceTape ← TLWE.batchEncrypt sourceRank queryCount errorSampler
          (embedRingSecret q sourceSecret) 0
        return (cloudTranscript, sourceTape)) =
      evalDist (cloudChallenges >>= fun cloudChallenge ↦
        cloudErrors >>= fun cloudError ↦
        tapeChallenges >>= fun tapeChallenge ↦
        tapeErrors >>= fun tapeError ↦
        finish cloudChallenge cloudError tapeChallenge tapeError) := by
    simp [fixedCloudRealTranscript, CloudReduction.problem, TLWE.batchEncrypt,
      cloudChallenges, tapeChallenges, cloudErrors, tapeErrors, finish,
      CloudChallenge, CloudError, TapeChallenge, TapeError, bind_assoc, monad_norm]
  rw [leftExpanded, rightExpanded]
  refine evalDist_bind_congr' cloudChallenges fun cloudChallenge ↦ ?_
  exact evalDist_bind_bind_swap tapeChallenges cloudErrors
    (fun tapeChallenge cloudError ↦
      tapeErrors >>= fun tapeError ↦
      finish cloudChallenge cloudError tapeChallenge tapeError)

/-- The fixed-source joint conversion is exactly the native suffix-only (or zero-message) cloud
view together with a fresh target-key scalar tape. -/
theorem convertView_fixedReal_evalDist
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (messages : BinarySecret
      (targetScalarDimension sourceRank suffixRank (degree + 1)))
    (sourceSecret : RingBinarySecret sourceRank (degree + 1))
    (suffixSecret : RingBinarySecret suffixRank (degree + 1)) :
    evalDist (do
      let transcript ← fixedJointRealTranscript q degree sourceRank suffixRank
        tgswLevels queryCount errorSampler sourceSecret
      let suffixChallenge ← $ᵗ Matrix (Fin suffixRank) (Fin queryCount)
        (RLWE.Rq q (degree + 1))
      return convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
        messages suffixSecret suffixChallenge transcript) =
      evalDist (do
        let bootstrappingKey ← Native.generateBootstrappingKey q (degree + 1)
          sourceRank tgswLevels
          (targetScalarDimension sourceRank suffixRank (degree + 1))
          errorSampler gadget messages sourceSecret
        let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank
          suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret
        let tape ← TLWE.batchEncrypt
          (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
          (extractedErrorSampler errorSampler)
          (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
        return ((bootstrappingKey, extensionKey), tape)) := by
  let CloudTranscript := CloudReduction.Transcript q (degree + 1) sourceRank
    suffixRank tgswLevels
  let SourceTape := TLWE.BatchCiphertext (RLWE.Rq q (degree + 1)) sourceRank queryCount
  let CloudView :=
    SourceBootstrappingKey q (degree + 1) sourceRank suffixRank tgswLevels ×
      RingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
  let ScalarTape := TLWE.BatchCiphertext (ZMod q)
    ((sourceRank + suffixRank) * (degree + 1)) queryCount
  let jointTranscripts := fixedJointRealTranscript q degree sourceRank suffixRank
    tgswLevels queryCount errorSampler sourceSecret
  let splitTranscripts : ProbComp (CloudTranscript × SourceTape) := do
    let cloudTranscript ← fixedCloudRealTranscript q degree sourceRank suffixRank
      tgswLevels errorSampler sourceSecret
    let sourceTape ← TLWE.batchEncrypt sourceRank queryCount errorSampler
      (embedRingSecret q sourceSecret) 0
    return (cloudTranscript, sourceTape)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let cloudMap := CloudReduction.cloudViewEquiv q (degree + 1) sourceRank suffixRank
    tgswLevels gadget messages
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q (degree + 1) suffixRank tgswLevels gadget suffixSecret)
  let cloudViews : ProbComp CloudView := do
    let bootstrappingKey ← Native.generateBootstrappingKey q (degree + 1)
      sourceRank tgswLevels
      (targetScalarDimension sourceRank suffixRank (degree + 1))
      errorSampler gadget messages sourceSecret
    let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank
      suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret
    return (bootstrappingKey, extensionKey)
  let tapeSampler : ProbComp ScalarTape := do
    let sourceTape ← TLWE.batchEncrypt sourceRank queryCount errorSampler
      (embedRingSecret q sourceSecret) 0
    let suffixChallenge ← suffixChallenges
    return extractTape (augmentTape suffixSecret suffixChallenge sourceTape)
  let targetTapes : ProbComp ScalarTape := TLWE.batchEncrypt
    ((sourceRank + suffixRank) * (degree + 1)) queryCount
    (extractedErrorSampler errorSampler)
    (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  let finish := fun (cloud : CloudView) (tape : ScalarTape) ↦
    (pure (cloud, tape) : ProbComp (CloudView × ScalarTape))
  have hSplit : evalDist
      (jointTranscriptRegroupEquiv q degree sourceRank suffixRank tgswLevels
        queryCount <$> jointTranscripts) = evalDist splitTranscripts := by
    exact jointTranscriptRegroup_fixedReal_evalDist q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler sourceSecret
  have hCloud : evalDist (cloudMap <$> fixedCloudRealTranscript q degree sourceRank
      suffixRank tgswLevels errorSampler sourceSecret) = evalDist cloudViews := by
    simpa [cloudMap, cloudViews, CloudView] using
      (cloudViewEquiv_fixedReal_evalDist q degree sourceRank suffixRank tgswLevels
        errorSampler gadget messages sourceSecret suffixSecret)
  have hTape : evalDist tapeSampler = evalDist targetTapes := by
    simpa [tapeSampler, targetTapes, suffixChallenges, ScalarTape] using
      (augmentExtract_realTape_evalDist q degree sourceRank suffixRank queryCount
        errorSampler sourceSecret suffixSecret)
  calc
    _ = evalDist ((jointTranscriptRegroupEquiv q degree sourceRank suffixRank
          tgswLevels queryCount <$> jointTranscripts) >>= fun split ↦
        suffixChallenges >>= fun suffixChallenge ↦
        finish (cloudMap split.1)
          (extractTape (augmentTape suffixSecret suffixChallenge split.2))) := by
      simp [jointTranscripts, suffixChallenges, finish, convertView, cloudMap,
        map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (splitTranscripts >>= fun split ↦
        suffixChallenges >>= fun suffixChallenge ↦
        finish (cloudMap split.1)
          (extractTape (augmentTape suffixSecret suffixChallenge split.2))) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSplit _
    _ = evalDist (fixedCloudRealTranscript q degree sourceRank suffixRank tgswLevels
          errorSampler sourceSecret >>= fun cloudTranscript ↦
        tapeSampler >>= fun tape ↦ finish (cloudMap cloudTranscript) tape) := by
      simp [splitTranscripts, tapeSampler, suffixChallenges, finish,
        bind_assoc, monad_norm]
    _ = evalDist ((cloudMap <$> fixedCloudRealTranscript q degree sourceRank suffixRank
          tgswLevels errorSampler sourceSecret) >>= fun cloud ↦
        tapeSampler >>= fun tape ↦ finish cloud tape) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (cloudViews >>= fun cloud ↦
        tapeSampler >>= fun tape ↦ finish cloud tape) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hCloud _
    _ = evalDist (cloudViews >>= fun cloud ↦
        targetTapes >>= fun tape ↦ finish cloud tape) := by
      refine evalDist_bind_congr' cloudViews fun cloud ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hTape
        (finish cloud)
    _ = _ := by
      simp [cloudViews, targetTapes, finish, bind_assoc, monad_norm]

/-! ## Real branch and native-game alignment -/

/-- The real joint LWE distribution is the mixture of the fixed-source samplers above. -/
theorem distr_evalDist_eq_sampleSecret_bind_fixedJoint
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    evalDist (LearningWithErrors.distr
      (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)) =
      evalDist (Native.sampleRingSecret sourceRank (degree + 1) >>= fun sourceSecret ↦
        fixedJointRealTranscript q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler sourceSecret) := by
  let challenges :=
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler).sampleChallenge
  let secrets := Native.sampleRingSecret sourceRank (degree + 1)
  let errors :=
    (problem q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler).sampleError
  let finish := fun
      (challenge : JointChallenge q degree sourceRank suffixRank tgswLevels queryCount)
      (sourceSecret : RingBinarySecret sourceRank (degree + 1))
      (error : JointOutput q degree sourceRank suffixRank tgswLevels queryCount) ↦
    (pure (challenge,
      (problem q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler).noiseless sourceSecret challenge + error) :
      ProbComp
        (JointTranscript q degree sourceRank suffixRank tgswLevels queryCount))
  calc
    _ = evalDist (challenges >>= fun challenge ↦
        secrets >>= fun sourceSecret ↦
        errors >>= fun error ↦ finish challenge sourceSecret error) := by
      simp [LearningWithErrors.distr, problem, challenges, secrets, errors, finish]
    _ = evalDist (secrets >>= fun sourceSecret ↦
        challenges >>= fun challenge ↦
        errors >>= fun error ↦ finish challenge sourceSecret error) :=
      evalDist_bind_bind_swap challenges secrets
        (fun challenge sourceSecret ↦
          errors >>= fun error ↦ finish challenge sourceSecret error)
    _ = _ := by
      simp [fixedJointRealTranscript, challenges, secrets, errors, finish]

/-- Native suffix-only adaptive game with equal cloud errors and sample-extracted input errors. -/
def suffixOnlyGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank (degree + 1)
  let suffixSecret ← Native.sampleRingSecret suffixRank (degree + 1)
  let bootstrappingKey ← generateSuffixOnlySourceBootstrappingKey q (degree + 1)
    sourceRank suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret
  let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank suffixRank
    tgswLevels errorSampler gadget sourceSecret suffixSecret
  let tape ← TLWE.batchEncrypt
    (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
    (extractedErrorSampler errorSampler)
    (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  adaptiveViewContinuation decompose encode adversary
    ((bootstrappingKey, extensionKey), tape)

/-- Native all-zero-BRK adaptive comparison with the same real extension table and input tape. -/
def zeroGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) : ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank (degree + 1)
  let suffixSecret ← Native.sampleRingSecret suffixRank (degree + 1)
  let bootstrappingKey ← generateZeroSourceBootstrappingKey q (degree + 1)
    sourceRank suffixRank tgswLevels errorSampler gadget sourceSecret
  let extensionKey ← generateRingExtensionKey q (degree + 1) sourceRank suffixRank
    tgswLevels errorSampler gadget sourceSecret suffixSecret
  let tape ← TLWE.batchEncrypt
    (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
    (extractedErrorSampler errorSampler)
    (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0
  adaptiveViewContinuation decompose encode adversary
    ((bootstrappingKey, extensionKey), tape)

/-- The explicit suffix-only game is the exact existing secret-dependent continuation game. -/
theorem suffixOnlyGame_eq_sourceContinuationGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    suffixOnlyGame q degree sourceRank suffixRank tgswLevels queryCount errorSampler
        gadget decompose encode adversary =
      suffixOnlySourceContinuationGame q (degree + 1) sourceRank suffixRank
        tgswLevels errorSampler errorSampler gadget
        (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
          decompose
          (adaptiveContinuation queryCount (extractedErrorSampler errorSampler)
            encode adversary)) := by
  rfl

/-- The explicit zero game is the exact existing secret-dependent continuation game. -/
theorem zeroGame_eq_sourceContinuationGame
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    zeroGame q degree sourceRank suffixRank tgswLevels queryCount errorSampler
        gadget decompose encode adversary =
      bootstrapZeroSourceContinuationGame q (degree + 1) sourceRank suffixRank
        tgswLevels errorSampler errorSampler gadget
        (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
          decompose
          (adaptiveContinuation queryCount (extractedErrorSampler errorSampler)
            encode adversary)) := by
  rfl

/-- Native real-message BRK generation at the constant-false message vector has exactly the
native zero-BRK distribution.  The two generators differ only in how their independent rows are
grouped before assembly. -/
theorem generateBootstrappingKey_false_evalDist_eq_zero
    (q degree ringRank tgswLevels messageCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (Native.generateBootstrappingKey q (degree + 1) ringRank tgswLevels
        messageCount errorSampler gadget (fun _ ↦ false) ringSecret) =
      evalDist (Native.generateZeroBootstrappingKey q (degree + 1) ringRank tgswLevels
        messageCount errorSampler gadget ringSecret) := by
  calc
    _ = evalDist (Native.BootstrapCutSecurity.sampleParallelRealBootstrap q (degree + 1)
        ringRank tgswLevels messageCount errorSampler gadget (fun _ ↦ false)
        ringSecret) :=
      Native.BootstrapCutSecurity.generateBootstrappingKey_evalDist_eq_parallel q
        (degree + 1) ringRank tgswLevels messageCount errorSampler gadget
        (fun _ ↦ false) ringSecret
    _ = evalDist (Native.BootstrapCutSecurity.sampleParallelZeroBootstrap q (degree + 1)
        ringRank tgswLevels messageCount errorSampler ringSecret) := by
      simp [Native.BootstrapCutSecurity.sampleParallelRealBootstrap,
        Native.BootstrapCutSecurity.sampleParallelZeroBootstrap]
    _ = _ :=
      (Native.BootstrapCutSecurity.generateZeroBootstrappingKey_evalDist_eq_parallel q
        (degree + 1) ringRank tgswLevels messageCount errorSampler gadget
        ringSecret).symm

/-- The native suffix-only adaptive game is exactly the real branch of the joint module-LWE
reduction, including the target-key input tape. -/
theorem suffixOnlyGame_evalDist_eq_game0
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist (suffixOnlyGame q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary) =
      evalDist (LearningWithErrors.game0
        (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
        (suffixReduction gadget decompose encode adversary)) := by
  let sourceSecrets := Native.sampleRingSecret sourceRank (degree + 1)
  let suffixes := Native.sampleRingSecret suffixRank (degree + 1)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let fixedTranscripts := fun
      (sourceSecret : RingBinarySecret sourceRank (degree + 1)) ↦
    fixedJointRealTranscript q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler sourceSecret
  let finish :
      AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount → ProbComp Bool :=
    adaptiveViewContinuation decompose encode adversary
  have nativeExpanded :
      evalDist (suffixOnlyGame q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget decompose encode adversary) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
            gadget (suffixOnlyMessages suffixSecret) suffixSecret suffixChallenge
            transcript)) := by
    unfold suffixOnlyGame
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    simpa [sourceSecrets, suffixes, suffixChallenges, fixedTranscripts, finish,
      generateSuffixOnlySourceBootstrappingKey, bind_assoc, monad_norm] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (convertView_fixedReal_evalDist q degree sourceRank suffixRank tgswLevels
          queryCount errorSampler gadget (suffixOnlyMessages suffixSecret)
          sourceSecret suffixSecret)
        finish).symm
  have lweExpanded :
      evalDist (LearningWithErrors.game0
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
          (suffixReduction gadget decompose encode adversary)) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixes >>= fun suffixSecret ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
            gadget (suffixOnlyMessages suffixSecret) suffixSecret suffixChallenge
            transcript)) := by
    rw [LearningWithErrors.game0]
    simpa [sourceSecrets, suffixes, suffixChallenges, fixedTranscripts, finish,
      suffixReduction, bind_assoc, monad_norm] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (distr_evalDist_eq_sampleSecret_bind_fixedJoint q degree sourceRank suffixRank
          tgswLevels queryCount errorSampler)
        (suffixReduction (errorSampler := errorSampler) gadget decompose encode adversary))
  rw [nativeExpanded, lweExpanded]
  refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
  exact evalDist_bind_bind_swap suffixes (fixedTranscripts sourceSecret)
    (fun suffixSecret transcript ↦
      suffixChallenges >>= fun suffixChallenge ↦
      finish (convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
        (suffixOnlyMessages suffixSecret) suffixSecret suffixChallenge transcript))

/-- The native all-zero-BRK adaptive game is exactly the real branch of its joint module-LWE
reduction, with the same real extension table and target-key input tape. -/
theorem zeroGame_evalDist_eq_game0
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    evalDist (zeroGame q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary) =
      evalDist (LearningWithErrors.game0
        (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
        (zeroReduction gadget decompose encode adversary)) := by
  let sourceSecrets := Native.sampleRingSecret sourceRank (degree + 1)
  let suffixes := Native.sampleRingSecret suffixRank (degree + 1)
  let suffixChallenges : ProbComp
      (Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))) :=
    $ᵗ Matrix (Fin suffixRank) (Fin queryCount) (RLWE.Rq q (degree + 1))
  let fixedTranscripts := fun
      (sourceSecret : RingBinarySecret sourceRank (degree + 1)) ↦
    fixedJointRealTranscript q degree sourceRank suffixRank tgswLevels queryCount
      errorSampler sourceSecret
  let finish :
      AdaptiveView q degree sourceRank suffixRank tgswLevels queryCount → ProbComp Bool :=
    adaptiveViewContinuation decompose encode adversary
  have nativeExpanded :
      evalDist (zeroGame q degree sourceRank suffixRank tgswLevels queryCount
          errorSampler gadget decompose encode adversary) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
            gadget (fun _ ↦ false) suffixSecret suffixChallenge transcript)) := by
    unfold zeroGame
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    calc
      evalDist (generateZeroSourceBootstrappingKey q (degree + 1) sourceRank
          suffixRank tgswLevels errorSampler gadget sourceSecret >>= fun bootstrappingKey ↦
        generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
            errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
          TLWE.batchEncrypt
              (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
              (extractedErrorSampler errorSampler)
              (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0 >>=
            fun tape ↦ finish ((bootstrappingKey, extensionKey), tape)) =
        evalDist (Native.generateBootstrappingKey q (degree + 1) sourceRank
            tgswLevels (targetScalarDimension sourceRank suffixRank (degree + 1))
            errorSampler gadget (fun _ ↦ false) sourceSecret >>=
          fun bootstrappingKey ↦
            generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
                errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
              TLWE.batchEncrypt
                  (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
                  (extractedErrorSampler errorSampler)
                  (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0 >>=
                fun tape ↦ finish ((bootstrappingKey, extensionKey), tape)) := by
          simpa [generateZeroSourceBootstrappingKey] using
            (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
              (generateBootstrappingKey_false_evalDist_eq_zero q degree sourceRank
                tgswLevels (targetScalarDimension sourceRank suffixRank (degree + 1))
                errorSampler gadget sourceSecret).symm
              (fun bootstrappingKey ↦
                generateRingExtensionKey q (degree + 1) sourceRank suffixRank tgswLevels
                    errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
                  TLWE.batchEncrypt
                      (targetScalarDimension sourceRank suffixRank (degree + 1)) queryCount
                      (extractedErrorSampler errorSampler)
                      (embedBinarySecret (targetMessages sourceSecret suffixSecret)) 0 >>=
                    fun tape ↦ finish ((bootstrappingKey, extensionKey), tape)))
      _ = evalDist (fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
            gadget (fun _ ↦ false) suffixSecret suffixChallenge transcript)) := by
        simpa [sourceSecrets, suffixes, suffixChallenges, fixedTranscripts, finish,
          bind_assoc, monad_norm] using
          (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            (convertView_fixedReal_evalDist q degree sourceRank suffixRank tgswLevels
              queryCount errorSampler gadget (fun _ ↦ false) sourceSecret suffixSecret)
            finish).symm
  have lweExpanded :
      evalDist (LearningWithErrors.game0
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
          (zeroReduction gadget decompose encode adversary)) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          fixedTranscripts sourceSecret >>= fun transcript ↦
          suffixes >>= fun suffixSecret ↦
          suffixChallenges >>= fun suffixChallenge ↦
          finish (convertView q degree sourceRank suffixRank tgswLevels queryCount
            gadget (fun _ ↦ false) suffixSecret suffixChallenge transcript)) := by
    rw [LearningWithErrors.game0]
    simpa [sourceSecrets, suffixes, suffixChallenges, fixedTranscripts, finish,
      zeroReduction, bind_assoc, monad_norm] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (distr_evalDist_eq_sampleSecret_bind_fixedJoint q degree sourceRank suffixRank
          tgswLevels queryCount errorSampler)
        (zeroReduction (errorSampler := errorSampler) gadget decompose encode adversary))
  rw [nativeExpanded, lweExpanded]
  refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
  exact evalDist_bind_bind_swap suffixes (fixedTranscripts sourceSecret)
    (fun suffixSecret transcript ↦
      suffixChallenges >>= fun suffixChallenge ↦
      finish (convertView q degree sourceRank suffixRank tgswLevels queryCount gadget
        (fun _ ↦ false) suffixSecret suffixChallenge transcript))

/-! ## Adaptive acyclic-suffix bound -/

/-- **Adaptive acyclic-suffix reduction.**  For positive ring degree, replacing the independent
suffix coordinates of the fixed target message vector by zero costs at most two advantages for
one ordinary blocked binary-secret module-LWE problem.  That problem jointly supplies the BRK
rows, the ring-extension rows, and every query-counted input-tape row under the same source key. -/
theorem independentSuffixAdaptiveAdvantage_le_two_moduleLwe
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    independentSuffixAdaptiveAdvantage q (degree + 1) sourceRank suffixRank tgswLevels
        queryCount errorSampler errorSampler (extractedErrorSampler errorSampler) gadget
        decompose encode adversary ≤
      LearningWithErrors.advantage
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
          (suffixReduction gadget decompose encode adversary) +
        LearningWithErrors.advantage
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
          (zeroReduction gadget decompose encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold independentSuffixAdaptiveAdvantage independentSuffixAdvantage
    ProbComp.boolDistAdvantage
  rw [← suffixOnlyGame_eq_sourceContinuationGame q degree sourceRank suffixRank
      tgswLevels queryCount errorSampler gadget decompose encode adversary,
    ← zeroGame_eq_sourceContinuationGame q degree sourceRank suffixRank tgswLevels
      queryCount errorSampler gadget decompose encode adversary]
  rw [evalDist_ext_iff.mp
      (suffixOnlyGame_evalDist_eq_game0 q degree sourceRank suffixRank tgswLevels
        queryCount errorSampler gadget decompose encode adversary) true,
    evalDist_ext_iff.mp
      (zeroGame_evalDist_eq_game0 q degree sourceRank suffixRank tgswLevels queryCount
        errorSampler gadget decompose encode adversary) true]
  let suffixProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
    (suffixReduction gadget decompose encode adversary)]).toReal
  let uniformSuffixProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
    (suffixReduction gadget decompose encode adversary)]).toReal
  let uniformZeroProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
    (zeroReduction gadget decompose encode adversary)]).toReal
  let zeroProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
    (zeroReduction gadget decompose encode adversary)]).toReal
  have hUniform : uniformSuffixProbability = uniformZeroProbability := by
    apply congrArg ENNReal.toReal
    exact evalDist_ext_iff.mp
      ((suffixReduction_game1_evalDist_eq_uniform q degree sourceRank suffixRank
          tgswLevels queryCount errorSampler gadget decompose encode adversary).trans
        (zeroReduction_game1_evalDist_eq_uniform q degree sourceRank suffixRank
          tgswLevels queryCount errorSampler gadget decompose encode adversary).symm) true
  change |suffixProbability - zeroProbability| ≤
    |suffixProbability - uniformSuffixProbability| +
      |zeroProbability - uniformZeroProbability|
  rw [hUniform, abs_sub_comm zeroProbability uniformZeroProbability]
  exact abs_sub_le suffixProbability uniformZeroProbability zeroProbability

/-- **End-to-end fixed-message TFHE security boundary.**  With the shared-randomness KSK and
positive ring degree, the honest adaptive TFHE advantage is bounded by exactly one native
source-prefix CircRLWE/KDM term, two ordinary joint module-LWE terms for all acyclic material,
and the standard zero-BRK encryption endpoint. -/
theorem abs_signedAdvantage_realAdaptive_le_nativePrefixCircRLWE_add_two_moduleLwe_add_zero
    {Message : Type}
    (q degree sourceRank suffixRank tgswLevels queryCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) sourceRank →
      Fin (sourceRank + 1) → Fin tgswLevels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) sourceRank suffixRank
      tgswLevels) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        errorSampler errorSampler (extractedErrorSampler errorSampler) gadget decompose
        encode adversary)| ≤
      PrefixCircLWE.kdmAdvantage errorSampler errorSampler gadget
          (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
            decompose
            (adaptiveContinuation queryCount (extractedErrorSampler errorSampler)
              encode adversary)) +
        LearningWithErrors.advantage
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
          (suffixReduction gadget decompose encode adversary) +
        LearningWithErrors.advantage
          (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
          (zeroReduction gadget decompose encode adversary) +
        |Encryption.signedAdvantage
          (bootstrapZeroAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels
            queryCount errorSampler errorSampler (extractedErrorSampler errorSampler)
            gadget decompose encode adversary)| := by
  let prefixTerm := sourcePrefixCircularAdaptiveAdvantage q (degree + 1) sourceRank
    suffixRank tgswLevels queryCount errorSampler errorSampler
    (extractedErrorSampler errorSampler) gadget decompose encode adversary
  let suffixTerm := independentSuffixAdaptiveAdvantage q (degree + 1) sourceRank
    suffixRank tgswLevels queryCount errorSampler errorSampler
    (extractedErrorSampler errorSampler) gadget decompose encode adversary
  let suffixLwe := LearningWithErrors.advantage
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
    (suffixReduction gadget decompose encode adversary)
  let zeroLwe := LearningWithErrors.advantage
    (problem q degree sourceRank suffixRank tgswLevels queryCount errorSampler)
    (zeroReduction gadget decompose encode adversary)
  let endpoint := |Encryption.signedAdvantage
    (bootstrapZeroAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels
      queryCount errorSampler errorSampler (extractedErrorSampler errorSampler) gadget
      decompose encode adversary)|
  have hMain : |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) sourceRank suffixRank tgswLevels queryCount
        errorSampler errorSampler (extractedErrorSampler errorSampler) gadget decompose
        encode adversary)| ≤ (prefixTerm + suffixTerm) + endpoint := by
    exact abs_signedAdvantage_realAdaptive_le_prefixCircular_add_suffix_add_zero q
      (degree + 1) sourceRank suffixRank tgswLevels queryCount errorSampler errorSampler
      (extractedErrorSampler errorSampler) gadget decompose encode adversary
  have hSuffix : suffixTerm ≤ suffixLwe + zeroLwe := by
    exact independentSuffixAdaptiveAdvantage_le_two_moduleLwe q degree sourceRank
      suffixRank tgswLevels queryCount errorSampler gadget decompose encode adversary
  have hPrefix :
      PrefixCircLWE.kdmAdvantage errorSampler errorSampler gadget
          (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
            decompose
            (adaptiveContinuation queryCount (extractedErrorSampler errorSampler)
              encode adversary)) = prefixTerm := by
    exact PrefixCircLWE.kdmAdvantage_eq_sourcePrefixCircularAdvantage errorSampler
      errorSampler gadget _
  calc
    _ ≤ (prefixTerm + suffixTerm) + endpoint := hMain
    _ ≤ (prefixTerm + (suffixLwe + zeroLwe)) + endpoint := by
      exact add_le_add (add_le_add (le_refl _) hSuffix) (le_refl _)
    _ = PrefixCircLWE.kdmAdvantage errorSampler errorSampler gadget
          (compileSourceContinuation q (degree + 1) sourceRank suffixRank tgswLevels
            decompose
            (adaptiveContinuation queryCount (extractedErrorSampler errorSampler)
              encode adversary)) + suffixLwe + zeroLwe + endpoint := by
      rw [hPrefix]
      ring

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveReduction
