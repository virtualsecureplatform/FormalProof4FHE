/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BootstrappingSecurity
import FormalProof4FHE.RLWE.RingRegev
import FormalProof4FHE.LWE.ParallelBatch

/-!
# Native TFHE Security after Cutting the Evaluation-Key Cycle

The native TFHE cloud key contains a two-way dependency: the bootstrapping key encrypts scalar-key
bits under the ring key, while the key-switch key encrypts ring-key coefficients under the scalar
key.  This file proves that the bootstrapping direction needs no circular assumption once the
opposite key-switch direction has been replaced by zero-message rows.

For a fixed scalar key, adding `mu * H` to homogeneous TGSW rows is a public bijective transcript
translation.  Therefore the real-message and zero-message bootstrapping endpoints can each be
compared with one common uniform endpoint.  The resulting cut-cycle replacement cost is bounded
by two ordinary parallel binary-secret module-LWE advantages.  The only premise left outside this
theorem is the intact two-way cycle, where neither secret is available to the reduction.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapCutSecurity

/-- Public matrices for one ordinary module-LWE batch per scalar-key coordinate. -/
abbrev ParallelChallenge (R : Type) (ringRank tgswLevels lweDimension : ℕ) :=
  Fin lweDimension → Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels)) R

/-- Output vectors for one ordinary module-LWE batch per scalar-key coordinate. -/
abbrev ParallelOutput (R : Type) (ringRank tgswLevels lweDimension : ℕ) :=
  Fin lweDimension → Fin (TGSW.rowCount ringRank tgswLevels) → R

/-- A parallel module-LWE transcript is definitionally the unzipped representation of a native
bootstrapping key. -/
abbrev ParallelTranscript (R : Type) (ringRank tgswLevels lweDimension : ℕ) :=
  ParallelChallenge R ringRank tgswLevels lweDimension ×
    ParallelOutput R ringRank tgswLevels lweDimension

/-- Pointwise addition through the proof-facing `CommRing` instance agrees with pointwise
addition through the executable bundled negacyclic-ring instance. -/
theorem semiringRqPiAdd_eq_native {Index : Type} (q degree : ℕ)
    (left right : Index → RLWE.Rq q degree) :
    @Add.add (Index → RLWE.Rq q degree)
        (@Pi.instAdd Index (fun _ ↦ RLWE.Rq q degree)
          (fun _ ↦ FormalProof4FHE.RLWE.RingRegev.semiringRqAdd q degree))
        left right =
      @Add.add (Index → RLWE.Rq q degree)
        (@Pi.instAdd Index (fun _ ↦ RLWE.Rq q degree)
          (fun _ ↦ LatticeCrypto.NegacyclicRing.instAddPoly
            (RLWE.negacyclicRing q degree)))
        left right := by
  funext index
  exact FormalProof4FHE.RLWE.RingRegev.semiringRqAdd_apply
    q degree (left index) (right index)

/-- Inferred proof-facing pointwise addition has the same executable value as bundled ring
addition.  This wrapper matches expressions produced by generic module-LWE definitions. -/
theorem rqPiAdd_eq_native {Index : Type} (q degree : ℕ)
    (left right : Index → RLWE.Rq q degree) :
    left + right =
      @Add.add (Index → RLWE.Rq q degree)
        (@Pi.instAdd Index (fun _ ↦ RLWE.Rq q degree)
          (fun _ ↦ LatticeCrypto.NegacyclicRing.instAddPoly
            (RLWE.negacyclicRing q degree)))
        left right := by
  rfl

/-- Eta-expanded pointwise addition contracts to the inferred function-space addition. -/
theorem pointwiseAdd_eq_add {Index Value : Type} [Add Value]
    (left right : Index → Value) :
    (fun index ↦ left index + right index) = left + right := by
  rfl

/-- Pointwise addition selected by the proof-facing negacyclic `CommRing`. -/
noncomputable def semiringRqPiAdd {Index : Type} (q degree : ℕ)
    (left right : Index → RLWE.Rq q degree) : Index → RLWE.Rq q degree :=
  @Add.add (Index → RLWE.Rq q degree)
    (@Pi.instAdd Index (fun _ ↦ RLWE.Rq q degree)
      (fun _ ↦ FormalProof4FHE.RLWE.RingRegev.semiringRqAdd q degree))
    left right

@[simp]
theorem semiringRqPiAdd_eq_add {Index : Type} (q degree : ℕ)
    (left right : Index → RLWE.Rq q degree) :
    semiringRqPiAdd q degree left right = left + right := by
  exact (semiringRqPiAdd_eq_native q degree left right).trans
    (rqPiAdd_eq_native q degree left right).symm

/-- Nested pointwise addition selected by the proof-facing negacyclic semiring. -/
@[reducible] noncomputable def semiringParallelOutputAdd
    (q degree ringRank tgswLevels lweDimension : ℕ) :
    Add (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
  @Pi.instAdd (Fin lweDimension)
    (fun _ ↦ Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)
    (fun _ ↦ @Pi.instAdd (Fin (TGSW.rowCount ringRank tgswLevels))
      (fun _ ↦ RLWE.Rq q degree)
      (fun _ ↦ FormalProof4FHE.RLWE.RingRegev.semiringRqAdd q degree))

/-- The proof-facing and executable nested output-addition dictionaries are equal. -/
theorem semiringParallelOutputAdd_eq
    (q degree ringRank tgswLevels lweDimension : ℕ) :
    semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension =
      (inferInstance : Add
        (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)) := by
  have hfun :
      @Add.add (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
          (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension) =
        @Add.add (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
          (inferInstance : Add
            (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)) := by
    funext left right block sample
    exact FormalProof4FHE.RLWE.RingRegev.semiringRqAdd_apply
      q degree (left block sample) (right block sample)
  calc
    semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension =
        ⟨@Add.add
          (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
          (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension)⟩ := by
      cases semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension
      rfl
    _ = ⟨@Add.add
          (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
          (inferInstance : Add
            (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension))⟩ := by
      exact congrArg
        (fun operation :
            ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension →
            ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension →
            ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension ↦
          (⟨operation⟩ : Add
            (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension))) hfun
    _ = (inferInstance : Add
        (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)) := by
      cases (inferInstance : Add
        (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension))
      rfl

/-- Zip the public matrices and output vectors into native TGSW ciphertext entries. -/
def transcriptToBootstrappingKey
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (transcript : ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :
    BootstrappingKey q degree ringRank tgswLevels lweDimension :=
  (Equiv.arrowProdEquivProdArrow (Fin lweDimension)
    (fun _ ↦ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree))
    (fun _ ↦ Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)).symm transcript

/-- Unzip a native bootstrapping key into parallel module-LWE challenge and output families. -/
def bootstrappingKeyToTranscript
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (key : BootstrappingKey q degree ringRank tgswLevels lweDimension) :
    ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension :=
  Equiv.arrowProdEquivProdArrow (Fin lweDimension)
    (fun _ ↦ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree))
    (fun _ ↦ Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree) key

@[simp]
theorem bootstrappingKeyToTranscript_transcriptToBootstrappingKey
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (transcript : ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :
    bootstrappingKeyToTranscript (transcriptToBootstrappingKey transcript) = transcript := by
  exact Equiv.apply_symm_apply _ transcript

@[simp]
theorem transcriptToBootstrappingKey_bootstrappingKeyToTranscript
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (key : BootstrappingKey q degree ringRank tgswLevels lweDimension) :
    transcriptToBootstrappingKey (bootstrappingKeyToTranscript key) = key := by
  exact Equiv.symm_apply_apply _ key

/-- Zipping and unzipping give a bijection between the complete parallel transcript and the
native bootstrapping-key carrier. -/
theorem transcriptToBootstrappingKey_bijective
    {q degree ringRank tgswLevels lweDimension : ℕ} :
    Function.Bijective
      (transcriptToBootstrappingKey :
        ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension →
          BootstrappingKey q degree ringRank tgswLevels lweDimension) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨bootstrappingKeyToTranscript, ?_, ?_⟩
  · exact bootstrappingKeyToTranscript_transcriptToBootstrappingKey
  · exact transcriptToBootstrappingKey_bootstrappingKeyToTranscript

/-- Add every coordinate-dependent native gadget matrix to an unzipped homogeneous transcript. -/
def shiftTranscript {R : Type} [Ring R]
    {ringRank tgswLevels lweDimension : ℕ}
    (gadget : Fin tgswLevels → R) (message : Fin lweDimension → R)
    (transcript : ParallelTranscript R ringRank tgswLevels lweDimension) :
    ParallelTranscript R ringRank tgswLevels lweDimension :=
  (fun coordinate ↦ transcript.1 coordinate +
      TGSW.gadgetMaskShift gadget (message coordinate),
    fun coordinate ↦ transcript.2 coordinate +
      TGSW.gadgetBodyShift gadget (message coordinate))

/-- Zipping a shifted parallel transcript is the coordinatewise native `addGadget` operation. -/
@[simp]
theorem transcriptToBootstrappingKey_shiftTranscript
    {q degree ringRank tgswLevels lweDimension : ℕ}
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : Fin lweDimension → RLWE.Rq q degree)
    (transcript : ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :
    transcriptToBootstrappingKey (shiftTranscript gadget message transcript) =
      fun coordinate ↦ TGSW.addGadget gadget (message coordinate)
        (transcriptToBootstrappingKey transcript coordinate) := by
  rfl

/-- Remove every coordinate-dependent gadget matrix. -/
def unshiftTranscript {R : Type} [Ring R]
    {ringRank tgswLevels lweDimension : ℕ}
    (gadget : Fin tgswLevels → R) (message : Fin lweDimension → R)
    (transcript : ParallelTranscript R ringRank tgswLevels lweDimension) :
    ParallelTranscript R ringRank tgswLevels lweDimension :=
  (fun coordinate ↦ transcript.1 coordinate -
      TGSW.gadgetMaskShift gadget (message coordinate),
    fun coordinate ↦ transcript.2 coordinate -
      TGSW.gadgetBodyShift gadget (message coordinate))

@[simp]
theorem unshiftTranscript_shiftTranscript
    {R : Type} [Ring R] {ringRank tgswLevels lweDimension : ℕ}
    (gadget : Fin tgswLevels → R) (message : Fin lweDimension → R)
    (transcript : ParallelTranscript R ringRank tgswLevels lweDimension) :
    unshiftTranscript gadget message (shiftTranscript gadget message transcript) = transcript := by
  apply Prod.ext
  · funext coordinate
    exact add_sub_cancel_right _ _
  · funext coordinate
    exact add_sub_cancel_right _ _

@[simp]
theorem shiftTranscript_unshiftTranscript
    {R : Type} [Ring R] {ringRank tgswLevels lweDimension : ℕ}
    (gadget : Fin tgswLevels → R) (message : Fin lweDimension → R)
    (transcript : ParallelTranscript R ringRank tgswLevels lweDimension) :
    shiftTranscript gadget message (unshiftTranscript gadget message transcript) = transcript := by
  apply Prod.ext
  · funext coordinate
    exact sub_add_cancel _ _
  · funext coordinate
    exact sub_add_cancel _ _

/-- Adding all native gadget matrices is a permutation of the complete parallel transcript. -/
theorem shiftTranscript_bijective
    {R : Type} [Ring R] {ringRank tgswLevels lweDimension : ℕ}
    (gadget : Fin tgswLevels → R) (message : Fin lweDimension → R) :
    Function.Bijective (shiftTranscript (ringRank := ringRank) gadget message) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftTranscript gadget message,
      unshiftTranscript_shiftTranscript gadget message,
      shiftTranscript_unshiftTranscript gadget message⟩

/-- Ordinary binary-secret module-LWE with independent parallel batches sharing one ring key. -/
noncomputable def parallelModuleLweProblem
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    LearningWithErrors.Problem
      (ParallelChallenge (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
      (RingBinarySecret ringRank degree)
      (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension) where
  sampleChallenge := Fin.mOfFn lweDimension fun _ ↦
    $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree)
  sampleSecret := sampleRingSecret ringRank degree
  sampleError := Fin.mOfFn lweDimension fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) errorSampler
  noiseless := fun ringSecret challenge coordinate ↦
    vecMul (embedRingSecret q ringSecret) (challenge coordinate)
  sampleUniform := Fin.mOfFn lweDimension fun _ ↦
    $ᵗ (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)

/-- The custom-shaped parallel problem is definitionally the generic equal-block LWE problem. -/
theorem parallelModuleLweProblem_eq_parallelBatchProblem
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    parallelModuleLweProblem q degree ringRank tgswLevels lweDimension errorSampler =
      FormalProof4FHE.LWE.ParallelBatch.problem ringRank lweDimension
        (TGSW.rowCount ringRank tgswLevels) (sampleRingSecret ringRank degree)
        (embedRingSecret q) errorSampler := by
  rfl

/-- Conventional binary-secret module-LWE batch containing every bootstrapping row contiguously. -/
noncomputable def batchModuleLweProblem
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :=
  FormalProof4FHE.LWE.embeddedBatchProblem ringRank
    (lweDimension * TGSW.rowCount ringRank tgswLevels)
    (sampleRingSecret ringRank degree) (embedRingSecret q) errorSampler

/-! ## Exact rank-one binary-secret RLWE normalization -/

/-- The TFHE binary-polynomial secret sampler, pushed forward into the rank-one secret carrier
of the finite negacyclic RLWE problem.  This records the secret distribution explicitly: it is
not the uniform-secret RLWE sampler. -/
noncomputable def binarySecretRLWESampler (q degree : ℕ) :
    ProbComp (RLWE.Secret q degree) :=
  embedRingSecret q <$> sampleRingSecret 1 degree

/-- Finite rank-one RLWE with independently uniform binary coefficients in its secret
polynomial.  The sample count and ring-error sampler remain explicit. -/
noncomputable def binarySecretRLWEProblem
    (q degree sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    LearningWithErrors.Problem
      (RLWE.Sample q degree sampleCount) (RLWE.Secret q degree)
      (RLWE.Output q degree sampleCount) :=
  RLWE.problem q degree sampleCount (binarySecretRLWESampler q degree) errorSampler

/-- At module rank one, the conventional post-cut BRK batch has exactly the real transcript
distribution of binary-secret RLWE with
`lweDimension * TGSW.rowCount 1 tgswLevels` samples. -/
theorem batchModuleLweProblem_one_distr_evalDist_eq_binarySecretRLWE
    (q degree tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    evalDist (LearningWithErrors.distr
      (batchModuleLweProblem q degree 1 tgswLevels lweDimension errorSampler)) =
      evalDist (LearningWithErrors.distr
        (binarySecretRLWEProblem q degree
          (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler)) := by
  simp [LearningWithErrors.distr, batchModuleLweProblem,
    binarySecretRLWEProblem, binarySecretRLWESampler, RLWE.problem,
    FormalProof4FHE.LWE.batchProblem, FormalProof4FHE.LWE.embeddedBatchProblem,
    sampleRingSecret, monad_norm]

/-- The uniform branches of the post-cut rank-one batch and binary-secret RLWE coincide exactly. -/
theorem batchModuleLweProblem_one_uniformDistr_evalDist_eq_binarySecretRLWE
    (q degree tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    evalDist (LearningWithErrors.uniformDistr
      (batchModuleLweProblem q degree 1 tgswLevels lweDimension errorSampler)) =
      evalDist (LearningWithErrors.uniformDistr
        (binarySecretRLWEProblem q degree
          (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler)) := by
  rfl

/-- Every public distinguisher has exactly the same advantage against the post-cut rank-one
ring batch and the explicitly named binary-secret RLWE problem.  There is no reduction loss. -/
theorem batchModuleLweProblem_one_advantage_eq_binarySecretRLWE
    (q degree tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (binarySecretRLWEProblem q degree
        (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler)) :
    LearningWithErrors.advantage
        (batchModuleLweProblem q degree 1 tgswLevels lweDimension errorSampler) adversary =
      LearningWithErrors.advantage
        (binarySecretRLWEProblem q degree
          (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler) adversary := by
  have hReal :
      evalDist (LearningWithErrors.game0
        (batchModuleLweProblem q degree 1 tgswLevels lweDimension errorSampler) adversary) =
        evalDist (LearningWithErrors.game0
          (binarySecretRLWEProblem q degree
            (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler) adversary) := by
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (batchModuleLweProblem_one_distr_evalDist_eq_binarySecretRLWE
        q degree tgswLevels lweDimension errorSampler) adversary
  have hUniform :
      evalDist (LearningWithErrors.game1
        (batchModuleLweProblem q degree 1 tgswLevels lweDimension errorSampler) adversary) =
        evalDist (LearningWithErrors.game1
          (binarySecretRLWEProblem q degree
            (lweDimension * TGSW.rowCount 1 tgswLevels) errorSampler) adversary) := by
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      (batchModuleLweProblem_one_uniformDistr_evalDist_eq_binarySecretRLWE
        q degree tgswLevels lweDimension errorSampler) adversary
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp hReal true, evalDist_ext_iff.mp hUniform true]

/-- Parallel homogeneous module-LWE rows for fixed ring secret. -/
noncomputable def sampleParallelHomogeneous
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension) := do
  let challenge ← Fin.mOfFn lweDimension fun _ ↦
    $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree)
  let error ← Fin.mOfFn lweDimension fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) errorSampler
  return (challenge, fun coordinate ↦
    semiringRqPiAdd q degree
      (vecMul (embedRingSecret q ringSecret) (challenge coordinate)) (error coordinate))

/-- The same parallel rows after adding every native scalar-key-dependent gadget matrix. -/
noncomputable def sampleParallelRealBootstrap
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) := do
  let transcript ← sampleParallelHomogeneous q degree ringRank tgswLevels lweDimension
    errorSampler ringSecret
  return fun coordinate ↦
    TGSW.addGadget gadget (embedConstantBit q degree (lweSecret coordinate))
      (transcriptToBootstrappingKey transcript coordinate)

/-- The unshifted parallel rows, viewed as a native zero-message bootstrapping key. -/
noncomputable def sampleParallelZeroBootstrap
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BootstrappingKey q degree ringRank tgswLevels lweDimension) := do
  let transcript ← sampleParallelHomogeneous q degree ringRank tgswLevels lweDimension
    errorSampler ringSecret
  return transcriptToBootstrappingKey transcript

/-- Regrouping all public matrices before all errors does not change the native real
bootstrapping-key distribution. -/
theorem generateBootstrappingKey_evalDist_eq_parallel
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      errorSampler gadget lweSecret ringSecret) =
      evalDist (sampleParallelRealBootstrap q degree ringRank tgswLevels lweDimension
        errorSampler gadget lweSecret ringSecret) := by
  let challengeSampler : Fin lweDimension →
      ProbComp (Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)) := fun _ ↦
    $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree)
  let errorVectorSampler : Fin lweDimension →
      ProbComp (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree) := fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) errorSampler
  let pairSampler := fun coordinate : Fin lweDimension ↦ do
    let challenge ← challengeSampler coordinate
    let error ← errorVectorSampler coordinate
    return (challenge, error)
  let assembleCoordinate := fun (coordinate : Fin lweDimension)
      (randomness :
        Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
            (RLWE.Rq q degree) ×
          (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) ↦
    TGSW.addGadget gadget (embedConstantBit q degree (lweSecret coordinate))
      (randomness.1,
        semiringRqPiAdd q degree
          (vecMul (embedRingSecret q ringSecret) randomness.1) randomness.2)
  let assemble :
      (Fin lweDimension →
        Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
          (RLWE.Rq q degree) ×
          (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) →
        BootstrappingKey q degree ringRank tgswLevels lweDimension :=
    fun randomness coordinate ↦ assembleCoordinate coordinate (randomness coordinate)
  let zipped :=
    (Equiv.arrowProdEquivProdArrow (Fin lweDimension)
      (fun _ ↦ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree))
      (fun _ ↦ Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)).symm <$>
      (do
        let challenge ← Fin.mOfFn lweDimension challengeSampler
        let error ← Fin.mOfFn lweDimension errorVectorSampler
        return (challenge, error))
  have hzip := FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_zip
    lweDimension challengeSampler errorVectorSampler
  have hmapped := congrArg (fun distribution ↦ assemble <$> distribution) hzip
  simp only [evalDist_map] at hmapped
  have hmap := FormalProof4FHE.FiniteProduct.map_fin_mOfFn
    lweDimension pairSampler assembleCoordinate
  calc
    evalDist (generateBootstrappingKey q degree ringRank tgswLevels lweDimension
        errorSampler gadget lweSecret ringSecret) =
        evalDist (Fin.mOfFn lweDimension fun coordinate ↦
          assembleCoordinate coordinate <$> pairSampler coordinate) := by
      simp [generateBootstrappingKey, pairSampler, assembleCoordinate,
        challengeSampler, errorVectorSampler, TGSW.encrypt, TLWE.batchEncrypt,
        TLWE.batchAssemble, TGSW.addGadget, semiringRqPiAdd, monad_norm]
      rfl
    _ = evalDist (assemble <$> Fin.mOfFn lweDimension pairSampler) := by
      exact congrArg evalDist hmap.symm
    _ = evalDist (assemble <$> zipped) := by
      simpa [zipped, pairSampler] using hmapped.symm
    _ = evalDist (sampleParallelRealBootstrap q degree ringRank tgswLevels lweDimension
        errorSampler gadget lweSecret ringSecret) := by
      simp [zipped, assemble, assembleCoordinate, sampleParallelRealBootstrap,
        sampleParallelHomogeneous, challengeSampler, errorVectorSampler,
        semiringRqPiAdd, monad_norm]
      rfl

/-- The analogous regrouping equality for the zero-message bootstrapping sampler. -/
theorem generateZeroBootstrappingKey_evalDist_eq_parallel
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
      errorSampler gadget ringSecret) =
      evalDist (sampleParallelZeroBootstrap q degree ringRank tgswLevels lweDimension
        errorSampler ringSecret) := by
  let challengeSampler : Fin lweDimension →
      ProbComp (Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)) := fun _ ↦
    $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
      (RLWE.Rq q degree)
  let errorVectorSampler : Fin lweDimension →
      ProbComp (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree) := fun _ ↦
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) errorSampler
  let pairSampler := fun coordinate : Fin lweDimension ↦ do
    let challenge ← challengeSampler coordinate
    let error ← errorVectorSampler coordinate
    return (challenge, error)
  let assembleCoordinate := fun (_ : Fin lweDimension)
      (randomness :
        Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
            (RLWE.Rq q degree) ×
          (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) ↦
    (randomness.1, semiringRqPiAdd q degree
      (vecMul (embedRingSecret q ringSecret) randomness.1) randomness.2)
  let assemble :
      (Fin lweDimension →
        Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
          (RLWE.Rq q degree) ×
          (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)) →
        BootstrappingKey q degree ringRank tgswLevels lweDimension :=
    fun randomness coordinate ↦ assembleCoordinate coordinate (randomness coordinate)
  let zipped :=
    (Equiv.arrowProdEquivProdArrow (Fin lweDimension)
      (fun _ ↦ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree))
      (fun _ ↦ Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)).symm <$>
      (do
        let challenge ← Fin.mOfFn lweDimension challengeSampler
        let error ← Fin.mOfFn lweDimension errorVectorSampler
        return (challenge, error))
  have hzip := FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_zip
    lweDimension challengeSampler errorVectorSampler
  have hmapped := congrArg (fun distribution ↦ assemble <$> distribution) hzip
  simp only [evalDist_map] at hmapped
  have hmap := FormalProof4FHE.FiniteProduct.map_fin_mOfFn
    lweDimension pairSampler assembleCoordinate
  calc
    evalDist (generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
        errorSampler gadget ringSecret) =
        evalDist (Fin.mOfFn lweDimension fun coordinate ↦
          assembleCoordinate coordinate <$> pairSampler coordinate) := by
      simp [generateZeroBootstrappingKey, pairSampler, assembleCoordinate,
        challengeSampler, errorVectorSampler, TGSW.encryptZero, TGSW.encrypt,
        TLWE.batchEncrypt, TLWE.batchAssemble, semiringRqPiAdd, monad_norm]
      rfl
    _ = evalDist (assemble <$> Fin.mOfFn lweDimension pairSampler) := by
      exact congrArg evalDist hmap.symm
    _ = evalDist (assemble <$> zipped) := by
      simpa [zipped, pairSampler] using hmapped.symm
    _ = evalDist (sampleParallelZeroBootstrap q degree ringRank tgswLevels lweDimension
        errorSampler ringSecret) := by
      simp [zipped, assemble, assembleCoordinate, sampleParallelZeroBootstrap,
        sampleParallelHomogeneous, challengeSampler, errorVectorSampler,
        semiringRqPiAdd, monad_norm]
      rfl

/-- If every ring-error coordinate is uniform, the complete homogeneous parallel transcript is
uniform, even for a fixed ring secret.  The public challenge is uniform and adding its fixed
secret product to a uniform error vector is a permutation. -/
theorem sampleParallelHomogeneous_uniformError_evalDist
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (sampleParallelHomogeneous q degree ringRank tgswLevels lweDimension
      ($ᵗ (RLWE.Rq q degree)) ringSecret) =
      evalDist ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) := by
  let RowChallenge := Matrix (Fin ringRank)
    (Fin (TGSW.rowCount ringRank tgswLevels)) (RLWE.Rq q degree)
  let RowOutput := Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree
  let Challenge := ParallelChallenge (RLWE.Rq q degree)
    ringRank tgswLevels lweDimension
  let Output := ParallelOutput (RLWE.Rq q degree)
    ringRank tgswLevels lweDimension
  let challenges : ProbComp Challenge :=
    ProbComp.sampleIID lweDimension ($ᵗ RowChallenge)
  let rowErrors : ProbComp RowOutput :=
    ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) ($ᵗ (RLWE.Rq q degree))
  let errors : ProbComp Output := ProbComp.sampleIID lweDimension rowErrors
  have hChallenges : evalDist challenges = evalDist ($ᵗ Challenge) := by
    simpa [challenges, Challenge, RowChallenge] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := RowChallenge) lweDimension)
  have hRowErrors : evalDist rowErrors = evalDist ($ᵗ RowOutput) := by
    simpa [rowErrors, RowOutput] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := RLWE.Rq q degree) (TGSW.rowCount ringRank tgswLevels))
  have hErrors : evalDist errors = evalDist ($ᵗ Output) := by
    calc
      evalDist errors =
          evalDist (ProbComp.sampleIID lweDimension ($ᵗ RowOutput)) := by
        exact FormalProof4FHE.SharedRandomness.sampleIID_evalDist_congr
          lweDimension hRowErrors
      _ = evalDist ($ᵗ Output) := by
        simpa [Output, RowOutput] using
          (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
            (alpha := RowOutput) lweDimension)
  let shift : Challenge → Output := fun challenge ↦
    fun coordinate ↦ vecMul (embedRingSecret q ringSecret) (challenge coordinate)
  let addOutput : Output → Output → Output :=
    @Add.add Output
      (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension)
  have hAddComm (left right : Output) :
      addOutput left right = addOutput right left := by
    change @Add.add Output
        (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension) left right =
      @Add.add Output
        (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension) right left
    exact add_comm left right
  have hAssemble (challenge : Challenge) (error : Output) :
      (fun coordinate ↦ semiringRqPiAdd q degree
        (vecMul (embedRingSecret q ringSecret) (challenge coordinate))
        (error coordinate)) = addOutput (shift challenge) error := by
    rfl
  have hAssembleNative (challenge : Challenge) (error : Output) :
      (fun coordinate ↦
        vecMul (embedRingSecret q ringSecret) (challenge coordinate) + error coordinate) =
          addOutput (shift challenge) error := by
    rw [← hAssemble challenge error]
    funext coordinate
    exact (semiringRqPiAdd_eq_add q degree
      (vecMul (embedRingSecret q ringSecret) (challenge coordinate))
      (error coordinate)).symm
  have hShift (challenge : Challenge) :
      evalDist (($ᵗ Output) >>= fun error ↦
        pure (challenge, addOutput (shift challenge) error)) =
        evalDist (($ᵗ Output) >>= fun output ↦ pure (challenge, output)) := by
    have h := evalDist_bind_bijective_add_right_uniform
        (α := Output) (β := Output) id Function.bijective_id (shift challenge)
        (fun output ↦ (pure (challenge, output) : ProbComp (Challenge × Output)))
    change evalDist (($ᵗ Output) >>= fun error ↦
        pure (challenge, addOutput error (shift challenge))) =
      evalDist (($ᵗ Output) >>= fun output ↦ pure (challenge, output)) at h
    rw [show (fun error : Output ↦
        (pure (challenge, addOutput (shift challenge) error) :
          ProbComp (Challenge × Output))) =
      fun error ↦ pure (challenge, addOutput error (shift challenge)) by
        funext error
        rw [hAddComm]]
    exact h
  have uniformProduct :
      ($ᵗ (Challenge × Output) : ProbComp (Challenge × Output)) =
        Prod.mk <$> ($ᵗ Challenge) <*> ($ᵗ Output) := rfl
  calc
    evalDist (sampleParallelHomogeneous q degree ringRank tgswLevels lweDimension
        ($ᵗ (RLWE.Rq q degree)) ringSecret) =
      evalDist (challenges >>= fun challenge ↦
        errors >>= fun error ↦ pure (challenge, addOutput (shift challenge) error)) := by
      simp [sampleParallelHomogeneous, challenges, errors, rowErrors,
        RowChallenge, RowOutput, Challenge, Output, ProbComp.sampleIID,
        hAssembleNative, monad_norm]
    _ = evalDist (($ᵗ Challenge) >>= fun challenge ↦
        errors >>= fun error ↦ pure (challenge, addOutput (shift challenge) error)) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hChallenges (fun challenge ↦
          errors >>= fun error ↦ pure (challenge, addOutput (shift challenge) error))
    _ = evalDist (($ᵗ Challenge) >>= fun challenge ↦
        ($ᵗ Output) >>= fun error ↦
          pure (challenge, addOutput (shift challenge) error)) := by
      refine evalDist_bind_congr' ($ᵗ Challenge) fun challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hErrors (fun error ↦ pure (challenge, addOutput (shift challenge) error))
    _ = evalDist (($ᵗ Challenge) >>= fun challenge ↦
        ($ᵗ Output) >>= fun output ↦ pure (challenge, output)) := by
      exact evalDist_bind_congr' ($ᵗ Challenge) hShift
    _ = evalDist ($ᵗ (Challenge × Output)) := by
      rw [uniformProduct]
      simp [monad_norm]
    _ = evalDist ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) := by
      rfl

/-- A native zero-message BRK generated with uniform ring errors is exactly uniform on the
native bootstrapping-key carrier, for every fixed ring secret and every gadget. -/
theorem generateZeroBootstrappingKey_uniformError_evalDist
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist (generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
      ($ᵗ (RLWE.Rq q degree)) gadget ringSecret) =
      evalDist ($ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)) := by
  calc
    _ = evalDist (sampleParallelZeroBootstrap q degree ringRank tgswLevels lweDimension
        ($ᵗ (RLWE.Rq q degree)) ringSecret) :=
      generateZeroBootstrappingKey_evalDist_eq_parallel q degree ringRank tgswLevels
        lweDimension ($ᵗ (RLWE.Rq q degree)) gadget ringSecret
    _ = evalDist (transcriptToBootstrappingKey <$>
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension))) := by
      unfold sampleParallelZeroBootstrap
      simpa [map_eq_bind_pure_comp] using
        (evalDist_map_eq_of_evalDist_eq
          (sampleParallelHomogeneous_uniformError_evalDist q degree ringRank tgswLevels
            lweDimension ringSecret) transcriptToBootstrappingKey)
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
      (β := BootstrappingKey q degree ringRank tgswLevels lweDimension)
      transcriptToBootstrappingKey transcriptToBootstrappingKey_bijective

/-- A continuation that receives the scalar secret and public cloud-key components but has no
direct access to the hidden ring secret.  Native IND-CPA continuations have exactly this shape. -/
abbrev Continuation
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  BinarySecret lweDimension →
    BootstrappingKey q degree ringRank tgswLevels lweDimension →
    KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels → ProbComp Bool

/-- Independently sample the scalar key together with a zero-message KSK under that key. -/
def zeroKeySwitchContext
    (q degree ringRank lweDimension keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q)) :
    ProbComp (BinarySecret lweDimension ×
      KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := do
  let lweSecret ← sampleLweSecret lweDimension
  let keySwitchKey ← generateZeroKeySwitchKey q lweDimension (ringRank * degree)
    keySwitchLevels keySwitchErrorSampler lweSecret
  return (lweSecret, keySwitchKey)

/-- Native cut-cycle endpoint with a real bootstrapping key and a zero-message KSK. -/
noncomputable def realCutGame
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let context ← zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget context.1 ringSecret
  continuation context.1 bootstrapKey context.2

/-- Native cut-cycle endpoint with both evaluation-key directions carrying zero messages. -/
noncomputable def zeroCutGame
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let context ← zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget ringSecret
  continuation context.1 bootstrapKey context.2

/-- The same real endpoint using the all-challenges-before-all-errors parallel sampler. -/
noncomputable def parallelRealCutGame
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let context ← zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← sampleParallelRealBootstrap q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget context.1 ringSecret
  continuation context.1 bootstrapKey context.2

/-- The analogous parallel zero endpoint. -/
noncomputable def parallelZeroCutGame
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let context ← zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← sampleParallelZeroBootstrap q degree ringRank tgswLevels lweDimension
    ringErrorSampler ringSecret
  continuation context.1 bootstrapKey context.2

theorem realCutGame_evalDist_eq_parallel
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (realCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
      evalDist (parallelRealCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget continuation) := by
  unfold realCutGame parallelRealCutGame
  refine evalDist_bind_congr'
    (zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
      keySwitchErrorSampler) fun context ↦ ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  rw [evalDist_bind, evalDist_bind,
    generateBootstrappingKey_evalDist_eq_parallel q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget context.1 ringSecret]

theorem zeroCutGame_evalDist_eq_parallel
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (zeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
      evalDist (parallelZeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler continuation) := by
  unfold zeroCutGame parallelZeroCutGame
  refine evalDist_bind_congr'
    (zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
      keySwitchErrorSampler) fun _ ↦ ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  rw [evalDist_bind, evalDist_bind,
    generateZeroBootstrappingKey_evalDist_eq_parallel q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget ringSecret]

/-- Reduction for the real-message side of the cut-cycle bootstrapping comparison. -/
noncomputable def realMessageReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler) :=
  fun transcript ↦ do
    let context ← zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
      keySwitchErrorSampler
    let bootstrapKey := fun coordinate ↦
      TGSW.addGadget tgswGadget
        (embedConstantBit q degree (context.1 coordinate))
        (transcriptToBootstrappingKey transcript coordinate)
    continuation context.1 bootstrapKey context.2

/-- Reduction for the zero-message side of the cut-cycle bootstrapping comparison. -/
noncomputable def zeroMessageReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler) :=
  fun transcript ↦ do
    let context ← zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
      keySwitchErrorSampler
    continuation context.1 (transcriptToBootstrappingKey transcript) context.2

/-- Conventional single-batch reduction obtained by unflattening one combined ring transcript
before running the real-message cut reduction. -/
noncomputable def realBatchReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler) :=
  FormalProof4FHE.LWE.ParallelBatch.reduction
    (realMessageReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation)

/-- Conventional single-batch reduction for the zero-message cut endpoint. -/
noncomputable def zeroBatchReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler) :=
  FormalProof4FHE.LWE.ParallelBatch.reduction
    (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation)

/-- The real cut reduction has exactly the advantage of its conventional flattened-batch
reduction. -/
theorem realMessageReduction_advantage_eq_batch
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LearningWithErrors.advantage
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
      LearningWithErrors.advantage
        (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (realBatchReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation) := by
  have h := FormalProof4FHE.LWE.ParallelBatch.advantage_eq_batch ringRank lweDimension
    (TGSW.rowCount ringRank tgswLevels) (sampleRingSecret ringRank degree)
    (embedRingSecret q) ringErrorSampler
    (realMessageReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation)
  change @LearningWithErrors.advantage
      (ParallelChallenge (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
      (RingBinarySecret ringRank degree)
      (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
      (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension)
      (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
      (realMessageReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
    @LearningWithErrors.advantage
      (Matrix (Fin ringRank)
        (Fin (lweDimension * TGSW.rowCount ringRank tgswLevels)) (RLWE.Rq q degree))
      (RingBinarySecret ringRank degree)
      (Fin (lweDimension * TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)
      (FormalProof4FHE.RLWE.RingRegev.semiringOutputAdd q degree
        (lweDimension * TGSW.rowCount ringRank tgswLevels))
      (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
      (realBatchReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation) at h
  rw [semiringParallelOutputAdd_eq,
    FormalProof4FHE.RLWE.RingRegev.semiringOutputAdd_eq] at h
  exact h

/-- The zero-message cut reduction has exactly the advantage of its conventional flattened-batch
reduction. -/
theorem zeroMessageReduction_advantage_eq_batch
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    LearningWithErrors.advantage
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation) =
      LearningWithErrors.advantage
        (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (zeroBatchReduction ringErrorSampler keySwitchErrorSampler continuation) := by
  have h := FormalProof4FHE.LWE.ParallelBatch.advantage_eq_batch ringRank lweDimension
    (TGSW.rowCount ringRank tgswLevels) (sampleRingSecret ringRank degree)
    (embedRingSecret q) ringErrorSampler
    (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation)
  change @LearningWithErrors.advantage
      (ParallelChallenge (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
      (RingBinarySecret ringRank degree)
      (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension)
      (semiringParallelOutputAdd q degree ringRank tgswLevels lweDimension)
      (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
      (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation) =
    @LearningWithErrors.advantage
      (Matrix (Fin ringRank)
        (Fin (lweDimension * TGSW.rowCount ringRank tgswLevels)) (RLWE.Rq q degree))
      (RingBinarySecret ringRank degree)
      (Fin (lweDimension * TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)
      (FormalProof4FHE.RLWE.RingRegev.semiringOutputAdd q degree
        (lweDimension * TGSW.rowCount ringRank tgswLevels))
      (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
      (zeroBatchReduction ringErrorSampler keySwitchErrorSampler continuation) at h
  rw [semiringParallelOutputAdd_eq,
    FormalProof4FHE.RLWE.RingRegev.semiringOutputAdd_eq] at h
  exact h

/-- The parallel real cut-cycle endpoint is exactly the real branch of the
parallel binary-secret module-LWE reduction. -/
theorem parallelRealCutGame_evalDist_eq_lwe_game0
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (parallelRealCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
      evalDist (LearningWithErrors.game0
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget continuation)) := by
  let contexts := zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let ringSecrets := sampleRingSecret ringRank degree
  let challenges : ProbComp
      (ParallelChallenge (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _ ↦
      $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)
  let errors : ProbComp
      (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) ringErrorSampler
  let finish := fun
      (context : BinarySecret lweDimension ×
        KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (ringSecret : RingBinarySecret ringRank degree)
      (challenge : ParallelChallenge (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)
      (error : ParallelOutput (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension) ↦
    continuation context.1
      (fun coordinate ↦ TGSW.addGadget tgswGadget
        (embedConstantBit q degree (context.1 coordinate))
        (transcriptToBootstrappingKey
          (challenge,
            (fun coordinate ↦
              vecMul (embedRingSecret q ringSecret) (challenge coordinate)) + error)
          coordinate))
      context.2
  have parallel_eq :
      parallelRealCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget continuation =
        (contexts >>= fun context ↦
          ringSecrets >>= fun ringSecret ↦
          challenges >>= fun challenge ↦
          errors >>= fun error ↦
          finish context ringSecret challenge error) := by
    simp [parallelRealCutGame, sampleParallelRealBootstrap,
      sampleParallelHomogeneous, contexts, ringSecrets, challenges, errors, finish,
      pointwiseAdd_eq_add, bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (realMessageReduction ringErrorSampler keySwitchErrorSampler
            tgswGadget continuation) =
        (challenges >>= fun challenge ↦
          ringSecrets >>= fun ringSecret ↦
          errors >>= fun error ↦
          contexts >>= fun context ↦
          finish context ringSecret challenge error) := by
    simp [LearningWithErrors.game0, LearningWithErrors.distr,
      parallelModuleLweProblem, realMessageReduction, contexts, ringSecrets,
      challenges, errors, finish, bind_assoc, monad_norm]
  rw [parallel_eq, lwe_eq]
  calc
    _ = evalDist (ringSecrets >>= fun ringSecret ↦
        contexts >>= fun context ↦
        challenges >>= fun challenge ↦
        errors >>= fun error ↦
        finish context ringSecret challenge error) :=
      evalDist_bind_bind_swap contexts ringSecrets
        (fun context ringSecret ↦ challenges >>= fun challenge ↦
          errors >>= fun error ↦ finish context ringSecret challenge error)
    _ = _ :=
      KeySwitchSecurity.evalDist_bind_four_reorder ringSecrets contexts challenges errors
        (fun ringSecret context challenge error ↦
          finish context ringSecret challenge error)

/-- The parallel all-zero cut-cycle endpoint is exactly the real branch of the
pass-through parallel module-LWE reduction. -/
theorem parallelZeroCutGame_evalDist_eq_lwe_game0
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (parallelZeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler continuation) =
      evalDist (LearningWithErrors.game0
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation)) := by
  let contexts := zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let ringSecrets := sampleRingSecret ringRank degree
  let challenges : ProbComp
      (ParallelChallenge (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _ ↦
      $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)
  let errors : ProbComp
      (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount ringRank tgswLevels) ringErrorSampler
  let finish := fun
      (context : BinarySecret lweDimension ×
        KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (ringSecret : RingBinarySecret ringRank degree)
      (challenge : ParallelChallenge (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)
      (error : ParallelOutput (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension) ↦
    continuation context.1
      (transcriptToBootstrappingKey
        (challenge,
          (fun coordinate ↦
            vecMul (embedRingSecret q ringSecret) (challenge coordinate)) + error))
      context.2
  have parallel_eq :
      parallelZeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler continuation =
        (contexts >>= fun context ↦
          ringSecrets >>= fun ringSecret ↦
          challenges >>= fun challenge ↦
          errors >>= fun error ↦
          finish context ringSecret challenge error) := by
    simp [parallelZeroCutGame, sampleParallelZeroBootstrap,
      sampleParallelHomogeneous, contexts, ringSecrets, challenges, errors, finish,
      pointwiseAdd_eq_add, bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation) =
        (challenges >>= fun challenge ↦
          ringSecrets >>= fun ringSecret ↦
          errors >>= fun error ↦
          contexts >>= fun context ↦
          finish context ringSecret challenge error) := by
    simp [LearningWithErrors.game0, LearningWithErrors.distr,
      parallelModuleLweProblem, zeroMessageReduction, contexts, ringSecrets,
      challenges, errors, finish, bind_assoc, monad_norm]
  rw [parallel_eq, lwe_eq]
  calc
    _ = evalDist (ringSecrets >>= fun ringSecret ↦
        contexts >>= fun context ↦
        challenges >>= fun challenge ↦
        errors >>= fun error ↦
        finish context ringSecret challenge error) :=
      evalDist_bind_bind_swap contexts ringSecrets
        (fun context ringSecret ↦ challenges >>= fun challenge ↦
          errors >>= fun error ↦ finish context ringSecret challenge error)
    _ = _ :=
      KeySwitchSecurity.evalDist_bind_four_reorder ringSecrets contexts challenges errors
        (fun ringSecret context challenge error ↦
          finish context ringSecret challenge error)

/-- The uniform branch of the parallel module-LWE problem is the canonical uniform sampler on
the complete unzipped native bootstrapping-key transcript. -/
theorem parallelUniformDistr_evalDist_eq_uniformSample
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree)) :
    evalDist (LearningWithErrors.uniformDistr
      (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)) =
      evalDist ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) := by
  let challengeSampler : ProbComp
      (ParallelChallenge (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _ ↦
      $ᵗ Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
        (RLWE.Rq q degree)
  let outputSampler : ProbComp
      (ParallelOutput (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :=
    Fin.mOfFn lweDimension fun _ ↦
      $ᵗ (Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)
  have hChallenge :
      evalDist challengeSampler =
        evalDist ($ᵗ (ParallelChallenge (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) := by
    simpa [challengeSampler, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank tgswLevels))
          (RLWE.Rq q degree)) lweDimension)
  have hOutput :
      evalDist outputSampler =
        evalDist ($ᵗ (ParallelOutput (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) := by
    simpa [outputSampler, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Fin (TGSW.rowCount ringRank tgswLevels) → RLWE.Rq q degree)
        lweDimension)
  have uniformProduct :
      ($ᵗ (ParallelTranscript (RLWE.Rq q degree) ringRank tgswLevels lweDimension) :
        ProbComp (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) =
      Prod.mk <$>
        ($ᵗ (ParallelChallenge (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) <*>
        ($ᵗ (ParallelOutput (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) := by
    rfl
  change evalDist (challengeSampler >>= fun challenge ↦
      outputSampler >>= fun output ↦ pure (challenge, output)) = _
  calc
    _ = evalDist (($ᵗ (ParallelChallenge (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun challenge ↦
        outputSampler >>= fun output ↦ pure (challenge, output)) := by
      rw [evalDist_bind, evalDist_bind, hChallenge]
    _ = evalDist (($ᵗ (ParallelChallenge (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun challenge ↦
        ($ᵗ (ParallelOutput (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun output ↦
        pure (challenge, output)) := by
      refine evalDist_bind_congr'
        ($ᵗ (ParallelChallenge (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) fun _ ↦ ?_
      rw [evalDist_bind, evalDist_bind, hOutput]
    _ = evalDist ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) := by
      rw [uniformProduct]
      simp [monad_norm]

/-- Adding fixed coordinate-dependent gadget matrices preserves a uniform complete parallel
transcript, even after an arbitrary continuation. -/
theorem uniformParallelTranscript_shift_evalDist
    {q degree ringRank tgswLevels lweDimension : ℕ} {Output : Type} [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : Fin lweDimension → RLWE.Rq q degree)
    (finish : ParallelTranscript (RLWE.Rq q degree)
      ringRank tgswLevels lweDimension → ProbComp Output) :
    evalDist (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) >>= fun transcript ↦
      finish (shiftTranscript gadget message transcript)) =
    evalDist (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) >>= finish) := by
  have hShift :
      evalDist (shiftTranscript (ringRank := ringRank) gadget message <$>
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension))) =
      evalDist ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) :=
    evalDist_map_bijective_uniform_cross
      (α := ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)
      (β := ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)
      (shiftTranscript gadget message) (shiftTranscript_bijective gadget message)
  rw [show (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) >>= fun transcript ↦
      finish (shiftTranscript gadget message transcript)) =
      ((shiftTranscript gadget message <$>
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension))) >>= finish) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind, hShift]

/-- The same uniform-translation fact when the message is selected by an independently sampled
context, such as the scalar key paired with its zero-message key-switch key. -/
theorem uniformParallelTranscript_context_shift_evalDist
    {q degree ringRank tgswLevels lweDimension : ℕ} {Context Output : Type} [NeZero q]
    (contextSampler : ProbComp Context)
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : Context → Fin lweDimension → RLWE.Rq q degree)
    (finish : Context → ParallelTranscript (RLWE.Rq q degree)
      ringRank tgswLevels lweDimension → ProbComp Output) :
    evalDist (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) >>= fun transcript ↦
      contextSampler >>= fun context ↦
      finish context (shiftTranscript gadget (message context) transcript)) =
    evalDist (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension)) >>= fun transcript ↦
      contextSampler >>= fun context ↦ finish context transcript) := by
  calc
    _ = evalDist (contextSampler >>= fun context ↦
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun transcript ↦
        finish context (shiftTranscript gadget (message context) transcript)) :=
      evalDist_bind_bind_swap
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) contextSampler
        (fun transcript context ↦
          finish context (shiftTranscript gadget (message context) transcript))
    _ = evalDist (contextSampler >>= fun context ↦
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun transcript ↦
        finish context transcript) := by
      refine evalDist_bind_congr' contextSampler fun context ↦ ?_
      exact uniformParallelTranscript_shift_evalDist gadget (message context)
        (finish context)
    _ = _ :=
      (evalDist_bind_bind_swap
        ($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) contextSampler
        (fun transcript context ↦ finish context transcript)).symm

/-- The real-message and zero-message cut-cycle reductions meet at exactly the same uniform
parallel module-LWE branch. -/
theorem reductions_game1_evalDist_eq
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (LearningWithErrors.game1
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget continuation)) =
      evalDist (LearningWithErrors.game1
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation)) := by
  let contexts := zeroKeySwitchContext q degree ringRank lweDimension keySwitchLevels
    keySwitchErrorSampler
  let message := fun
      (context : BinarySecret lweDimension ×
        KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (coordinate : Fin lweDimension) ↦
    embedConstantBit q degree (context.1 coordinate)
  let finish := fun
      (context : BinarySecret lweDimension ×
        KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (transcript : ParallelTranscript (RLWE.Rq q degree)
        ringRank tgswLevels lweDimension) ↦
    continuation context.1 (transcriptToBootstrappingKey transcript) context.2
  have real_eq :
      LearningWithErrors.game1
          (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (realMessageReduction ringErrorSampler keySwitchErrorSampler
            tgswGadget continuation) =
        (LearningWithErrors.uniformDistr
            (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension
              ringErrorSampler) >>= fun transcript ↦
          contexts >>= fun context ↦
          finish context (shiftTranscript tgswGadget (message context) transcript)) := by
    simp [LearningWithErrors.game1, realMessageReduction, contexts, message, finish,
      monad_norm]
  have zero_eq :
      LearningWithErrors.game1
          (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation) =
        (LearningWithErrors.uniformDistr
            (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension
              ringErrorSampler) >>= fun transcript ↦
          contexts >>= fun context ↦ finish context transcript) := by
    simp [LearningWithErrors.game1, zeroMessageReduction, contexts, finish,
      monad_norm]
  rw [real_eq, zero_eq]
  calc
    _ = evalDist (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun transcript ↦
        contexts >>= fun context ↦
        finish context (shiftTranscript tgswGadget (message context) transcript)) := by
      rw [evalDist_bind, evalDist_bind,
        parallelUniformDistr_evalDist_eq_uniformSample q degree ringRank tgswLevels
          lweDimension ringErrorSampler]
    _ = evalDist (($ᵗ (ParallelTranscript (RLWE.Rq q degree)
          ringRank tgswLevels lweDimension)) >>= fun transcript ↦
        contexts >>= fun context ↦ finish context transcript) :=
      uniformParallelTranscript_context_shift_evalDist contexts tgswGadget message finish
    _ = _ := by
      rw [evalDist_bind, evalDist_bind,
        parallelUniformDistr_evalDist_eq_uniformSample q degree ringRank tgswLevels
          lweDimension ringErrorSampler]

/-- Distinguishing a real native bootstrapping key from a zero-message bootstrapping key after
cutting the opposite KSK edge. -/
noncomputable def cutBootstrapReplacementAdvantage
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) : ℝ :=
  (realCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget continuation).boolDistAdvantage
  (zeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget continuation)

/-- **Native cut-cycle bootstrapping replacement theorem.** Once the opposite key-switch edge
carries only zero messages, replacing all native TGSW encryptions of scalar-key bits by
zero-message rows costs at most two advantages for ordinary parallel binary-secret module-LWE.
No circular-security premise is used in this theorem. -/
theorem cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    cutBootstrapReplacementAdvantage q degree ringRank tgswLevels lweDimension
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget continuation ≤
      LearningWithErrors.advantage
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget continuation) +
      LearningWithErrors.advantage
        (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold cutBootstrapReplacementAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realCutGame_evalDist_eq_parallel ringErrorSampler keySwitchErrorSampler
        tgswGadget continuation) true,
    evalDist_ext_iff.mp
      (parallelRealCutGame_evalDist_eq_lwe_game0 ringErrorSampler
        keySwitchErrorSampler tgswGadget continuation) true,
    evalDist_ext_iff.mp
      (zeroCutGame_evalDist_eq_parallel ringErrorSampler keySwitchErrorSampler
        tgswGadget continuation) true,
    evalDist_ext_iff.mp
      (parallelZeroCutGame_evalDist_eq_lwe_game0 ringErrorSampler
        keySwitchErrorSampler continuation) true]
  let realProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
    (realMessageReduction ringErrorSampler keySwitchErrorSampler
      tgswGadget continuation)]).toReal
  let uniformRealProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
    (realMessageReduction ringErrorSampler keySwitchErrorSampler
      tgswGadget continuation)]).toReal
  let uniformZeroProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
    (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation)]).toReal
  let zeroProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (parallelModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
    (zeroMessageReduction ringErrorSampler keySwitchErrorSampler continuation)]).toReal
  have hUniform : uniformRealProbability = uniformZeroProbability := by
    exact congrArg ENNReal.toReal (evalDist_ext_iff.mp
      (reductions_game1_evalDist_eq ringErrorSampler keySwitchErrorSampler
        tgswGadget continuation) true)
  change |realProbability - zeroProbability| ≤
    |realProbability - uniformRealProbability| +
      |zeroProbability - uniformZeroProbability|
  rw [hUniform, abs_sub_comm zeroProbability uniformZeroProbability]
  exact abs_sub_le realProbability uniformZeroProbability zeroProbability

/-- Flattened form of the cut-cycle theorem: the post-cut native BRK hop costs at most two
advantages for one conventional binary-secret ring batch-LWE problem with
`lweDimension * TGSW.rowCount` samples. -/
theorem cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    cutBootstrapReplacementAdvantage q degree ringRank tgswLevels lweDimension
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget continuation ≤
      LearningWithErrors.advantage
        (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (realBatchReduction ringErrorSampler keySwitchErrorSampler tgswGadget continuation) +
      LearningWithErrors.advantage
        (batchModuleLweProblem q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (zeroBatchReduction ringErrorSampler keySwitchErrorSampler continuation) := by
  have h := cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    ringErrorSampler keySwitchErrorSampler tgswGadget continuation
  rw [realMessageReduction_advantage_eq_batch,
    zeroMessageReduction_advantage_eq_batch] at h
  exact h

/-- Regard a ring-secret-independent cut-cycle continuation as an ordinary circular
continuation. -/
def liftContinuation
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
  fun lweSecret _ bootstrapKey keySwitchKey ↦
    continuation lweSecret bootstrapKey keySwitchKey

/-- The concrete real-BRK/zero-KSK cut game is exactly the alternative abstract circular hybrid,
up to reordering independent KSK and ring-key randomness. -/
theorem realCutGame_evalDist_eq_keySwitchZeroContinuationGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (realCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
      evalDist (Circular.keySwitchZeroContinuationGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (liftContinuation continuation)) := by
  let scalarSecrets := sampleLweSecret lweDimension
  let ringSecrets := sampleRingSecret ringRank degree
  let zeroKeySwitchKeys := fun lweSecret : BinarySecret lweDimension ↦
    generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler lweSecret
  let bootstrapKeys := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree) ↦
    generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (_ : RingBinarySecret ringRank degree)
      (bootstrapKey : BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) ↦
    continuation lweSecret bootstrapKey keySwitchKey
  have cut_eq :
      realCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget continuation =
        (scalarSecrets >>= fun lweSecret ↦
          zeroKeySwitchKeys lweSecret >>= fun keySwitchKey ↦
          ringSecrets >>= fun ringSecret ↦
          bootstrapKeys lweSecret ringSecret >>= fun bootstrapKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey) := by
    simp [realCutGame, zeroKeySwitchContext, scalarSecrets, ringSecrets,
      zeroKeySwitchKeys, bootstrapKeys, finish, bind_assoc, monad_norm]
  have abstract_eq :
      Circular.keySwitchZeroContinuationGame
          (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (liftContinuation continuation) =
        (scalarSecrets >>= fun lweSecret ↦
          ringSecrets >>= fun ringSecret ↦
          bootstrapKeys lweSecret ringSecret >>= fun bootstrapKey ↦
          zeroKeySwitchKeys lweSecret >>= fun keySwitchKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey) := by
    simp [Circular.keySwitchZeroContinuationGame, nativeCycleSpec, liftContinuation,
      scalarSecrets, ringSecrets, zeroKeySwitchKeys, bootstrapKeys, finish,
      monad_norm]
  rw [cut_eq, abstract_eq]
  refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
  calc
    _ = evalDist (ringSecrets >>= fun ringSecret ↦
        zeroKeySwitchKeys lweSecret >>= fun keySwitchKey ↦
        bootstrapKeys lweSecret ringSecret >>= fun bootstrapKey ↦
        finish lweSecret ringSecret bootstrapKey keySwitchKey) :=
      evalDist_bind_bind_swap (zeroKeySwitchKeys lweSecret) ringSecrets
        (fun keySwitchKey ringSecret ↦
          bootstrapKeys lweSecret ringSecret >>= fun bootstrapKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey)
    _ = _ := by
      refine evalDist_bind_congr' ringSecrets fun ringSecret ↦ ?_
      exact evalDist_bind_bind_swap (zeroKeySwitchKeys lweSecret)
        (bootstrapKeys lweSecret ringSecret)
        (fun keySwitchKey bootstrapKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey)

/-- The concrete all-zero cut endpoint is the abstract all-zero circular endpoint for the lifted
continuation. -/
theorem zeroCutGame_evalDist_eq_zeroContinuationGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (zeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget continuation) =
      evalDist (Circular.zeroContinuationGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (liftContinuation continuation)) := by
  let scalarSecrets := sampleLweSecret lweDimension
  let ringSecrets := sampleRingSecret ringRank degree
  let zeroKeySwitchKeys := fun lweSecret : BinarySecret lweDimension ↦
    generateZeroKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler lweSecret
  let zeroBootstrapKeys := fun ringSecret : RingBinarySecret ringRank degree ↦
    generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget ringSecret
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (_ : RingBinarySecret ringRank degree)
      (bootstrapKey : BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) ↦
    continuation lweSecret bootstrapKey keySwitchKey
  have cut_eq :
      zeroCutGame q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget continuation =
        (scalarSecrets >>= fun lweSecret ↦
          zeroKeySwitchKeys lweSecret >>= fun keySwitchKey ↦
          ringSecrets >>= fun ringSecret ↦
          zeroBootstrapKeys ringSecret >>= fun bootstrapKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey) := by
    simp [zeroCutGame, zeroKeySwitchContext, scalarSecrets, ringSecrets,
      zeroKeySwitchKeys, zeroBootstrapKeys, finish, bind_assoc, monad_norm]
  have abstract_eq :
      Circular.zeroContinuationGame
          (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (liftContinuation continuation) =
        (scalarSecrets >>= fun lweSecret ↦
          ringSecrets >>= fun ringSecret ↦
          zeroBootstrapKeys ringSecret >>= fun bootstrapKey ↦
          zeroKeySwitchKeys lweSecret >>= fun keySwitchKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey) := by
    simp [Circular.zeroContinuationGame, nativeCycleSpec, liftContinuation,
      scalarSecrets, ringSecrets, zeroKeySwitchKeys, zeroBootstrapKeys, finish,
      monad_norm]
  rw [cut_eq, abstract_eq]
  refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
  calc
    _ = evalDist (ringSecrets >>= fun ringSecret ↦
        zeroKeySwitchKeys lweSecret >>= fun keySwitchKey ↦
        zeroBootstrapKeys ringSecret >>= fun bootstrapKey ↦
        finish lweSecret ringSecret bootstrapKey keySwitchKey) :=
      evalDist_bind_bind_swap (zeroKeySwitchKeys lweSecret) ringSecrets
        (fun keySwitchKey ringSecret ↦
          zeroBootstrapKeys ringSecret >>= fun bootstrapKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey)
    _ = _ := by
      refine evalDist_bind_congr' ringSecrets fun ringSecret ↦ ?_
      exact evalDist_bind_bind_swap (zeroKeySwitchKeys lweSecret)
        (zeroBootstrapKeys ringSecret)
        (fun keySwitchKey bootstrapKey ↦
          finish lweSecret ringSecret bootstrapKey keySwitchKey)

/-- The concrete cut-cycle advantage is exactly the alternative abstract second-hop advantage. -/
theorem cutBootstrapReplacementAdvantage_eq_continuationBootstrapAfterKeySwitch
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Continuation q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    cutBootstrapReplacementAdvantage q degree ringRank tgswLevels lweDimension
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget continuation =
      Circular.continuationBootstrapAfterKeySwitchReplacementAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (liftContinuation continuation) := by
  unfold cutBootstrapReplacementAdvantage
    Circular.continuationBootstrapAfterKeySwitchReplacementAdvantage
    ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (realCutGame_evalDist_eq_keySwitchZeroContinuationGame ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget continuation) true,
    evalDist_ext_iff.mp
      (zeroCutGame_evalDist_eq_zeroContinuationGame ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget continuation) true]

end FormalProof4FHE.TFHE.Native.BootstrapCutSecurity

namespace FormalProof4FHE.TFHE.Encryption.CutCycleSecurity

open Native

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]

/-- The adaptive one-time TFHE continuation, restricted to the interface that intentionally hides
the unused ring secret from the reduction. -/
def oneTimeContinuation
    (inputErrorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Native.BootstrapCutSecurity.Continuation q degree ringRank tgswLevels
      lweDimension keySwitchLevels :=
  fun lweSecret bootstrapKey keySwitchKey ↦
    Encryption.oneTimeContinuation inputErrorSampler encode adversary
      lweSecret (fun _ _ ↦ false) bootstrapKey keySwitchKey

/-- Lifting the restricted continuation recovers the original TFHE one-time continuation exactly,
because that experiment never inspects the ring secret directly. -/
theorem lift_oneTimeContinuation
    (inputErrorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Native.BootstrapCutSecurity.liftContinuation
        (oneTimeContinuation inputErrorSampler encode adversary) =
      Encryption.oneTimeContinuation inputErrorSampler encode adversary := by
  funext lweSecret ringSecret bootstrapKey keySwitchKey
  rfl

/-- Alternative adaptive one-time hybrid with the native real BRK and a zero-message KSK. -/
noncomputable def oneTimeKeySwitchZeroGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.keySwitchZeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (Encryption.oneTimeContinuation inputErrorSampler encode adversary)

/-- Intact-cycle first-hop cost when the KSK is replaced before the BRK. -/
noncomputable def oneTimeKeySwitchFirstReplacementAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (oneTimeKeySwitchZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- The native one-time first-hop cost is exactly the generic KSK-first intact-cycle KDM cost for
the induced secret-dependent continuation. -/
theorem oneTimeKeySwitchFirstReplacementAdvantage_eq_abstract
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      Circular.continuationKeySwitchFirstReplacementAdvantage
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (Encryption.oneTimeContinuation inputErrorSampler encode adversary) := by
  rfl

/-- Adaptive one-time distinguishing cost between the alternative hybrid with a real BRK and a
zero-message KSK, and the all-zero-message cloud-key hybrid. -/
noncomputable def oneTimeCutBootstrapReplacementAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- The one-time cut advantage is the second hop of the alternative abstract circular hybrid. -/
theorem oneTimeCutBootstrapReplacementAdvantage_eq_abstract
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneTimeCutBootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary =
      Circular.continuationBootstrapAfterKeySwitchReplacementAdvantage
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (Encryption.oneTimeContinuation inputErrorSampler encode adversary) := by
  rw [← lift_oneTimeContinuation inputErrorSampler encode adversary]
  exact Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_eq_continuationBootstrapAfterKeySwitch
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- The adaptive TFHE circular advantage decomposed in KSK-first order.  The second summand is the
concrete post-cut advantage already reduced below to parallel module-LWE. -/
theorem circularAdvantage_le_keySwitchFirst_add_cutBootstrap
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Encryption.circularAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary ≤
      oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        oneTimeCutBootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary := by
  have h := Circular.continuationCircularAdvantage_le_keySwitchFirst_add_bootstrapAfter
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (Encryption.oneTimeContinuation inputErrorSampler encode adversary)
  rw [← oneTimeCutBootstrapReplacementAdvantage_eq_abstract ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] at h
  simpa [Encryption.circularAdvantage, Encryption.realGame, Encryption.zeroCloudGame,
    oneTimeKeySwitchFirstReplacementAdvantage, oneTimeKeySwitchZeroGame,
    Circular.continuationCircularAdvantage,
    Circular.continuationKeySwitchFirstReplacementAdvantage] using h

/-- The original BRK-first intact-cycle term is no larger than the alternative KSK-first term
plus the two post-cut edges. -/
theorem bootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        oneTimeCutBootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary +
        Encryption.keySwitchReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary := by
  have h :=
    Circular.continuationBootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
      (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (Encryption.oneTimeContinuation inputErrorSampler encode adversary)
  rw [← oneTimeCutBootstrapReplacementAdvantage_eq_abstract ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] at h
  simpa [Encryption.bootstrapReplacementAdvantage,
    Encryption.keySwitchReplacementAdvantage, Encryption.realGame,
    Encryption.bootstrapZeroGame, Encryption.zeroCloudGame,
    oneTimeKeySwitchFirstReplacementAdvantage, oneTimeKeySwitchZeroGame,
    Circular.continuationBootstrapReplacementAdvantage,
    Circular.continuationKeySwitchFirstReplacementAdvantage,
    Circular.continuationKeySwitchReplacementAdvantage] using h

/-- Conversely, the alternative KSK-first intact-cycle term is no larger than the original
BRK-first term plus the two post-cut edges. -/
theorem keySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        Encryption.keySwitchReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        oneTimeCutBootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary := by
  have h :=
    Circular.continuationKeySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
      (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (Encryption.oneTimeContinuation inputErrorSampler encode adversary)
  rw [← oneTimeCutBootstrapReplacementAdvantage_eq_abstract ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] at h
  simpa [Encryption.bootstrapReplacementAdvantage,
    Encryption.keySwitchReplacementAdvantage, Encryption.realGame,
    Encryption.bootstrapZeroGame, Encryption.zeroCloudGame,
    oneTimeKeySwitchFirstReplacementAdvantage, oneTimeKeySwitchZeroGame,
    Circular.continuationBootstrapReplacementAdvantage,
    Circular.continuationKeySwitchFirstReplacementAdvantage,
    Circular.continuationKeySwitchReplacementAdvantage] using h

/-- One-time IND-CPA specialization of the native cut-cycle theorem.  After the KSK edge has been
zeroed, contextual BRK replacement, including the adaptive TLWE challenge, follows from two
ordinary parallel binary-secret module-LWE advantages. -/
theorem oneTimeCutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneTimeCutBootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realMessageReduction ringErrorSampler
          keySwitchErrorSampler tgswGadget
          (oneTimeContinuation inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroMessageReduction ringErrorSampler
          keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) := by
  exact Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    ringErrorSampler keySwitchErrorSampler tgswGadget
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- Conventional single-batch form of the adaptive cut-cycle theorem. -/
theorem oneTimeCutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneTimeCutBootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
          keySwitchErrorSampler tgswGadget
          (oneTimeContinuation inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
          keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) := by
  exact Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    ringErrorSampler keySwitchErrorSampler tgswGadget
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- The KSK-first intact-cycle assumption is implied, up to checked post-cut LWE terms, by the
existing direct-bilinear BRK-first assumption. -/
theorem keySwitchFirstReplacementAdvantage_le_directBilinear_add_postCutLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      Native.BootstrapSecurity.directBilinearAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget
          (Encryption.oneTimeContinuation inputErrorSampler encode adversary) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realMessageReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroMessageReduction ringErrorSampler
            keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Encryption.Security.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (Encryption.Security.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget
            (Encryption.Security.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        LearningWithErrors.advantage
          (Encryption.Security.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (Encryption.Security.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have hRelation := keySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCut := oneTimeCutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary
  have hKeySwitch := Encryption.Security.keySwitchReplacementAdvantage_le_two_jointLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  rw [Encryption.Security.bootstrapReplacementAdvantage_eq_directBilinear
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary] at hRelation
  linarith

/-- Conversely, the direct-bilinear BRK-first assumption is implied, up to the same checked
post-cut LWE terms, by the KSK-first intact-cycle assumption. -/
theorem directBilinearAdvantage_le_keySwitchFirst_add_postCutLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Native.BootstrapSecurity.directBilinearAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget
        (Encryption.oneTimeContinuation inputErrorSampler encode adversary) ≤
      oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realMessageReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroMessageReduction ringErrorSampler
            keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Encryption.Security.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (Encryption.Security.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget
            (Encryption.Security.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        LearningWithErrors.advantage
          (Encryption.Security.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (Encryption.Security.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have hRelation := bootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCut := oneTimeCutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary
  have hKeySwitch := Encryption.Security.keySwitchReplacementAdvantage_le_two_jointLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  rw [Encryption.Security.bootstrapReplacementAdvantage_eq_directBilinear
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary] at hRelation
  linarith

/-- **Alternative-order native TFHE one-time security theorem.** The honest advantage is bounded
by one intact-cycle KSK-first term, two post-cut parallel module-LWE terms, and the checked
zero-cloud joint-LWE term.  Thus every term except the explicitly named first hop is reduced to
ordinary LWE/module-LWE. -/
theorem abs_signedAdvantage_real_le_keySwitchFirst_add_two_parallelModuleLwe_add_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realMessageReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroMessageReduction ringErrorSampler
            keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Encryption.Security.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (Encryption.Security.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have hOuter := Encryption.abs_signedAdvantage_real_le_circular_add_zero
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCircular := circularAdvantage_le_keySwitchFirst_add_cutBootstrap
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCut := oneTimeCutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary
  have hZero := Encryption.Security.abs_signedAdvantage_zeroCloud_eq_jointLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  rw [hZero] at hOuter
  linarith

/-- Strongest conventional-batch form of the alternative-order one-time theorem.  Each post-cut
BRK reduction now consumes one standard binary-secret ring batch of exactly
`lweDimension * TGSW.rowCount` samples. -/
theorem abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
            keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Encryption.Security.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (Encryption.Security.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have h := abs_signedAdvantage_real_le_keySwitchFirst_add_two_parallelModuleLwe_add_jointLwe
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  rw [Native.BootstrapCutSecurity.realMessageReduction_advantage_eq_batch,
    Native.BootstrapCutSecurity.zeroMessageReduction_advantage_eq_batch] at h
  exact h

/-- Equal-noise specialization in which every non-circular term is a conventional batch-LWE
advantage: two binary-secret ring batches for the post-cut BRK hop and one binary-secret scalar
batch containing all KSK rows plus the adaptive challenge row. -/
theorem abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_batchLwe_of_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
            errorSampler tgswGadget (oneTimeContinuation errorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
            errorSampler (oneTimeContinuation errorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + 1)
            errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Security.zeroCloudReduction ringErrorSampler errorSampler errorSampler
              tgswGadget encode adversary)) := by
  have hOuter := Encryption.abs_signedAdvantage_real_le_circular_add_zero
    ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget encode adversary
  have hCircular := circularAdvantage_le_keySwitchFirst_add_cutBootstrap
    ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget encode adversary
  have hCut := oneTimeCutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    ringErrorSampler errorSampler errorSampler tgswGadget encode adversary
  have hZero := Encryption.Security.abs_signedAdvantage_zeroCloud_eq_batchLwe_of_same_noise
    ringErrorSampler errorSampler tgswGadget keySwitchGadget encode adversary
  rw [hZero] at hOuter
  linarith

/-- The exact scheme-specific circular/KDM premise left by the native TFHE proof.  It compares a
real cloud key with the hybrid in which the KSK messages are zero while the real structured BRK,
the shared scalar key, and the complete adaptive challenge continuation remain visible.

The ACPS, Brakerski--Vaikuntanathan, and Brakerski--Goldwasser--Kalai results establish KDM
security for their own modified schemes; they do not discharge this native-TFHE predicate. -/
def NativeIntactCycleKDMHardAgainst
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤ bound

/-- A generic fixed-hint KSK-first circular/KDM assumption for the native cycle implies its exact
adaptive one-time specialization whenever the selected adversary class induces allowed
continuations. -/
theorem nativeIntactCycleKDMHardAgainst_of_continuation
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (continuationAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (bound : ℝ)
    (hClosed : ∀ adversary, allowed adversary →
      continuationAllowed (Encryption.oneTimeContinuation inputErrorSampler encode adversary))
    (hCircular : Circular.KeySwitchFirstHardAgainst
      (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      continuationAllowed bound) :
    NativeIntactCycleKDMHardAgainst ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode allowed bound := by
  intro adversary hadversary
  rw [oneTimeKeySwitchFirstReplacementAdvantage_eq_abstract]
  exact hCircular _ (hClosed adversary hadversary)

/-- **Paper-aligned conditional TFHE security theorem.**  Native intact-cycle fixed-hint KDM
security, two conventional post-cut binary-secret ring batch-LWE assumptions, and the exact
zero-cloud joint binary-LWE assumption imply adaptive one-time TFHE security for a selected
adversary class.  Every non-circular premise names an ordinary concrete LWE problem and its
reduction; the native circular premise is not silently identified with the KDM security of a
different construction. -/
theorem oneTimeHardAgainst_of_nativeIntactCycleKDM_and_batchLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (realBatchAllowed zeroBatchAllowed : LearningWithErrors.Adversary
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) → Prop)
    (jointLweAllowed : LearningWithErrors.Adversary
      (Encryption.Security.jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler) → Prop)
    (intactCycleBound realBatchBound zeroBatchBound jointLweBound : ℝ)
    (hRealBatchClosed : ∀ adversary, allowed adversary →
      realBatchAllowed
        (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
          keySwitchErrorSampler tgswGadget
          (oneTimeContinuation inputErrorSampler encode adversary)))
    (hZeroBatchClosed : ∀ adversary, allowed adversary →
      zeroBatchAllowed
        (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
          keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)))
    (hJointLweClosed : ∀ adversary, allowed adversary →
      jointLweAllowed
        (Encryption.Security.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary))
    (hIntactCycle : NativeIntactCycleKDMHardAgainst ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode allowed intactCycleBound)
    (hRealBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) realBatchAllowed realBatchBound)
    (hZeroBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) zeroBatchAllowed zeroBatchBound)
    (hJointLwe : FormalProof4FHE.LWE.HardAgainst
      (Encryption.Security.jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler) jointLweAllowed jointLweBound) :
    Encryption.Security.OneTimeHardAgainst ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode allowed
      (intactCycleBound + realBatchBound + zeroBatchBound + jointLweBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
              lweDimension ringErrorSampler)
            (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
              keySwitchErrorSampler tgswGadget
              (oneTimeContinuation inputErrorSampler encode adversary)) +
          LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
              lweDimension ringErrorSampler)
            (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
              keySwitchErrorSampler (oneTimeContinuation inputErrorSampler encode adversary)) +
          LearningWithErrors.advantage
            (Encryption.Security.jointLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
              keySwitchErrorSampler inputErrorSampler)
            (Encryption.Security.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
              inputErrorSampler tgswGadget encode adversary) :=
      abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary
    _ ≤ intactCycleBound + realBatchBound + zeroBatchBound + jointLweBound :=
      add_le_add
        (add_le_add
          (add_le_add (hIntactCycle adversary hadversary)
            (hRealBatch _ (hRealBatchClosed adversary hadversary)))
          (hZeroBatch _ (hZeroBatchClosed adversary hadversary)))
        (hJointLwe _ (hJointLweClosed adversary hadversary))

/-- Equal-noise adversary-class specialization of the paper-aligned conditional theorem.  Apart
from `NativeIntactCycleKDMHardAgainst`, all computational premises are ordinary binary-secret
batch LWE: two ring batches of `lweDimension * TGSW.rowCount` samples and one scalar batch of
`keySwitchSamples + 1` samples. -/
theorem oneTimeHardAgainst_of_nativeIntactCycleKDM_and_standardBatchLwe_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (realRingBatchAllowed zeroRingBatchAllowed : LearningWithErrors.Adversary
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) → Prop)
    (scalarBatchAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + 1)
        errorSampler) → Prop)
    (intactCycleBound realRingBatchBound zeroRingBatchBound scalarBatchBound : ℝ)
    (hRealRingBatchClosed : ∀ adversary, allowed adversary →
      realRingBatchAllowed
        (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler errorSampler
          tgswGadget (oneTimeContinuation errorSampler encode adversary)))
    (hZeroRingBatchClosed : ∀ adversary, allowed adversary →
      zeroRingBatchAllowed
        (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler errorSampler
          (oneTimeContinuation errorSampler encode adversary)))
    (hScalarBatchClosed : ∀ adversary, allowed adversary →
      scalarBatchAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (Encryption.Security.zeroCloudReduction ringErrorSampler errorSampler errorSampler
            tgswGadget encode adversary)))
    (hIntactCycle : NativeIntactCycleKDMHardAgainst ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed intactCycleBound)
    (hRealRingBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) realRingBatchAllowed realRingBatchBound)
    (hZeroRingBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) zeroRingBatchAllowed zeroRingBatchBound)
    (hScalarBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + 1)
        errorSampler) scalarBatchAllowed scalarBatchBound) :
    Encryption.Security.OneTimeHardAgainst ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed
      (intactCycleBound + realRingBatchBound + zeroRingBatchBound + scalarBatchBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (Encryption.realGame ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        oneTimeKeySwitchFirstReplacementAdvantage ringErrorSampler errorSampler errorSampler
            tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
              lweDimension ringErrorSampler)
            (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler errorSampler
              tgswGadget (oneTimeContinuation errorSampler encode adversary)) +
          LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
              lweDimension ringErrorSampler)
            (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler errorSampler
              (oneTimeContinuation errorSampler encode adversary)) +
          LearningWithErrors.advantage
            (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + 1)
              errorSampler)
            (FormalProof4FHE.LWE.TwoBlock.reduction
              (Encryption.Security.zeroCloudReduction ringErrorSampler errorSampler errorSampler
                tgswGadget encode adversary)) :=
      abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_batchLwe_of_same_noise
        ringErrorSampler errorSampler tgswGadget keySwitchGadget encode adversary
    _ ≤ intactCycleBound + realRingBatchBound + zeroRingBatchBound + scalarBatchBound :=
      add_le_add
        (add_le_add
          (add_le_add (hIntactCycle adversary hadversary)
            (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
          (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
        (hScalarBatch _ (hScalarBatchClosed adversary hadversary))

end FormalProof4FHE.TFHE.Encryption.CutCycleSecurity
