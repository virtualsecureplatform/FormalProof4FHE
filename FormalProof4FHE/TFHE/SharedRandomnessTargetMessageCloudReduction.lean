/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageSecurity
import FormalProof4FHE.TFHE.CutCycleSecurity

set_option autoImplicit false

/-!
# Ordinary Module-LWE Reduction for the Acyclic Target-Message Cloud View

After the source-prefix coordinates of the target message vector have been replaced by zero, the
remaining public ring rows have an acyclic dependency graph:

* the source BRK encrypts only coefficients of the independent suffix secret under the source
  ring secret; and
* the ring-extension table encrypts gadget multiples of that same suffix secret under the source
  ring secret.

For equal ring-error samplers, both objects are one ordinary same-secret module-LWE transcript.
This file checks that statement without giving the reduction the source secret.  It also proves
that the real-message and zero-message reductions have the same uniform endpoint, so the
cloud-only suffix replacement is bounded by two ordinary module-LWE advantages.

The adaptive target-key input tape is intentionally not included here.  Its scalar rows require
the separate joint sample-extraction simulator formalized in the next layer.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.CloudReduction

noncomputable section

@[simp]
theorem embedConstantBit_false (q degree : ℕ) [NeZero q] :
    embedConstantBit q degree false = 0 := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  simp [embedConstantBit, embedBinaryPolynomial, embedBit,
    LatticeCrypto.Poly.ofPi, Vector.get]
  change (0 : ZMod q) =
    (RLWE.negacyclicRing q degree).backend.coeff
      (RLWE.negacyclicRing q degree).zero coefficient
  exact (LatticeCrypto.NegacyclicRing.coeff_zero
    (RLWE.negacyclicRing q degree) coefficient).symm

/-- The zero chosen through the proof-facing semiring dictionary used by `TGSW.addGadget`. -/
noncomputable def semiringRqZero (q degree : ℕ) : RLWE.Rq q degree :=
  @OfNat.ofNat (RLWE.Rq q degree) 0
    (@Zero.toOfNat0 (RLWE.Rq q degree)
      (@MulZeroClass.toZero (RLWE.Rq q degree)
        (@instMulZeroClassOfSemiring (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toSemiring)))

/-- The proof-facing and executable zero polynomials are extensionally equal. -/
theorem semiringRqZero_eq_zero (q degree : ℕ) : semiringRqZero q degree = 0 := by
  cases degree with
  | zero =>
      apply LatticeCrypto.NegacyclicRing.poly_ext
      intro coefficient
      exact coefficient.elim0
  | succ degree => rfl

@[simp]
theorem addGadget_embedConstantBit_false
    {q degree dimension levels : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q degree)
    (homogeneous : TGSW.Ciphertext (RLWE.Rq q degree) dimension levels) :
    TGSW.addGadget gadget (embedConstantBit q degree false) homogeneous = homogeneous := by
  rw [embedConstantBit_false, ← semiringRqZero_eq_zero]
  simpa only [semiringRqZero] using TGSW.addGadget_zero gadget homogeneous

@[simp]
theorem addGadget_executable_zero
    {q degree dimension levels : ℕ}
    (gadget : Fin levels → RLWE.Rq q degree)
    (homogeneous : TGSW.Ciphertext (RLWE.Rq q degree) dimension levels) :
    TGSW.addGadget gadget (0 : RLWE.Rq q degree) homogeneous = homogeneous := by
  rw [← semiringRqZero_eq_zero]
  simpa only [semiringRqZero] using TGSW.addGadget_zero gadget homogeneous

abbrev BootstrapChallenge
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Native.BootstrapCutSecurity.ParallelChallenge (RLWE.Rq q degree) sourceRank
    tgswLevels (targetScalarDimension sourceRank suffixRank degree)

abbrev BootstrapOutput
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Native.BootstrapCutSecurity.ParallelOutput (RLWE.Rq q degree) sourceRank
    tgswLevels (targetScalarDimension sourceRank suffixRank degree)

abbrev ExtensionChallenge
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Matrix (Fin sourceRank) (Fin (suffixRank * tgswLevels)) (RLWE.Rq q degree)

abbrev ExtensionOutput
    (q degree suffixRank tgswLevels : ℕ) :=
  Fin (suffixRank * tgswLevels) → RLWE.Rq q degree

/-- Public matrices for the source BRK rows and the ring-extension rows. -/
abbrev Challenge
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  BootstrapChallenge q degree sourceRank suffixRank tgswLevels ×
    ExtensionChallenge q degree sourceRank suffixRank tgswLevels

/-- Right-hand sides for the source BRK rows and the ring-extension rows. -/
abbrev Output
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  BootstrapOutput q degree sourceRank suffixRank tgswLevels ×
    ExtensionOutput q degree suffixRank tgswLevels

/-- The complete two-block public module-LWE transcript. -/
abbrev Transcript
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  Challenge q degree sourceRank suffixRank tgswLevels ×
    Output q degree sourceRank suffixRank tgswLevels

/-- Regroup `(BRK challenge, extension challenge, BRK output, extension output)` into two
ordinary challenge/output transcript pairs. -/
def regroupEquiv
    (q degree sourceRank suffixRank tgswLevels : ℕ) :
    Transcript q degree sourceRank suffixRank tgswLevels ≃
      Native.BootstrapCutSecurity.ParallelTranscript (RLWE.Rq q degree) sourceRank
          tgswLevels (targetScalarDimension sourceRank suffixRank degree) ×
        TLWE.BatchCiphertext (RLWE.Rq q degree) sourceRank
          (suffixRank * tgswLevels) where
  toFun transcript :=
    ((transcript.1.1, transcript.2.1), (transcript.1.2, transcript.2.2))
  invFun transcripts :=
    ((transcripts.1.1, transcripts.2.1), (transcripts.1.2, transcripts.2.2))
  left_inv transcript := by
    rcases transcript with ⟨⟨firstChallenge, secondChallenge⟩,
      firstOutput, secondOutput⟩
    rfl
  right_inv transcripts := by
    rcases transcripts with ⟨⟨firstChallenge, firstOutput⟩,
      secondChallenge, secondOutput⟩
    rfl

/-- Add a fixed native TGSW message vector to a parallel homogeneous source-BRK transcript. -/
def bootstrappingKeyEquiv
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (messages : BinarySecret (targetScalarDimension sourceRank suffixRank degree)) :
    Native.BootstrapCutSecurity.ParallelTranscript (RLWE.Rq q degree) sourceRank
        tgswLevels (targetScalarDimension sourceRank suffixRank degree) ≃
      SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels where
  toFun transcript :=
    Native.BootstrapCutSecurity.transcriptToBootstrappingKey
      (Native.BootstrapCutSecurity.shiftTranscript gadget
        (fun coordinate ↦ embedConstantBit q degree (messages coordinate)) transcript)
  invFun key :=
    Native.BootstrapCutSecurity.unshiftTranscript gadget
      (fun coordinate ↦ embedConstantBit q degree (messages coordinate))
      (Native.BootstrapCutSecurity.bootstrappingKeyToTranscript key)
  left_inv transcript := by
    change Native.BootstrapCutSecurity.unshiftTranscript gadget
        (fun coordinate ↦ embedConstantBit q degree (messages coordinate))
        (Native.BootstrapCutSecurity.bootstrappingKeyToTranscript
          (Native.BootstrapCutSecurity.transcriptToBootstrappingKey
            (Native.BootstrapCutSecurity.shiftTranscript gadget
              (fun coordinate ↦ embedConstantBit q degree (messages coordinate))
              transcript))) = transcript
    rw [Native.BootstrapCutSecurity.bootstrappingKeyToTranscript_transcriptToBootstrappingKey]
    exact Native.BootstrapCutSecurity.unshiftTranscript_shiftTranscript gadget
      (fun coordinate ↦ embedConstantBit q degree (messages coordinate)) transcript
  right_inv key := by
    simp

/-- Add the fixed extension-message vector to homogeneous ring-TLWE rows. -/
def extensionKeyEquiv
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (message : ExtensionOutput q degree suffixRank tgswLevels) :
    TLWE.BatchCiphertext (RLWE.Rq q degree) sourceRank (suffixRank * tgswLevels) ≃
      RingExtensionKey q degree sourceRank suffixRank tgswLevels where
  toFun transcript := (transcript.1, transcript.2 + message)
  invFun transcript := (transcript.1, transcript.2 - message)
  left_inv transcript := by
    rcases transcript with ⟨challenge, output⟩
    apply Prod.ext
    · rfl
    · change output + message - message = output
      funext row
      change output row + message row - message row = output row
      exact @add_sub_cancel_right (RLWE.Rq q degree)
        (LatticeCrypto.NegacyclicRing.instAddCommGroupPoly
          (RLWE.negacyclicRing q degree)).toAddGroup
        (output row) (message row)
  right_inv transcript := by
    rcases transcript with ⟨challenge, output⟩
    apply Prod.ext
    · rfl
    · change output - message + message = output
      funext row
      change output row - message row + message row = output row
      exact @sub_add_cancel (RLWE.Rq q degree)
        (LatticeCrypto.NegacyclicRing.instAddCommGroupPoly
          (RLWE.negacyclicRing q degree)).toAddGroup
        (output row) (message row)

/-- For fixed suffix data, the complete homogeneous module-LWE transcript is in public bijection
with the concrete source BRK plus ring-extension table. -/
def cloudViewEquiv
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (messages : BinarySecret (targetScalarDimension sourceRank suffixRank degree))
    (extensionMessage : ExtensionOutput q degree suffixRank tgswLevels) :
    Transcript q degree sourceRank suffixRank tgswLevels ≃
      SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
        RingExtensionKey q degree sourceRank suffixRank tgswLevels :=
  (regroupEquiv q degree sourceRank suffixRank tgswLevels).trans
    ((bootstrappingKeyEquiv q degree sourceRank suffixRank tgswLevels gadget messages).prodCongr
      (extensionKeyEquiv q degree sourceRank suffixRank tgswLevels extensionMessage))

/-- Concrete coordinate form of the BRK transcript equivalence. -/
theorem bootstrappingKeyEquiv_apply
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (messages : BinarySecret (targetScalarDimension sourceRank suffixRank degree))
    (transcript : Native.BootstrapCutSecurity.ParallelTranscript
      (RLWE.Rq q degree) sourceRank tgswLevels
      (targetScalarDimension sourceRank suffixRank degree)) :
    bootstrappingKeyEquiv q degree sourceRank suffixRank tgswLevels gadget messages
        transcript =
      fun coordinate ↦ TGSW.addGadget gadget
        (embedConstantBit q degree (messages coordinate))
        (Native.BootstrapCutSecurity.transcriptToBootstrappingKey transcript coordinate) := by
  exact Native.BootstrapCutSecurity.transcriptToBootstrappingKey_shiftTranscript
    gadget (fun coordinate ↦ embedConstantBit q degree (messages coordinate)) transcript

/-- The addition dictionary selected by generic `Semiring`-parametric TLWE assembly. -/
@[reducible] noncomputable def tlweRqAdd (q degree : ℕ) : Add (RLWE.Rq q degree) :=
  @Distrib.toAdd (RLWE.Rq q degree)
    (@instDistribOfSemiring (RLWE.Rq q degree)
      (@CommSemiring.toSemiring (RLWE.Rq q degree)
        (@CommRing.toCommSemiring (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree))))

/-- Generic TLWE addition and the bundled executable ring addition compute identically. -/
theorem tlweRqAdd_apply (q degree : ℕ) (left right : RLWE.Rq q degree) :
    @Add.add (RLWE.Rq q degree) (tlweRqAdd q degree) left right = left + right := by
  exact FormalProof4FHE.RLWE.RingRegev.semiringRqAdd_apply q degree left right

/-- Adding the extension message to a homogeneous transcript is the native batch assembler. -/
theorem extensionKeyEquiv_real
    (q degree sourceRank suffixRank tgswLevels : ℕ)
    (sourceSecret : Fin sourceRank → RLWE.Rq q degree)
    (challenge : ExtensionChallenge q degree sourceRank suffixRank tgswLevels)
    (error message : ExtensionOutput q degree suffixRank tgswLevels) :
    extensionKeyEquiv q degree sourceRank suffixRank tgswLevels message
        (challenge, vecMul sourceSecret challenge + error) =
      TLWE.batchAssemble sourceSecret challenge message error := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [extensionKeyEquiv, Equiv.coe_fn_mk, TLWE.batchAssemble,
      Pi.add_apply]
    simp only [← tlweRqAdd_apply]
    change
      @Add.add (RLWE.Rq q degree) (tlweRqAdd q degree)
          (@Add.add (RLWE.Rq q degree) (tlweRqAdd q degree)
            ((vecMul sourceSecret challenge) row) (error row)) (message row) =
        @Add.add (RLWE.Rq q degree) (tlweRqAdd q degree)
          (@Add.add (RLWE.Rq q degree) (tlweRqAdd q degree)
            ((vecMul sourceSecret challenge) row) (message row)) (error row)
    simp only [tlweRqAdd_apply]
    exact @add_right_comm (RLWE.Rq q degree)
      (LatticeCrypto.NegacyclicRing.instAddCommGroupPoly
        (RLWE.negacyclicRing q degree)).toAddCommSemigroup
      ((vecMul sourceSecret challenge) row) (error row) (message row)

/-- Ordinary two-block module-LWE for every BRK row and every extension row under one source
ring secret.  The two blocks use the same error sampler in this exact flattening. -/
def problem
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    LearningWithErrors.Problem
      (Challenge q degree sourceRank suffixRank tgswLevels)
      (RingBinarySecret sourceRank degree)
      (Output q degree sourceRank suffixRank tgswLevels) where
  sampleChallenge := $ᵗ (Challenge q degree sourceRank suffixRank tgswLevels)
  sampleSecret := Native.sampleRingSecret sourceRank degree
  sampleError := do
    let bootstrapError ← Fin.mOfFn
      (targetScalarDimension sourceRank suffixRank degree) fun _ ↦
        ProbComp.sampleIID (TGSW.rowCount sourceRank tgswLevels) errorSampler
    let extensionError ←
      ProbComp.sampleIID (suffixRank * tgswLevels) errorSampler
    return (bootstrapError, extensionError)
  noiseless := fun sourceSecret challenge ↦
    (fun coordinate ↦
      vecMul (embedRingSecret q sourceSecret) (challenge.1 coordinate),
      vecMul (embedRingSecret q sourceSecret) challenge.2)
  sampleUniform := $ᵗ (Output q degree sourceRank suffixRank tgswLevels)

/-- A public continuation sees the two source-ring evaluation-key components but no hidden
secret. -/
abbrev PublicContinuation
    (q degree sourceRank suffixRank tgswLevels : ℕ) :=
  SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels →
    RingExtensionKey q degree sourceRank suffixRank tgswLevels → ProbComp Bool

/-- Cloud-only suffix-message experiment. -/
def suffixOnlyGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let bootstrappingKey ← generateSuffixOnlySourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels errorSampler gadget sourceSecret suffixSecret
  let extensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels errorSampler gadget sourceSecret suffixSecret
  continuation bootstrappingKey extensionKey

/-- Cloud-only comparison after replacing the remaining suffix BRK messages by zero. -/
def zeroGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    ProbComp Bool := do
  let sourceSecret ← Native.sampleRingSecret sourceRank degree
  let suffixSecret ← Native.sampleRingSecret suffixRank degree
  let bootstrappingKey ← generateZeroSourceBootstrappingKey q degree sourceRank
    suffixRank tgswLevels errorSampler gadget sourceSecret
  let extensionKey ← generateRingExtensionKey q degree sourceRank suffixRank
    tgswLevels errorSampler gadget sourceSecret suffixSecret
  continuation bootstrappingKey extensionKey

/-- Ordinary module-LWE reduction for the suffix-only source BRK branch. -/
def suffixReduction
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q degree)}
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    LearningWithErrors.Adversary
      (problem q degree sourceRank suffixRank tgswLevels errorSampler) :=
  fun transcript ↦ do
    let suffixSecret ← Native.sampleRingSecret suffixRank degree
    let view := cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
      (suffixOnlyMessages suffixSecret)
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q degree suffixRank tgswLevels gadget suffixSecret) transcript
    continuation view.1 view.2

/-- Ordinary module-LWE reduction for the zero-message source BRK branch. -/
def zeroReduction
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    {errorSampler : ProbComp (RLWE.Rq q degree)}
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    LearningWithErrors.Adversary
      (problem q degree sourceRank suffixRank tgswLevels errorSampler) :=
  fun transcript ↦ do
    let suffixSecret ← Native.sampleRingSecret suffixRank degree
    let view := cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
      (fun _ ↦ false)
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q degree suffixRank tgswLevels gadget suffixSecret) transcript
    continuation view.1 view.2

/-- Common fully uniform cloud endpoint of both ordinary module-LWE reductions. -/
def uniformGame
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    ProbComp Bool := do
  let view ← $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
    RingExtensionKey q degree sourceRank suffixRank tgswLevels)
  continuation view.1 view.2

/-- Replace the BRK supplied to a public continuation by an independently uniform BRK while
retaining the supplied ring-extension table.  This is the intermediate endpoint needed to
compare the source-prefix reference branch with its uniform-BRK branch without revealing the
source ring secret. -/
def resampleBootstrapContinuation
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    PublicContinuation q degree sourceRank suffixRank tgswLevels :=
  fun _ extensionKey ↦ do
    let bootstrappingKey ←
      $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels)
    continuation bootstrappingKey extensionKey

/-- Resampling an unused BRK inside a completely uniform cloud view does not change its law.
Both sides supply one independent uniform BRK and one independent uniform extension table to the
same public continuation. -/
theorem uniformGame_resampleBootstrapContinuation_evalDist
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    evalDist (uniformGame q degree sourceRank suffixRank tgswLevels
        (resampleBootstrapContinuation continuation)) =
      evalDist (uniformGame q degree sourceRank suffixRank tgswLevels continuation) := by
  let BootstrappingKey :=
    SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels
  let ExtensionKey := RingExtensionKey q degree sourceRank suffixRank tgswLevels
  let views : ProbComp (BootstrappingKey × ExtensionKey) :=
    $ᵗ (BootstrappingKey × ExtensionKey)
  let bootstrappingKeys : ProbComp BootstrappingKey := $ᵗ BootstrappingKey
  let extensionKeys : ProbComp ExtensionKey := $ᵗ ExtensionKey
  have uniformProduct :
      views = Prod.mk <$> bootstrappingKeys <*> extensionKeys := rfl
  unfold uniformGame resampleBootstrapContinuation
  change evalDist (views >>= fun view ↦
      bootstrappingKeys >>= fun bootstrappingKey ↦
      continuation bootstrappingKey view.2) =
    evalDist (views >>= fun view ↦ continuation view.1 view.2)
  rw [uniformProduct]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  calc
    _ = evalDist (extensionKeys >>= fun extensionKey ↦
          bootstrappingKeys >>= fun bootstrappingKey ↦
          continuation bootstrappingKey extensionKey) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        bootstrappingKeys (by simp [bootstrappingKeys]) _
    _ = evalDist (bootstrappingKeys >>= fun bootstrappingKey ↦
          extensionKeys >>= fun extensionKey ↦
          continuation bootstrappingKey extensionKey) :=
      (evalDist_bind_bind_swap bootstrappingKeys extensionKeys
        (fun bootstrappingKey extensionKey ↦
          continuation bootstrappingKey extensionKey)).symm

/-- The explicitly blocked uniform branch of `problem` is the canonical uniform transcript
sampler. -/
theorem problem_uniformDistr_eq_uniformSample
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree)) :
    LearningWithErrors.uniformDistr
        (problem q degree sourceRank suffixRank tgswLevels errorSampler) =
      ($ᵗ (Transcript q degree sourceRank suffixRank tgswLevels)) := by
  unfold LearningWithErrors.uniformDistr problem
  have uniformProduct :
      ($ᵗ (Transcript q degree sourceRank suffixRank tgswLevels) :
        ProbComp (Transcript q degree sourceRank suffixRank tgswLevels)) =
      Prod.mk <$>
        ($ᵗ (Challenge q degree sourceRank suffixRank tgswLevels)) <*>
        ($ᵗ (Output q degree sourceRank suffixRank tgswLevels)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- Every fixed-message cloud conversion maps a uniform homogeneous transcript to a uniform
concrete BRK-plus-extension view. -/
theorem cloudViewEquiv_uniform_evalDist
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (messages : BinarySecret (targetScalarDimension sourceRank suffixRank degree))
    (extensionMessage : ExtensionOutput q degree suffixRank tgswLevels) :
    evalDist (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
        messages extensionMessage <$>
      ($ᵗ (Transcript q degree sourceRank suffixRank tgswLevels))) =
      evalDist ($ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
        RingExtensionKey q degree sourceRank suffixRank tgswLevels)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Transcript q degree sourceRank suffixRank tgswLevels)
    (β := SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
      RingExtensionKey q degree sourceRank suffixRank tgswLevels)
    (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
      messages extensionMessage)
    (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
      messages extensionMessage).bijective

/-- The suffix-message reduction's module-LWE uniform branch is the common uniform cloud game. -/
theorem suffixReduction_game1_evalDist_eq_uniform
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    evalDist (LearningWithErrors.game1
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (suffixReduction gadget continuation)) =
      evalDist (uniformGame q degree sourceRank suffixRank tgswLevels continuation) := by
  rw [LearningWithErrors.game1,
    problem_uniformDistr_eq_uniformSample q degree sourceRank suffixRank tgswLevels]
  let transcripts : ProbComp (Transcript q degree sourceRank suffixRank tgswLevels) :=
    $ᵗ (Transcript q degree sourceRank suffixRank tgswLevels)
  let suffixes := Native.sampleRingSecret suffixRank degree
  let views : ProbComp
      (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
        RingExtensionKey q degree sourceRank suffixRank tgswLevels) :=
    $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
      RingExtensionKey q degree sourceRank suffixRank tgswLevels)
  let finish := fun
      (view : SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
        RingExtensionKey q degree sourceRank suffixRank tgswLevels) ↦
    continuation view.1 view.2
  calc
    evalDist (transcripts >>= suffixReduction gadget continuation) =
        evalDist (suffixes >>= fun suffixSecret ↦
          transcripts >>= fun transcript ↦
          finish (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
            (suffixOnlyMessages suffixSecret)
            (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
              q degree suffixRank tgswLevels gadget suffixSecret) transcript)) := by
      simpa [transcripts, suffixes, finish, suffixReduction] using
        (evalDist_bind_bind_swap transcripts suffixes
          (fun transcript suffixSecret ↦
            finish (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
              (suffixOnlyMessages suffixSecret)
              (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
                q degree suffixRank tgswLevels gadget suffixSecret) transcript)))
    _ = evalDist (suffixes >>= fun _ ↦ views >>= finish) := by
      refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
      simpa [transcripts, views, map_eq_bind_pure_comp, bind_assoc] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (cloudViewEquiv_uniform_evalDist q degree sourceRank suffixRank tgswLevels gadget
            (suffixOnlyMessages suffixSecret)
            (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
              q degree suffixRank tgswLevels gadget suffixSecret)) finish)
    _ = evalDist (views >>= finish) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        suffixes (by simp [suffixes]) (views >>= finish)
    _ = evalDist (uniformGame q degree sourceRank suffixRank tgswLevels continuation) := by
      simp [uniformGame, views, finish]

/-- The zero-message reduction has the identical module-LWE uniform endpoint. -/
theorem zeroReduction_game1_evalDist_eq_uniform
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    evalDist (LearningWithErrors.game1
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (zeroReduction gadget continuation)) =
      evalDist (uniformGame q degree sourceRank suffixRank tgswLevels continuation) := by
  rw [LearningWithErrors.game1,
    problem_uniformDistr_eq_uniformSample q degree sourceRank suffixRank tgswLevels]
  let transcripts : ProbComp (Transcript q degree sourceRank suffixRank tgswLevels) :=
    $ᵗ (Transcript q degree sourceRank suffixRank tgswLevels)
  let suffixes := Native.sampleRingSecret suffixRank degree
  let views : ProbComp
      (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
        RingExtensionKey q degree sourceRank suffixRank tgswLevels) :=
    $ᵗ (SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
      RingExtensionKey q degree sourceRank suffixRank tgswLevels)
  let finish := fun
      (view : SourceBootstrappingKey q degree sourceRank suffixRank tgswLevels ×
        RingExtensionKey q degree sourceRank suffixRank tgswLevels) ↦
    continuation view.1 view.2
  calc
    evalDist (transcripts >>= zeroReduction gadget continuation) =
        evalDist (suffixes >>= fun suffixSecret ↦
          transcripts >>= fun transcript ↦
          finish (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
            (fun _ ↦ false)
            (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
              q degree suffixRank tgswLevels gadget suffixSecret) transcript)) := by
      simpa [transcripts, suffixes, finish, zeroReduction] using
        (evalDist_bind_bind_swap transcripts suffixes
          (fun transcript suffixSecret ↦
            finish (cloudViewEquiv q degree sourceRank suffixRank tgswLevels gadget
              (fun _ ↦ false)
              (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
                q degree suffixRank tgswLevels gadget suffixSecret) transcript)))
    _ = evalDist (suffixes >>= fun _ ↦ views >>= finish) := by
      refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
      simpa [transcripts, views, map_eq_bind_pure_comp, bind_assoc] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          (cloudViewEquiv_uniform_evalDist q degree sourceRank suffixRank tgswLevels gadget
            (fun _ ↦ false)
            (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
              q degree suffixRank tgswLevels gadget suffixSecret)) finish)
    _ = evalDist (views >>= finish) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        suffixes (by simp [suffixes]) (views >>= finish)
    _ = evalDist (uniformGame q degree sourceRank suffixRank tgswLevels continuation) := by
      simp [uniformGame, views, finish]

/-! ## Exact real-branch simulations -/

/-- The cloud-only suffix-message game is exactly the real branch of its ordinary module-LWE
reduction. -/
theorem suffixOnlyGame_evalDist_eq_game0
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    evalDist (suffixOnlyGame q degree sourceRank suffixRank tgswLevels
        errorSampler gadget continuation) =
      evalDist (LearningWithErrors.game0
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (suffixReduction gadget continuation)) := by
  let FirstChallenge := BootstrapChallenge q degree sourceRank suffixRank tgswLevels
  let FirstError := BootstrapOutput q degree sourceRank suffixRank tgswLevels
  let SecondChallenge := ExtensionChallenge q degree sourceRank suffixRank tgswLevels
  let SecondError := ExtensionOutput q degree suffixRank tgswLevels
  let sourceSecrets := Native.sampleRingSecret sourceRank degree
  let suffixes := Native.sampleRingSecret suffixRank degree
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let nativeFirstChallenges : ProbComp FirstChallenge := Fin.mOfFn
    (targetScalarDimension sourceRank suffixRank degree) fun _ ↦
      $ᵗ Matrix (Fin sourceRank) (Fin (TGSW.rowCount sourceRank tgswLevels))
        (RLWE.Rq q degree)
  let firstErrors : ProbComp FirstError := Fin.mOfFn
    (targetScalarDimension sourceRank suffixRank degree) fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount sourceRank tgswLevels) errorSampler
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID (suffixRank * tgswLevels) errorSampler
  let finish := fun (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree)
      (firstChallenge : FirstChallenge) (firstError : FirstError)
      (secondChallenge : SecondChallenge) (secondError : SecondError) ↦
    let firstTranscript : Native.BootstrapCutSecurity.ParallelTranscript
        (RLWE.Rq q degree) sourceRank tgswLevels
        (targetScalarDimension sourceRank suffixRank degree) :=
      (firstChallenge, fun coordinate ↦
        Native.BootstrapCutSecurity.semiringRqPiAdd q degree
          (vecMul (embedRingSecret q sourceSecret) (firstChallenge coordinate))
          (firstError coordinate))
    let bootstrappingKey := fun coordinate ↦ TGSW.addGadget gadget
      (embedConstantBit q degree (suffixOnlyMessages suffixSecret coordinate))
      (Native.BootstrapCutSecurity.transcriptToBootstrappingKey
        firstTranscript coordinate)
    let extensionKey := TLWE.batchAssemble (embedRingSecret q sourceSecret)
      secondChallenge
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q degree suffixRank tgswLevels gadget suffixSecret) secondError
    continuation bootstrappingKey extensionKey
  have hFirstChallenges : evalDist nativeFirstChallenges = evalDist firstChallenges := by
    simpa [nativeFirstChallenges, firstChallenges, FirstChallenge, BootstrapChallenge,
      ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin sourceRank) (Fin (TGSW.rowCount sourceRank tgswLevels))
          (RLWE.Rq q degree))
        (targetScalarDimension sourceRank suffixRank degree))
  have nativeParallel :
      evalDist (suffixOnlyGame q degree sourceRank suffixRank tgswLevels
          errorSampler gadget continuation) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          nativeFirstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
    unfold suffixOnlyGame
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    calc
      evalDist (generateSuffixOnlySourceBootstrappingKey q degree sourceRank suffixRank
          tgswLevels errorSampler gadget sourceSecret suffixSecret >>= fun bootstrappingKey ↦
        generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
            errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
          continuation bootstrappingKey extensionKey) =
        evalDist (Native.BootstrapCutSecurity.sampleParallelRealBootstrap q degree
            sourceRank tgswLevels (targetScalarDimension sourceRank suffixRank degree)
            errorSampler gadget (suffixOnlyMessages suffixSecret) sourceSecret >>=
          fun bootstrappingKey ↦
            generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
                errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
              continuation bootstrappingKey extensionKey) := by
        simp only [generateSuffixOnlySourceBootstrappingKey]
        rw [evalDist_bind, evalDist_bind,
          Native.BootstrapCutSecurity.generateBootstrappingKey_evalDist_eq_parallel
            q degree sourceRank tgswLevels
            (targetScalarDimension sourceRank suffixRank degree) errorSampler gadget
            (suffixOnlyMessages suffixSecret) sourceSecret]
      _ = evalDist (nativeFirstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
        simp [Native.BootstrapCutSecurity.sampleParallelRealBootstrap,
          Native.BootstrapCutSecurity.sampleParallelHomogeneous,
          generateRingExtensionKey,
          FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateRingKeySwitchKey,
          TLWE.batchEncrypt, nativeFirstChallenges, firstErrors, secondChallenges,
          secondErrors, finish, FirstChallenge, FirstError, SecondChallenge, SecondError,
          Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add, bind_assoc, monad_norm]
  have nativeExpanded :
      evalDist (suffixOnlyGame q degree sourceRank suffixRank tgswLevels
          errorSampler gadget continuation) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          firstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
    rw [nativeParallel]
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hFirstChallenges (fun firstChallenge ↦
        firstErrors >>= fun firstError ↦
        secondChallenges >>= fun secondChallenge ↦
        secondErrors >>= fun secondError ↦
        finish sourceSecret suffixSecret firstChallenge firstError
          secondChallenge secondError)
  have lweExpanded :
      evalDist (LearningWithErrors.game0
          (problem q degree sourceRank suffixRank tgswLevels errorSampler)
          (suffixReduction gadget continuation)) =
        evalDist (firstChallenges >>= fun firstChallenge ↦
          secondChallenges >>= fun secondChallenge ↦
          sourceSecrets >>= fun sourceSecret ↦
          firstErrors >>= fun firstError ↦
          secondErrors >>= fun secondError ↦
          suffixes >>= fun suffixSecret ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
    have uniformChallengeProduct :
        ($ᵗ (Challenge q degree sourceRank suffixRank tgswLevels) :
          ProbComp (Challenge q degree sourceRank suffixRank tgswLevels)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    unfold LearningWithErrors.distr
    simp only [problem]
    rw [uniformChallengeProduct]
    simp [suffixReduction, cloudViewEquiv, regroupEquiv,
      bootstrappingKeyEquiv_apply, extensionKeyEquiv_real,
      sourceSecrets, suffixes, firstChallenges, firstErrors, secondChallenges,
      secondErrors, finish, FirstChallenge, FirstError, SecondChallenge, SecondError,
      Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add,
      Native.BootstrapCutSecurity.pointwiseAdd_eq_add, bind_assoc, monad_norm]
  rw [nativeExpanded, lweExpanded]
  exact Encryption.Security.evalDist_bind_six_reorder sourceSecrets suffixes
    firstChallenges firstErrors secondChallenges secondErrors finish

/-- The cloud-only zero-message game is exactly the real branch of its ordinary module-LWE
reduction. -/
theorem zeroGame_evalDist_eq_game0
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    evalDist (zeroGame q degree sourceRank suffixRank tgswLevels
        errorSampler gadget continuation) =
      evalDist (LearningWithErrors.game0
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (zeroReduction gadget continuation)) := by
  let FirstChallenge := BootstrapChallenge q degree sourceRank suffixRank tgswLevels
  let FirstError := BootstrapOutput q degree sourceRank suffixRank tgswLevels
  let SecondChallenge := ExtensionChallenge q degree sourceRank suffixRank tgswLevels
  let SecondError := ExtensionOutput q degree suffixRank tgswLevels
  let sourceSecrets := Native.sampleRingSecret sourceRank degree
  let suffixes := Native.sampleRingSecret suffixRank degree
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let nativeFirstChallenges : ProbComp FirstChallenge := Fin.mOfFn
    (targetScalarDimension sourceRank suffixRank degree) fun _ ↦
      $ᵗ Matrix (Fin sourceRank) (Fin (TGSW.rowCount sourceRank tgswLevels))
        (RLWE.Rq q degree)
  let firstErrors : ProbComp FirstError := Fin.mOfFn
    (targetScalarDimension sourceRank suffixRank degree) fun _ ↦
      ProbComp.sampleIID (TGSW.rowCount sourceRank tgswLevels) errorSampler
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID (suffixRank * tgswLevels) errorSampler
  let finish := fun (sourceSecret : RingBinarySecret sourceRank degree)
      (suffixSecret : RingBinarySecret suffixRank degree)
      (firstChallenge : FirstChallenge) (firstError : FirstError)
      (secondChallenge : SecondChallenge) (secondError : SecondError) ↦
    let firstTranscript : Native.BootstrapCutSecurity.ParallelTranscript
        (RLWE.Rq q degree) sourceRank tgswLevels
        (targetScalarDimension sourceRank suffixRank degree) :=
      (firstChallenge, fun coordinate ↦
        Native.BootstrapCutSecurity.semiringRqPiAdd q degree
          (vecMul (embedRingSecret q sourceSecret) (firstChallenge coordinate))
          (firstError coordinate))
    let bootstrappingKey :=
      Native.BootstrapCutSecurity.transcriptToBootstrappingKey firstTranscript
    let extensionKey := TLWE.batchAssemble (embedRingSecret q sourceSecret)
      secondChallenge
      (FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.ringKeySwitchMessages
        q degree suffixRank tgswLevels gadget suffixSecret) secondError
    continuation bootstrappingKey extensionKey
  have hFirstChallenges : evalDist nativeFirstChallenges = evalDist firstChallenges := by
    simpa [nativeFirstChallenges, firstChallenges, FirstChallenge, BootstrapChallenge,
      ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin sourceRank) (Fin (TGSW.rowCount sourceRank tgswLevels))
          (RLWE.Rq q degree))
        (targetScalarDimension sourceRank suffixRank degree))
  have nativeParallel :
      evalDist (zeroGame q degree sourceRank suffixRank tgswLevels
          errorSampler gadget continuation) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          nativeFirstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
    unfold zeroGame
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    calc
      evalDist (generateZeroSourceBootstrappingKey q degree sourceRank suffixRank
          tgswLevels errorSampler gadget sourceSecret >>= fun bootstrappingKey ↦
        generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
            errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
          continuation bootstrappingKey extensionKey) =
        evalDist (Native.BootstrapCutSecurity.sampleParallelZeroBootstrap q degree
            sourceRank tgswLevels (targetScalarDimension sourceRank suffixRank degree)
            errorSampler sourceSecret >>= fun bootstrappingKey ↦
          generateRingExtensionKey q degree sourceRank suffixRank tgswLevels
              errorSampler gadget sourceSecret suffixSecret >>= fun extensionKey ↦
            continuation bootstrappingKey extensionKey) := by
        simp only [generateZeroSourceBootstrappingKey]
        rw [evalDist_bind, evalDist_bind,
          Native.BootstrapCutSecurity.generateZeroBootstrappingKey_evalDist_eq_parallel
            q degree sourceRank tgswLevels
            (targetScalarDimension sourceRank suffixRank degree) errorSampler gadget
            sourceSecret]
      _ = evalDist (nativeFirstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
        simp [Native.BootstrapCutSecurity.sampleParallelZeroBootstrap,
          Native.BootstrapCutSecurity.sampleParallelHomogeneous,
          generateRingExtensionKey,
          FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.generateRingKeySwitchKey,
          TLWE.batchEncrypt, nativeFirstChallenges, firstErrors, secondChallenges,
          secondErrors, finish, FirstChallenge, FirstError, SecondChallenge, SecondError,
          Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add, bind_assoc, monad_norm]
  have nativeExpanded :
      evalDist (zeroGame q degree sourceRank suffixRank tgswLevels
          errorSampler gadget continuation) =
        evalDist (sourceSecrets >>= fun sourceSecret ↦
          suffixes >>= fun suffixSecret ↦
          firstChallenges >>= fun firstChallenge ↦
          firstErrors >>= fun firstError ↦
          secondChallenges >>= fun secondChallenge ↦
          secondErrors >>= fun secondError ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
    rw [nativeParallel]
    refine evalDist_bind_congr' sourceSecrets fun sourceSecret ↦ ?_
    refine evalDist_bind_congr' suffixes fun suffixSecret ↦ ?_
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hFirstChallenges (fun firstChallenge ↦
        firstErrors >>= fun firstError ↦
        secondChallenges >>= fun secondChallenge ↦
        secondErrors >>= fun secondError ↦
        finish sourceSecret suffixSecret firstChallenge firstError
          secondChallenge secondError)
  have lweExpanded :
      evalDist (LearningWithErrors.game0
          (problem q degree sourceRank suffixRank tgswLevels errorSampler)
          (zeroReduction gadget continuation)) =
        evalDist (firstChallenges >>= fun firstChallenge ↦
          secondChallenges >>= fun secondChallenge ↦
          sourceSecrets >>= fun sourceSecret ↦
          firstErrors >>= fun firstError ↦
          secondErrors >>= fun secondError ↦
          suffixes >>= fun suffixSecret ↦
          finish sourceSecret suffixSecret firstChallenge firstError
            secondChallenge secondError) := by
    have uniformChallengeProduct :
        ($ᵗ (Challenge q degree sourceRank suffixRank tgswLevels) :
          ProbComp (Challenge q degree sourceRank suffixRank tgswLevels)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    unfold LearningWithErrors.distr
    simp only [problem]
    rw [uniformChallengeProduct]
    simp [zeroReduction, cloudViewEquiv, regroupEquiv,
      bootstrappingKeyEquiv_apply, extensionKeyEquiv_real,
      sourceSecrets, suffixes, firstChallenges, firstErrors, secondChallenges,
      secondErrors, finish, FirstChallenge, FirstError, SecondChallenge, SecondError,
      Native.BootstrapCutSecurity.semiringRqPiAdd_eq_add,
      Native.BootstrapCutSecurity.pointwiseAdd_eq_add, bind_assoc, monad_norm]
  rw [nativeExpanded, lweExpanded]
  exact Encryption.Security.evalDist_bind_six_reorder sourceSecrets suffixes
    firstChallenges firstErrors secondChallenges secondErrors finish

/-! ## Cloud-only acyclic replacement bound -/

/-- Distinguishing the suffix-only source BRK from its zero-message replacement while retaining
the correlated ring-extension table.  The continuation is public: neither ring secret is exposed
to it. -/
noncomputable def publicIndependentSuffixAdvantage
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) : ℝ :=
  (suffixOnlyGame q degree sourceRank suffixRank tgswLevels
    errorSampler gadget continuation).boolDistAdvantage
  (zeroGame q degree sourceRank suffixRank tgswLevels
    errorSampler gadget continuation)

/-- **Acyclic suffix-cloud reduction.** Once the source-prefix circular messages have already
been removed, replacing the remaining independent suffix messages in the source BRK costs at
most two advantages for the same ordinary blocked module-LWE problem.  The extension table and
the BRK rows share the source ring secret in that problem. -/
theorem publicIndependentSuffixAdvantage_le_two_moduleLwe
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    publicIndependentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
        errorSampler gadget continuation ≤
      LearningWithErrors.advantage
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (suffixReduction gadget continuation) +
      LearningWithErrors.advantage
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (zeroReduction gadget continuation) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold publicIndependentSuffixAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (suffixOnlyGame_evalDist_eq_game0 q degree sourceRank suffixRank tgswLevels
        errorSampler gadget continuation) true,
    evalDist_ext_iff.mp
      (zeroGame_evalDist_eq_game0 q degree sourceRank suffixRank tgswLevels
        errorSampler gadget continuation) true]
  let suffixProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem q degree sourceRank suffixRank tgswLevels errorSampler)
    (suffixReduction gadget continuation)]).toReal
  let uniformSuffixProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem q degree sourceRank suffixRank tgswLevels errorSampler)
    (suffixReduction gadget continuation)]).toReal
  let uniformZeroProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem q degree sourceRank suffixRank tgswLevels errorSampler)
    (zeroReduction gadget continuation)]).toReal
  let zeroProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem q degree sourceRank suffixRank tgswLevels errorSampler)
    (zeroReduction gadget continuation)]).toReal
  have hUniform : uniformSuffixProbability = uniformZeroProbability := by
    apply congrArg ENNReal.toReal
    exact evalDist_ext_iff.mp
      ((suffixReduction_game1_evalDist_eq_uniform q degree sourceRank suffixRank
          tgswLevels errorSampler gadget continuation).trans
        (zeroReduction_game1_evalDist_eq_uniform q degree sourceRank suffixRank
          tgswLevels errorSampler gadget continuation).symm) true
  change |suffixProbability - zeroProbability| ≤
    |suffixProbability - uniformSuffixProbability| +
      |zeroProbability - uniformZeroProbability|
  rw [hUniform, abs_sub_comm zeroProbability uniformZeroProbability]
  exact abs_sub_le suffixProbability uniformZeroProbability zeroProbability

/-- Regard a public cloud continuation as a source continuation that ignores both sampled ring
secrets.  This makes the boundary of the ordinary module-LWE theorem explicit. -/
def publicSourceContinuation
    {q degree sourceRank suffixRank tgswLevels : ℕ}
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    SourceContinuation q degree sourceRank suffixRank tgswLevels Bool :=
  fun _ _ bootstrappingKey extensionKey ↦ continuation bootstrappingKey extensionKey

/-- For equal BRK and extension error samplers, the generic contextual suffix advantage restricted
to public continuations is exactly the cloud-only advantage above. -/
theorem independentSuffixAdvantage_public_eq
    (q degree sourceRank suffixRank tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    independentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
        errorSampler errorSampler gadget (publicSourceContinuation continuation) =
      publicIndependentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
        errorSampler gadget continuation := by
  rfl

/-- Public-continuation form of the acyclic suffix-cloud reduction, stated directly for the
contextual advantage used by the full-target-message security decomposition. -/
theorem independentSuffixAdvantage_public_le_two_moduleLwe
    {q degree sourceRank suffixRank tgswLevels : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q degree))
    (gadget : Fin tgswLevels → RLWE.Rq q degree)
    (continuation : PublicContinuation q degree sourceRank suffixRank tgswLevels) :
    independentSuffixAdvantage q degree sourceRank suffixRank tgswLevels
        errorSampler errorSampler gadget (publicSourceContinuation continuation) ≤
      LearningWithErrors.advantage
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (suffixReduction gadget continuation) +
      LearningWithErrors.advantage
        (problem q degree sourceRank suffixRank tgswLevels errorSampler)
        (zeroReduction gadget continuation) := by
  rw [independentSuffixAdvantage_public_eq]
  exact publicIndependentSuffixAdvantage_le_two_moduleLwe errorSampler gadget continuation

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.CloudReduction
