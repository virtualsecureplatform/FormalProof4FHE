/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSecretRandomization

/-!
# Shear-Invariant Narrow Noise for Shared-Randomness One-Cycle TFHE

The exact global-complement action on a rank-one native TGSW ciphertext maps its matched row
errors by the involution

`(e_mask, e_body) ↦ (e_mask + d * e_body, -e_body)`.

Independent narrow errors are generally not invariant under this map.  This module changes only
the joint row-error geometry: it averages an arbitrary base error-vector sampler over the two
points of every shear orbit.  The resulting correlated distribution is exactly shear invariant,
while retaining a finite narrow base sampler rather than replacing the errors by uniform noise.

The module provides structured and direct TGSW samplers accepting a complete correlated error
vector, proves their usual challenge-translation equivalence, and lifts exact complement
transport through the full BRK and the joint BRK plus suffix-style shared-randomness KSK.  The
construction removes the BRK complement-loss obligation.  It does not by itself construct the
nonlinear evaluator needed to randomize the remaining relative master-key bits.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-- Average an arbitrary finite sampler over the two-element orbit of an involution. -/
def involutiveSymmetrization {A : Type} (action : A → A)
    (source : ProbComp A) : ProbComp A := do
  let value ← source
  let applyAction ← $ᵗ Bool
  return if applyAction then action value else value

/-- Orbit averaging makes any source sampler exactly invariant under the involution. -/
theorem involutiveSymmetrization_invariant
    {A : Type} [Fintype A] [DecidableEq A] [SampleableType A]
    (action : A → A) (source : ProbComp A)
    (hinvolutive : Function.Involutive action) :
    evalDist (action <$> involutiveSymmetrization action source) =
      evalDist (involutiveSymmetrization action source) := by
  unfold involutiveSymmetrization
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  apply evalDist_bind_congr' source
  intro value
  apply evalDist_ext
  intro output
  rw [probOutput_bind_uniformBool, probOutput_bind_uniformBool]
  simp only [probOutput_pure]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [hinvolutive value]
  ac_rfl

/-- Every value in an orbit-averaged sampler is either an original value or its image under the
involution.  This support decomposition is used to retain concrete narrowness bounds. -/
theorem mem_support_involutiveSymmetrization_cases
    {A : Type} (action : A → A) (source : ProbComp A) {output : A}
    (houtput : output ∈ support (involutiveSymmetrization action source)) :
    ∃ input ∈ support source, output = input ∨ output = action input := by
  unfold involutiveSymmetrization at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨input, hinput, houtput⟩ := houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨applyAction, _, houtput⟩ := houtput
  simp only [support_pure, Set.mem_singleton_iff] at houtput
  refine ⟨input, hinput, ?_⟩
  cases applyAction
  · exact Or.inl (by simpa using houtput)
  · exact Or.inr (by simpa using houtput)

/-- A TGSW sampler whose complete row-error vector may have correlations. -/
def TGSW.encryptWithErrorVector {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ)
    (errorVectorSampler : ProbComp (Fin (TGSW.rowCount dimension levels) → R))
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    ProbComp (TGSW.Ciphertext R dimension levels) := do
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
  let error ← errorVectorSampler
  return TGSW.addGadget gadget message
    (TLWE.batchAssemble secret challenge 0 error)

/-- Direct gadget-phase presentation with an arbitrary complete error-vector sampler. -/
def TGSW.directEncryptWithErrorVector {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ)
    (errorVectorSampler : ProbComp (Fin (TGSW.rowCount dimension levels) → R))
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    ProbComp (TGSW.Ciphertext R dimension levels) := do
  let challenge ← $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
  let error ← errorVectorSampler
  return TLWE.batchAssemble secret challenge
    (TGSW.gadgetPhase secret gadget message) error

/-- Challenge translation still identifies the structured and direct presentations when the
row errors are correlated. -/
theorem TGSW.encryptWithErrorVector_evalDist_eq_direct
    {R : Type} [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ)
    (errorVectorSampler : ProbComp (Fin (TGSW.rowCount dimension levels) → R))
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    evalDist (TGSW.encryptWithErrorVector dimension levels errorVectorSampler
      secret gadget message) =
      evalDist (TGSW.directEncryptWithErrorVector dimension levels errorVectorSampler
        secret gadget message) := by
  let challenges :
      ProbComp (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R
  let finish : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R →
      (Fin (TGSW.rowCount dimension levels) → R) →
      ProbComp (TGSW.Ciphertext R dimension levels) :=
    fun challenge error ↦ pure
      (TLWE.batchAssemble secret challenge (TGSW.gadgetPhase secret gadget message) error)
  let shift : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R →
      Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R :=
    TGSW.shiftChallenge (dimension := dimension) gadget message
  have left_eq :
      TGSW.encryptWithErrorVector dimension levels errorVectorSampler
          secret gadget message =
        (challenges >>= fun challenge ↦
          errorVectorSampler >>= fun error ↦ finish (shift challenge) error) := by
    unfold TGSW.encryptWithErrorVector
    dsimp only [challenges, finish, shift]
    apply bind_congr
    intro challenge
    apply bind_congr
    intro error
    exact congrArg pure
      (TGSW.addGadget_batchAssemble_zero secret challenge error gadget message)
  have right_eq :
      TGSW.directEncryptWithErrorVector dimension levels errorVectorSampler
          secret gadget message =
        (challenges >>= fun challenge ↦
          errorVectorSampler >>= fun error ↦ finish challenge error) := by
    simp [TGSW.directEncryptWithErrorVector, challenges, finish, monad_norm]
  rw [left_eq, right_eq]
  apply evalDist_ext
  intro ciphertext
  simpa only [challenges, shift] using
    (probOutput_bind_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
      (β := Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
      (TGSW.shiftChallenge (dimension := dimension) gadget message)
      (TGSW.shiftChallenge_bijective (dimension := dimension) gadget message)
      (fun challenge ↦ errorVectorSampler >>= fun error ↦ finish challenge error)
      ciphertext)

/-- Exact complement-invariance requirement for a possibly correlated rank-one error vector. -/
def RankOneComplementErrorVectorInvariant {R : Type} [Ring R] {levels : ℕ}
    (errorVectorSampler : ProbComp (Fin (TGSW.rowCount 1 levels) → R))
    (offset : R) : Prop :=
  evalDist (rankOneComplementErrorShear offset <$> errorVectorSampler) =
    evalDist errorVectorSampler

/-- Orbit averaging any row-vector sampler with its shear gives exact complement invariance. -/
def rankOneShearSymmetrizedErrorVector {R : Type} [Ring R] {levels : ℕ}
    (baseSampler : ProbComp (Fin (TGSW.rowCount 1 levels) → R))
    (offset : R) : ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
  involutiveSymmetrization (rankOneComplementErrorShear offset) baseSampler

theorem rankOneShearSymmetrizedErrorVector_invariant
    {R : Type} [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ}
    (baseSampler : ProbComp (Fin (TGSW.rowCount 1 levels) → R))
    (offset : R) :
    RankOneComplementErrorVectorInvariant
      (rankOneShearSymmetrizedErrorVector baseSampler offset) offset := by
  exact involutiveSymmetrization_invariant
    (rankOneComplementErrorShear offset) baseSampler
    (rankOneComplementErrorShear_involutive offset)

/-- Exact global-complement transport for direct rank-one TGSW rows with a correlated,
shear-invariant error vector. -/
theorem globalComplementTGSW_directEncryptWithErrorVector_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ}
    (errorVectorSampler : ProbComp (Fin (TGSW.rowCount 1 levels) → R))
    (secretValue offset message : R) (gadget : Fin levels → R)
    (hnoise : RankOneComplementErrorVectorInvariant errorVectorSampler offset) :
    evalDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncryptWithErrorVector 1 levels errorVectorSampler
          (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.directEncryptWithErrorVector 1 levels errorVectorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) := by
  let samples := TGSW.rowCount 1 levels
  let errors := errorVectorSampler
  let finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble (fun _ ↦ offset - secretValue) challenge
          (TGSW.gadgetPhase (fun _ ↦ offset - secretValue) gadget (1 - message))
          error) : ProbComp (TGSW.Ciphertext R 1 levels))
  rw [show TGSW.directEncryptWithErrorVector 1 levels errorVectorSampler
      (fun _ ↦ secretValue) gadget message =
      (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
            (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error)) by
    simp [TGSW.directEncryptWithErrorVector, samples, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          finish
            (rankOneGlobalComplementChallenge (levels := levels)
              offset gadget challenge)
            (rankOneComplementErrorShear (levels := levels) offset error)) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin 1) (Fin samples) R)
        fun challenge => ?_
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [samples, finish] using congrArg evalDist
        (congrArg pure (globalComplementTGSW_batchAssemble
          secretValue offset message gadget challenge error))
    _ = evalDist (((fun challenge : Matrix (Fin 1) (Fin samples) R =>
          rankOneGlobalComplementChallenge (levels := levels)
            offset gadget challenge) <$>
          ($ᵗ Matrix (Fin 1) (Fin samples) R)) >>= fun challenge =>
        ((fun error : Fin samples → R =>
          rankOneComplementErrorShear (levels := levels) offset error) <$>
            errors) >>= fun error =>
          finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      rfl
    _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
        ((fun error : Fin samples → R =>
          rankOneComplementErrorShear (levels := levels) offset error) <$>
            errors) >>= fun error =>
          finish challenge error) := by
      rw [evalDist_bind,
        rankOneGlobalComplementChallenge_uniform_evalDist offset gadget,
        ← evalDist_bind]
    _ = evalDist (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin 1) (Fin samples) R)
        fun _ => ?_
      rw [evalDist_bind, show evalDist
          ((fun error : Fin samples → R =>
            rankOneComplementErrorShear (levels := levels) offset error) <$>
              errors) = evalDist errors by
            exact hnoise,
        ← evalDist_bind]
    _ = _ := by
      simp [TGSW.directEncryptWithErrorVector, samples, errors, finish,
        monad_norm]

/-- The same exact law for the structured correlated-error TGSW presentation. -/
theorem globalComplementTGSW_encryptWithErrorVector_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ}
    (errorVectorSampler : ProbComp (Fin (TGSW.rowCount 1 levels) → R))
    (secretValue offset message : R) (gadget : Fin levels → R)
    (hnoise : RankOneComplementErrorVectorInvariant errorVectorSampler offset) :
    evalDist (globalComplementTGSW offset gadget <$>
        TGSW.encryptWithErrorVector 1 levels errorVectorSampler
          (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.encryptWithErrorVector 1 levels errorVectorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) := by
  calc
    _ = evalDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncryptWithErrorVector 1 levels errorVectorSampler
          (fun _ ↦ secretValue) gadget message) :=
      evalDist_map_eq_of_evalDist_eq
        (TGSW.encryptWithErrorVector_evalDist_eq_direct
          1 levels errorVectorSampler (fun _ ↦ secretValue) gadget message)
        (globalComplementTGSW offset gadget)
    _ = evalDist (TGSW.directEncryptWithErrorVector 1 levels errorVectorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) :=
      globalComplementTGSW_directEncryptWithErrorVector_evalDist
        errorVectorSampler secretValue offset message gadget hnoise
    _ = _ :=
      (TGSW.encryptWithErrorVector_evalDist_eq_direct
        1 levels errorVectorSampler (fun _ ↦ offset - secretValue)
          gadget (1 - message)).symm

/-- Rank-one native BRK generation with one arbitrary correlated error-vector draw per TGSW
entry. -/
noncomputable def generateBootstrappingKeyWithErrorVector
    (q degree levels lweDimension : ℕ) [NeZero q]
    (errorVectorSampler :
      ProbComp (Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1)) :
    ProbComp (Native.BootstrappingKey q (degree + 1) 1 levels lweDimension) :=
  Fin.mOfFn lweDimension fun coordinate ↦
    TGSW.encryptWithErrorVector 1 levels errorVectorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q (degree + 1) (lweSecret coordinate))

/-- A shear-invariant correlated error vector removes the complete BRK complement loss. -/
theorem globalComplementBootstrappingKey_generateWithErrorVector_evalDist
    {q degree levels lweDimension : ℕ} [NeZero q]
    (errorVectorSampler :
      ProbComp (Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (hnoise : RankOneComplementErrorVectorInvariant errorVectorSampler
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))) :
    evalDist (globalComplementBootstrappingKey
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        gadget <$>
      generateBootstrappingKeyWithErrorVector q degree levels lweDimension
        errorVectorSampler gadget lweSecret ringSecret) =
      evalDist (generateBootstrappingKeyWithErrorVector q degree levels lweDimension
        errorVectorSampler gadget (globalComplementAction lweSecret true)
        (maskedRingSecret ringSecret
          (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))) := by
  let offset :=
    embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))
  let complementedRingSecret :=
    maskedRingSecret ringSecret
      (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1))
  let secretValue := embedRingSecret q ringSecret (0 : Fin 1)
  have hsourceRing :
      embedRingSecret q ringSecret = fun _ ↦ secretValue := by
    funext component
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    rfl
  have htargetValue :
      embedRingSecret q complementedRingSecret (0 : Fin 1) =
        offset - secretValue := by
    change embedBinaryPolynomial q (degree + 1)
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          (ringSecret 0) (allTruePolynomial (degree + 1))) =
      offset - secretValue
    rw [embedBinaryPolynomial_masked_allTrue]
    simp only [offset, secretValue, embedRingSecret]
    abel
  have htargetRing :
      embedRingSecret q complementedRingSecret =
        fun _ ↦ offset - secretValue := by
    funext component
    have hcomponent : component = 0 := Subsingleton.elim _ _
    subst component
    exact htargetValue
  rw [show globalComplementBootstrappingKey offset gadget =
      (fun bootstrappingKey coordinate ↦
        globalComplementTGSW offset gadget (bootstrappingKey coordinate)) by rfl]
  simpa only [generateBootstrappingKeyWithErrorVector,
      complementedRingSecret] using
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
      lweDimension
      (fun coordinate ↦
        TGSW.encryptWithErrorVector 1 levels errorVectorSampler
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1) (lweSecret coordinate)))
      (fun coordinate ↦
        TGSW.encryptWithErrorVector 1 levels errorVectorSampler
          (embedRingSecret q complementedRingSecret) gadget
          (embedConstantBit q (degree + 1)
            (globalComplementAction lweSecret true coordinate)))
      (fun _ ↦ globalComplementTGSW offset gadget)
      (fun coordinate ↦ by
        have hmessage :
            embedConstantBit q (degree + 1)
                (globalComplementAction lweSecret true coordinate) =
              1 - embedConstantBit q (degree + 1) (lweSecret coordinate) := by
          rw [BlindRotation.embedConstantBit_eq_embedBit,
            BlindRotation.embedConstantBit_eq_embedBit]
          cases hbit : lweSecret coordinate <;>
            simp [globalComplementAction,
              FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
              LWE.MultiKeyAffine.maskedBit, hbit, embedBit]
        rw [hsourceRing, htargetRing, hmessage]
        exact globalComplementTGSW_encryptWithErrorVector_evalDist
          errorVectorSampler secretValue offset
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          gadget hnoise)

/-- Correlate an IID base row law with its complement shear by a hidden uniform orbit bit. -/
def rankOneShearSymmetrizedIIDErrorVector {R : Type} [Ring R] {levels : ℕ}
    (baseErrorSampler : ProbComp R) (offset : R) :
    ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
  rankOneShearSymmetrizedErrorVector
    (ProbComp.sampleIID (TGSW.rowCount 1 levels) baseErrorSampler) offset

theorem rankOneShearSymmetrizedIIDErrorVector_invariant
    {R : Type} [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (baseErrorSampler : ProbComp R) (offset : R) :
    RankOneComplementErrorVectorInvariant
      (rankOneShearSymmetrizedIIDErrorVector
        (levels := levels) baseErrorSampler offset) offset :=
  rankOneShearSymmetrizedErrorVector_invariant _ _

/-- Exact joint BRK+shared-KSK complement transport for an arbitrary invariant correlated BRK
error vector. -/
theorem globalComplementEvaluationKeyPair_generateWithErrorVector_evalDist
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    (ringErrorVectorSampler :
      ProbComp (Fin (TGSW.rowCount 1 tgswLevels) → RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension)
    (hringNoise : RankOneComplementErrorVectorInvariant ringErrorVectorSampler
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))))
    (hkeySwitchNoise :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        keySwitchErrorSampler) :
    evalDist (globalComplementEvaluationKeyPair
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          generateBootstrappingKeyWithErrorVector q degree tgswLevels
            lweDimension ringErrorVectorSampler tgswGadget lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget sourceSecret
              lweSecret
        return (bootstrappingKey, keySwitchKey))) =
      evalDist (do
        let bootstrappingKey ←
          generateBootstrappingKeyWithErrorVector q degree tgswLevels
            lweDimension ringErrorVectorSampler tgswGadget
              (globalComplementAction lweSecret true)
              (maskedRingSecret ringSecret
                (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget
              (globalComplementAction sourceSecret true)
              (globalComplementAction lweSecret true)
        return (bootstrappingKey, keySwitchKey)) := by
  unfold globalComplementEvaluationKeyPair
  exact
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.independentPair_map_evalDist_congr
      (generateBootstrappingKeyWithErrorVector q degree tgswLevels
        lweDimension ringErrorVectorSampler tgswGadget lweSecret ringSecret)
      (Native.generateKeySwitchKey q lweDimension sourceDimension keySwitchLevels
        keySwitchErrorSampler keySwitchGadget sourceSecret lweSecret)
      (generateBootstrappingKeyWithErrorVector q degree tgswLevels
        lweDimension ringErrorVectorSampler tgswGadget
          (globalComplementAction lweSecret true)
          (maskedRingSecret ringSecret
            (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1))))
      (Native.generateKeySwitchKey q lweDimension sourceDimension keySwitchLevels
        keySwitchErrorSampler keySwitchGadget
          (globalComplementAction sourceSecret true)
          (globalComplementAction lweSecret true))
      (globalComplementBootstrappingKey
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        tgswGadget)
      (globalComplementKeySwitchKey keySwitchGadget)
      (globalComplementBootstrappingKey_generateWithErrorVector_evalDist
        ringErrorVectorSampler tgswGadget lweSecret ringSecret hringNoise)
      (globalComplementKeySwitchKey_generate_evalDist keySwitchErrorSampler
        hkeySwitchNoise keySwitchGadget sourceSecret lweSecret)

/-- With orbit-symmetrized IID base noise, the complete joint BRK+KSK complement law is exact
without a BRK noise hypothesis. -/
theorem globalComplementEvaluationKeyPair_shearSymmetrized_evalDist
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    (baseRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension)
    (hkeySwitchNoise :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        keySwitchErrorSampler) :
    let offset :=
      embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))
    let ringErrorVectorSampler :=
      rankOneShearSymmetrizedIIDErrorVector
        (levels := tgswLevels) baseRingErrorSampler offset
    evalDist (globalComplementEvaluationKeyPair offset
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          generateBootstrappingKeyWithErrorVector q degree tgswLevels
            lweDimension ringErrorVectorSampler tgswGadget lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget sourceSecret
              lweSecret
        return (bootstrappingKey, keySwitchKey))) =
      evalDist (do
        let bootstrappingKey ←
          generateBootstrappingKeyWithErrorVector q degree tgswLevels
            lweDimension ringErrorVectorSampler tgswGadget
              (globalComplementAction lweSecret true)
              (maskedRingSecret ringSecret
                (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget
              (globalComplementAction sourceSecret true)
              (globalComplementAction lweSecret true)
        return (bootstrappingKey, keySwitchKey)) := by
  dsimp only
  apply globalComplementEvaluationKeyPair_generateWithErrorVector_evalDist
  · exact rankOneShearSymmetrizedIIDErrorVector_invariant _ _
  · exact hkeySwitchNoise

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
