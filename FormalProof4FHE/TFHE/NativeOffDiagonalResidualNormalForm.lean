/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.ConditionalCollision
import FormalProof4FHE.TFHE.DiscreteGaussianSampler
import FormalProof4FHE.TFHE.NativeCiphertextTranslation
import FormalProof4FHE.TFHE.NativeShiftedDifferenceReparameterization

/-!
# Off-Diagonal Residual Normal Form for the Native Shifted TFHE Evaluator

For a correct shifted-CMux candidate, output coordinate `j` retains source BRK entry `j` and adds
an internal-product perturbation controlled by source entry `i`.  When `j ≠ i`, native BRK
generation samples those two TGSW entries independently.  Together with the independent-difference
reparameterization, the retained entry is therefore a genuinely fresh TGSW ciphertext independent
of the perturbation.

This file proves the resulting construction-level normal form.  The output-coordinate experiment
is exactly a direct residual encryption whose residual is the phase of the independently sampled
control perturbation.  The selected diagonal `j = i` is deliberately excluded: there the retained
entry and control coincide, so this independence argument does not apply.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

variable {q degree ringRank lweDimension : ℕ}

/-- The direct fresh TGSW sampler for one native BRK coordinate. -/
noncomputable def directEntrySampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  TGSW.directEncrypt ringRank params.levels errorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))

/-- The zero-control internal-product ciphertext added to a retained source entry. -/
noncomputable def controlPerturbation
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control differenceEntry :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  @TGSW.internalProductWithDigits (RLWE.Rq q (degree + 1))
    (LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod q) (degree + 1)).toSemiring
    ringRank params.levels
    (fun row => Gadget.Base.ringExtendedDigits params
      (TLWE.entry differenceEntry row))
    (candidateHomogeneousPart params proofZero candidate control)

/-- The complete correct entry is its retained source ciphertext plus `controlPerturbation`. -/
theorem selectBootstrappingKey_correct_add_controlPerturbation
    (params : Gadget.Base.Parameters q)
    (hidden : BinarySecret lweDimension)
    (coordinate outputCoordinate : Fin lweDimension)
    (source difference :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
    selectBootstrappingKey params coordinate (hidden coordinate) source
        (addDifference source difference) outputCoordinate =
      TGSW.add (source outputCoordinate)
        (controlPerturbation params (hidden coordinate) (source coordinate)
          (difference outputCoordinate)) := by
  rw [selectBootstrappingKey_correct_ciphertext_addDifference]
  rfl

/-- Independently sample the selected control entry and one uniform difference entry, then form
the complete zero-control internal-product perturbation. -/
noncomputable def perturbationSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let control ← directEntrySampler params errorSampler hidden ringSecret coordinate
  let differenceEntry ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  return controlPerturbation params (hidden coordinate) control differenceEntry

/-- One correct output entry of the native direct-BRK experiment under independent-difference
coins. -/
noncomputable def correctEntryExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let source ← BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension errorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let difference ←
    $ᵗ BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  return selectBootstrappingKey params coordinate (hidden coordinate) source
    (addDifference source difference) outputCoordinate

/-- Complete correct shifted-CMux BRK experiment under independent-difference coins. -/
noncomputable def correctKeyExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) := do
  let source ← BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension errorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let difference ←
    $ᵗ BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  return selectBootstrappingKey params coordinate (hidden coordinate) source
    (addDifference source difference)

/-- Conditional coordinate sampler after pulling the selected source control in front.  At the
selected coordinate the retained base is that same control; elsewhere the retained base is an
independent native direct entry. -/
noncomputable def factorizedCoordinateSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let base ← if outputCoordinate = coordinate then pure control
    else directEntrySampler params errorSampler hidden ringSecret outputCoordinate
  let differenceEntry ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  return TGSW.add base
    (controlPerturbation params (hidden coordinate) control differenceEntry)

/-- Whole-BRK factorized form: the common selected source control is sampled once, after which
all difference entries and all nonselected source entries are independent coordinate samplers. -/
noncomputable def factorizedKeyExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) := do
  let control ← directEntrySampler params errorSampler hidden ringSecret coordinate
  Fin.mOfFn lweDimension fun outputCoordinate =>
    factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate

/-- With the selected source control fixed, the only random input to an off-diagonal
internal-product perturbation is one independent uniform difference entry. -/
noncomputable def fixedControlPerturbationSampler [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let differenceEntry ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  return controlPerturbation params candidate control differenceEntry

/-- Public mask-matrix space of one off-diagonal native TGSW entry. -/
abbrev OffDiagonalChallenge (q degree ringRank levels : ℕ) :=
  Matrix (Fin ringRank) (Fin (TGSW.rowCount ringRank levels))
    (RLWE.Rq q (degree + 1))

/-- Complete row-error vector of one off-diagonal native TGSW entry. -/
abbrev OffDiagonalErrorVector (q degree ringRank levels : ℕ) :=
  Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)

/-- The correct candidate contributes either the control error or its additive inverse. -/
def signedControlValue {R : Type} [Ring R] (candidate : Bool) (value : R) : R :=
  if candidate then -value else value

/-- Error-only form of an off-diagonal internal product after fixing the public gadget digits.
It is independent of the control ciphertext's public masks and of the secret used to assemble
those masks. -/
def perturbationErrorOperator {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (controlError : Fin (TGSW.rowCount dimension levels) → R) :
    Fin (TGSW.rowCount dimension levels) → R :=
  fun row ↦
    ∑ index : Fin (dimension + 1) × Fin levels,
      digits row index.1 index.2 *
        signedControlValue candidate (controlError (finProdFinEquiv index))

/-- The phase of a row-wise internal product is the corresponding linear operator on the
control's complete phase vector. -/
theorem batchPhase_internalProductWithDigits {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : TGSW.Ciphertext R dimension levels) :
    TLWE.batchPhase secret (TGSW.internalProductWithDigits digits control) =
      fun row ↦
        ∑ index : Fin (dimension + 1) × Fin levels,
          digits row index.1 index.2 *
            TLWE.batchPhase secret control (finProdFinEquiv index) := by
  funext row
  rw [← TLWE.phase_entry, TGSW.entry_internalProductWithDigits,
    TGSW.phase_externalProduct]
  simp only [TLWE.phase_entry]

/-- Correct toggling of a structured source control removes its gadget message and leaves its
homogeneous part with the candidate-dependent sign.  This local copy avoids a cyclic import from
the selected-diagonal normal form. -/
theorem candidateHomogeneousPart_structured_correct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (homogeneous : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    candidateHomogeneousPart params proofZero candidate
        (TGSW.addGadget (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) homogeneous) =
      if candidate then ScalarSecretRandomization.negateCiphertext homogeneous
      else homogeneous := by
  rw [BlindRotation.embedConstantBit_eq_embedBit]
  unfold candidateHomogeneousPart
  rw [proofNeg_eq_neg, proofZero_eq_zero, neg_zero]
  unfold proofAddGadget candidateControl
  rw [TGSW.addGadget_zero]
  simpa only [TGSW.addGadget_zero] using
    (toggleTGSW_correct (Gadget.Base.ringGadget params) candidate homogeneous)

/-- A structured correct control contributes only the digit-weighted signed phase vector of its
homogeneous part. -/
theorem controlPerturbation_structured_correct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (homogeneous difference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    controlPerturbation params candidate
        (TGSW.addGadget (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) homogeneous)
        difference =
      TGSW.internalProductWithDigits
        (fun row ↦ Gadget.Base.ringExtendedDigits params (TLWE.entry difference row))
        (if candidate then ScalarSecretRandomization.negateCiphertext homogeneous
        else homogeneous) := by
  unfold controlPerturbation
  rw [candidateHomogeneousPart_structured_correct]

/-- Consequently, the phase of the off-diagonal perturbation depends on a structured control
only through its error/phase vector. -/
theorem batchPhase_controlPerturbation_structured_correct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (secret : Fin ringRank → RLWE.Rq q (degree + 1))
    (homogeneous difference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    TLWE.batchPhase secret
        (controlPerturbation params candidate
          (TGSW.addGadget (Gadget.Base.ringGadget params)
            (embedConstantBit q (degree + 1) candidate) homogeneous)
          difference) =
      perturbationErrorOperator candidate
        (fun row ↦ Gadget.Base.ringExtendedDigits params (TLWE.entry difference row))
        (TLWE.batchPhase secret homogeneous) := by
  rw [controlPerturbation_structured_correct,
    batchPhase_internalProductWithDigits]
  cases candidate with
  | false => rfl
  | true =>
      simp only [if_true]
      rw [Native.ShiftedResidualBounds.batchPhase_negateCiphertext]
      rfl

/-- Conditional effective error law of one off-diagonal entry.  It samples the uniform
difference ciphertext used by the internal product, takes its phase under the ring secret, and
adds the independently sampled narrow source-error vector.  This is the finite smoothing object
that must approach the target error-vector law. -/
noncomputable def fixedControlResidualErrorSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ProbComp (OffDiagonalErrorVector q degree ringRank params.levels) := do
  let perturbation ← fixedControlPerturbationSampler params candidate control
  let sourceError ←
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  return TLWE.batchPhase (embedRingSecret q ringSecret) perturbation + sourceError

/-- Error-only off-diagonal law after replacing a structured generated control by its sampled
error vector.  The remaining randomness is an independent uniform digit tensor (obtained by
digitizing the uniform difference ciphertext) and the fresh source-error vector. -/
noncomputable def errorOnlyResidualSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    ProbComp (OffDiagonalErrorVector q degree ringRank params.levels) := do
  let differenceEntry ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let sourceError ←
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  return perturbationErrorOperator candidate
    (fun row ↦ Gadget.Base.ringExtendedDigits params (TLWE.entry differenceEntry row))
    controlError + sourceError

/-- Complete uniform randomness for the centered-binomial error-only residual law: one native
difference entry and one bit-pair table for every fresh source-error row. -/
abbrev CenteredBinomialResidualCoins
    (q degree ringRank levels eta : ℕ) :=
  RingGSWCiphertext q (degree + 1) ringRank levels ×
    RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank levels) (degree + 1) eta

/-- Deterministically evaluate the centered-binomial residual from all of its uniform coins. -/
noncomputable def centeredBinomialResidualFromCoins [NeZero q]
    (params : Gadget.Base.Parameters q)
    (eta : ℕ)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels)
    (coins : CenteredBinomialResidualCoins q degree ringRank params.levels eta) :
    OffDiagonalErrorVector q degree ringRank params.levels :=
  perturbationErrorOperator candidate
      (fun row ↦ Gadget.Base.ringExtendedDigits params (TLWE.entry coins.1 row))
      controlError +
    RLWE.CenteredBinomial.errorVectorFromCoins q
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta coins.2

/-- The centered-binomial residual law is exactly the deterministic image of its finite uniform
coin space. -/
theorem errorOnlyResidualSampler_centeredBinomial_evalDist_eq_uniformCoins [NeZero q]
    (params : Gadget.Base.Parameters q)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels)
    (eta : ℕ) :
    evalDist
        (errorOnlyResidualSampler params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          candidate controlError) =
      evalDist
        (centeredBinomialResidualFromCoins params eta candidate controlError <$>
          ($ᵗ (CenteredBinomialResidualCoins
            q degree ringRank params.levels eta))) := by
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let ErrorCoins := RLWE.CenteredBinomial.ErrorVectorCoinTable
    (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  let finish : Difference →
      OffDiagonalErrorVector q degree ringRank params.levels →
      OffDiagonalErrorVector q degree ringRank params.levels :=
    fun differenceEntry sourceError ↦
      perturbationErrorOperator candidate
          (fun row ↦ Gadget.Base.ringExtendedDigits params
            (TLWE.entry differenceEntry row)) controlError + sourceError
  let assemble : Difference → ErrorCoins →
      OffDiagonalErrorVector q degree ringRank params.levels :=
    fun differenceEntry sourceCoins ↦
      finish differenceEntry
        (RLWE.CenteredBinomial.errorVectorFromCoins q
          (TGSW.rowCount ringRank params.levels) (degree + 1) eta sourceCoins)
  have hErrors := RLWE.CenteredBinomial.sampleIID_sampler_evalDist_eq_uniformCoins
    q (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  have hSource :
      evalDist
          (errorOnlyResidualSampler params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            candidate controlError) =
        evalDist (do
          let differenceEntry ← $ᵗ Difference
          let sourceCoins ← $ᵗ ErrorCoins
          pure (assemble differenceEntry sourceCoins)) := by
    unfold errorOnlyResidualSampler
    refine evalDist_bind_congr' ($ᵗ Difference) fun differenceEntry ↦ ?_
    have hMapped := evalDist_map_eq_of_evalDist_eq hErrors
      (finish differenceEntry)
    simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply, Function.comp_def, assemble, finish, Difference,
      ErrorCoins] using hMapped
  have hProduct := FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
    (first := Difference) (second := ErrorCoins)
  have hMappedProduct := evalDist_map_eq_of_evalDist_eq hProduct
    (fun coins : Difference × ErrorCoins ↦ assemble coins.1 coins.2)
  calc
    _ = evalDist (do
        let differenceEntry ← $ᵗ Difference
        let sourceCoins ← $ᵗ ErrorCoins
        pure (assemble differenceEntry sourceCoins)) := hSource
    _ = evalDist
        ((fun coins : Difference × ErrorCoins ↦ assemble coins.1 coins.2) <$>
          ($ᵗ (Difference × ErrorCoins))) := by
      simpa only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
        pure_bind] using hMappedProduct
    _ = _ := by
      rfl

/-- Negating the fixed control-error vector exchanges the two candidate signs exactly. -/
theorem errorOnlyResidualSampler_true_eq_false_neg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    errorOnlyResidualSampler params sourceErrorSampler true controlError =
      errorOnlyResidualSampler params sourceErrorSampler false (-controlError) := by
  unfold errorOnlyResidualSampler
  apply bind_congr
  intro differenceEntry
  apply bind_congr
  intro sourceError
  apply congrArg pure
  rfl

/-- Explicit randomness used by one honestly generated structured TGSW control. -/
abbrev OffDiagonalControlWitness (q degree ringRank levels : ℕ) :=
  OffDiagonalChallenge q degree ringRank levels ×
    OffDiagonalErrorVector q degree ringRank levels

/-- Independent public challenge and narrow control-error vector. -/
noncomputable def structuredControlWitnessSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    ProbComp (OffDiagonalControlWitness q degree ringRank params.levels) := do
  let challenge ← $ᵗ OffDiagonalChallenge q degree ringRank params.levels
  let controlError ←
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  return (challenge, controlError)

/-- Assemble one structured correct TGSW control from its explicit witness. -/
noncomputable def structuredControlFromWitness [NeZero q]
    (params : Gadget.Base.Parameters q)
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (witness : OffDiagonalControlWitness q degree ringRank params.levels) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  TGSW.addGadget (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
    (TLWE.batchAssemble (embedRingSecret q ringSecret) witness.1 0 witness.2)

/-- Mapping the explicit witness sampler through structured assembly is definitionally the
ordinary structured TGSW encryption sampler. -/
theorem structuredControlWitnessSampler_map_eq_encrypt [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    structuredControlFromWitness params candidate ringSecret <$>
        structuredControlWitnessSampler (ringRank := ringRank) params sourceErrorSampler =
      TGSW.encrypt ringRank params.levels sourceErrorSampler
        (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate) := by
  simp [structuredControlWitnessSampler, structuredControlFromWitness,
    TGSW.encrypt, TLWE.batchEncrypt, monad_norm]

/-- The explicit structured-control witness presentation and the direct native TGSW sampler
have exactly the same output distribution. -/
theorem structuredControlWitnessSampler_evalDist_eq_directEncrypt [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (structuredControlFromWitness params candidate ringSecret <$>
          structuredControlWitnessSampler (ringRank := ringRank) params sourceErrorSampler) =
      evalDist
        (TGSW.directEncrypt ringRank params.levels sourceErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) := by
  rw [structuredControlWitnessSampler_map_eq_encrypt]
  exact TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels sourceErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)

/-- Projecting away the independent public challenge leaves exactly the sampled control-error
vector. -/
theorem structuredControlWitnessSampler_snd_evalDist [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    evalDist
        (Prod.snd <$>
          structuredControlWitnessSampler (ringRank := ringRank) params sourceErrorSampler) =
      evalDist
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          sourceErrorSampler) := by
  unfold structuredControlWitnessSampler
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply evalDist_ext
  intro value
  simp only [bind_pure, probOutput_bind_const, probFailure_uniformSample,
    tsub_zero, one_mul]

/-- For a structured correct control, the conditional residual sampler is exactly the
error-only sampler.  In particular, its distribution does not depend on the control's public
challenge matrix or on the ring secret. -/
theorem fixedControlResidualErrorSampler_structured_eq_errorOnly [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (challenge : OffDiagonalChallenge q degree ringRank params.levels)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    fixedControlResidualErrorSampler params sourceErrorSampler candidate ringSecret
        (TGSW.addGadget (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)
          (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 controlError)) =
      errorOnlyResidualSampler params sourceErrorSampler candidate controlError := by
  have hPhase :
      TLWE.batchPhase (embedRingSecret q ringSecret)
          (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 controlError) =
        controlError := by
    simpa using
      (TLWE.batchPhase_batchAssemble (embedRingSecret q ringSecret)
        challenge 0 controlError)
  unfold fixedControlResidualErrorSampler fixedControlPerturbationSampler
    errorOnlyResidualSampler
  simp only [bind_assoc, pure_bind,
    batchPhase_controlPerturbation_structured_correct, hPhase]

/-- Fresh target error-vector law for one native TGSW entry. -/
noncomputable def targetErrorVectorSampler
    (params : Gadget.Base.Parameters q)
    (targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    ProbComp (OffDiagonalErrorVector q degree ringRank params.levels) :=
  ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) targetErrorSampler

/-- The `L²` loss of a structured control is therefore a function only of its control-error
vector. -/
noncomputable def errorOnlyResidualL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  FormalProof4FHE.ConditionalCollision.l2Loss
    (errorOnlyResidualSampler params sourceErrorSampler candidate controlError)
    (targetErrorVectorSampler (ringRank := ringRank) params targetErrorSampler)

/-- Exact finite fiber-count expression for the centered-binomial residual against a compiled
coefficientwise discrete-Gaussian target.  Both inputs are deterministic images of explicit
uniform finite spaces. -/
noncomputable def centeredBinomialResidualFiberL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  FormalProof4FHE.ConditionalCollision.twoUniformImagesL2Loss
    (centeredBinomialResidualFromCoins params eta candidate controlError)
    (DiscreteGaussianSampler.ringErrorVectorFromTickets
      (TGSW.rowCount ringRank params.levels) (degree + 1) certificate)

/-- The residual `L²` obligation is definitionally an explicit finite collision/fiber-count
quantity once centered-binomial source coins and compiled Gaussian tickets are exposed. -/
theorem errorOnlyResidualL2Loss_centeredBinomial_ringSampler_eq_fiber [NeZero q]
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    errorOnlyResidualL2Loss params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        candidate controlError =
      centeredBinomialResidualFiberL2Loss params eta certificate
        candidate controlError := by
  have hReal := errorOnlyResidualSampler_centeredBinomial_evalDist_eq_uniformCoins
    (ringRank := ringRank) params candidate controlError eta
  have hIdeal :=
    DiscreteGaussianSampler.sampleIID_ringSampler_evalDist_eq_uniformTickets
      (TGSW.rowCount ringRank params.levels) (degree + 1) certificate
  unfold errorOnlyResidualL2Loss targetErrorVectorSampler
  calc
    FormalProof4FHE.ConditionalCollision.l2Loss
        (errorOnlyResidualSampler params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          candidate controlError)
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) =
      FormalProof4FHE.ConditionalCollision.l2Loss
        (centeredBinomialResidualFromCoins params eta candidate controlError <$>
          ($ᵗ (CenteredBinomialResidualCoins
            q degree ringRank params.levels eta)))
        (DiscreteGaussianSampler.ringErrorVectorFromTickets
            (TGSW.rowCount ringRank params.levels) (degree + 1) certificate <$>
          ($ᵗ (DiscreteGaussianSampler.RingErrorVectorTicketCoins
            (TGSW.rowCount ringRank params.levels) (degree + 1) certificate))) :=
      FormalProof4FHE.ConditionalCollision.l2Loss_congr hReal hIdeal
    _ = centeredBinomialResidualFiberL2Loss params eta certificate
          candidate controlError := by
      exact FormalProof4FHE.ConditionalCollision.l2Loss_uniformImages_eq_twoUniformImagesL2Loss
        (centeredBinomialResidualFromCoins params eta candidate controlError)
        (DiscreteGaussianSampler.ringErrorVectorFromTickets
          (TGSW.rowCount ringRank params.levels) (degree + 1) certificate)

theorem centeredBinomialResidualFiberL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ centeredBinomialResidualFiberL2Loss params eta certificate
      candidate controlError := by
  unfold centeredBinomialResidualFiberL2Loss
  rw [← FormalProof4FHE.ConditionalCollision.l2Loss_uniformImages_eq_twoUniformImagesL2Loss]
  exact FormalProof4FHE.ConditionalCollision.l2Loss_nonneg _ _

theorem errorOnlyResidualL2Loss_true_eq_false_neg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler true controlError =
      errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
        false (-controlError) := by
  unfold errorOnlyResidualL2Loss
  rw [errorOnlyResidualSampler_true_eq_false_neg]

theorem errorOnlyResidualL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
      candidate controlError :=
  FormalProof4FHE.ConditionalCollision.l2Loss_nonneg _ _

/-- Exact residual-level distance for one generated control.  This removes the public masks,
messages, and ciphertext assembly from the analytic obligation. -/
noncomputable def conditionalResidualErrorDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  tvDist
    (fixedControlResidualErrorSampler params sourceErrorSampler candidate ringSecret control)
    (targetErrorVectorSampler (ringRank := ringRank) params targetErrorSampler)

/-- Explicit finite `L²` smoothing budget for the same effective residual law.  It remains total
when a compiled target table has zero-probability residues, unlike a Pearson quotient. -/
noncomputable def conditionalResidualErrorL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  FormalProof4FHE.ConditionalCollision.l2Loss
    (fixedControlResidualErrorSampler params sourceErrorSampler candidate ringSecret control)
    (targetErrorVectorSampler (ringRank := ringRank) params targetErrorSampler)

/-- On an honest structured-control witness, the older ciphertext-indexed loss is exactly the
new error-only loss. -/
theorem conditionalResidualErrorL2Loss_structured_eq_errorOnly [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (witness : OffDiagonalControlWitness q degree ringRank params.levels) :
    conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
        candidate ringSecret
        (structuredControlFromWitness params candidate ringSecret witness) =
      errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
        candidate witness.2 := by
  unfold conditionalResidualErrorL2Loss errorOnlyResidualL2Loss
    structuredControlFromWitness
  rw [fixedControlResidualErrorSampler_structured_eq_errorOnly]

/-- Assemble one fresh public mask and a supplied effective error vector into the direct native
TGSW row presentation for the requested message coordinate. -/
noncomputable def entryFromErrorVectorSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorVectorSampler :
      ProbComp (OffDiagonalErrorVector q degree ringRank params.levels))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let challenge ← $ᵗ OffDiagonalChallenge q degree ringRank params.levels
  let error ← errorVectorSampler
  return TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
    (TGSW.gadgetPhase (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) (hidden outputCoordinate))) error

/-- Conditional coordinate normal form.  The diagonal is retained verbatim; every other
coordinate is a fresh direct residual encryption whose residual is the fixed-control
perturbation phase. -/
noncomputable def residualizedCoordinateSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  if outputCoordinate = coordinate then
    factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate
  else do
    let perturbation ← fixedControlPerturbationSampler params (hidden coordinate) control
    TGSW.directEncryptWithResidual ringRank params.levels errorSampler
      (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) (hidden outputCoordinate))
      (TLWE.batchPhase (embedRingSecret q ringSecret) perturbation)

theorem conditionalResidualErrorDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ conditionalResidualErrorDistance params sourceErrorSampler targetErrorSampler
      candidate ringSecret control :=
  tvDist_nonneg _ _

theorem conditionalResidualErrorL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
      candidate ringSecret control :=
  FormalProof4FHE.ConditionalCollision.l2Loss_nonneg _ _

theorem conditionalResidualErrorDistance_le_l2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    conditionalResidualErrorDistance params sourceErrorSampler targetErrorSampler
        candidate ringSecret control ≤
      conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
        candidate ringSecret control :=
  FormalProof4FHE.ConditionalCollision.tvDist_le_l2Loss _ _

/-- Away from the selected coordinate, commuting the independent perturbation and fresh public
mask samples exposes exactly `fixedControlResidualErrorSampler`. -/
theorem residualizedCoordinateSampler_evalDist_eq_entryFromResidualError [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hCoordinate : outputCoordinate ≠ coordinate) :
    evalDist
        (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
          control outputCoordinate) =
      evalDist
        (entryFromErrorVectorSampler params
          (fixedControlResidualErrorSampler params sourceErrorSampler (hidden coordinate)
            ringSecret control)
          hidden ringSecret outputCoordinate) := by
  let Perturbation := fixedControlPerturbationSampler params (hidden coordinate) control
  let Challenge : ProbComp (OffDiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ OffDiagonalChallenge q degree ringRank params.levels
  let SourceErrors : ProbComp (OffDiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let finish :
      RingGSWCiphertext q (degree + 1) ringRank params.levels →
        OffDiagonalChallenge q degree ringRank params.levels →
          OffDiagonalErrorVector q degree ringRank params.levels →
            ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    fun perturbation challenge sourceError =>
    pure (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
      (TGSW.gadgetPhase (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) (hidden outputCoordinate)))
      (TLWE.batchPhase (embedRingSecret q ringSecret) perturbation + sourceError))
  rw [residualizedCoordinateSampler, if_neg hCoordinate]
  calc
    _ = evalDist (Perturbation >>= fun perturbation =>
          Challenge >>= fun challenge =>
            SourceErrors >>= fun sourceError => finish perturbation challenge sourceError) := by
      rfl
    _ = evalDist (Challenge >>= fun challenge =>
          Perturbation >>= fun perturbation =>
            SourceErrors >>= fun sourceError => finish perturbation challenge sourceError) :=
      evalDist_bind_bind_swap Perturbation Challenge
        (fun perturbation challenge =>
          SourceErrors >>= fun sourceError => finish perturbation challenge sourceError)
    _ = _ := by
      simp [entryFromErrorVectorSampler, fixedControlResidualErrorSampler,
        Perturbation, Challenge, SourceErrors, finish]

/-- A fresh direct target entry is the same mask-and-message assembly applied to the fresh target
error-vector sampler. -/
theorem directEntrySampler_evalDist_eq_entryFromTargetError [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (outputCoordinate : Fin lweDimension) :
    evalDist (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) =
      evalDist
        (entryFromErrorVectorSampler params
          (targetErrorVectorSampler (ringRank := ringRank) params targetErrorSampler)
          hidden ringSecret outputCoordinate) := by
  rfl

/-- Public masks, gadget messages, and deterministic ciphertext assembly do not increase the
effective residual-vector distance. -/
theorem tvDist_residualizedCoordinateSampler_directEntry_le_residualError [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hCoordinate : outputCoordinate ≠ coordinate) :
    tvDist
        (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
          control outputCoordinate)
        (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) ≤
      conditionalResidualErrorDistance params sourceErrorSampler targetErrorSampler
        (hidden coordinate) ringSecret control := by
  let Challenge : ProbComp (OffDiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ OffDiagonalChallenge q degree ringRank params.levels
  let ActualErrors := fixedControlResidualErrorSampler params sourceErrorSampler
    (hidden coordinate) ringSecret control
  let TargetErrors := targetErrorVectorSampler (ringRank := ringRank) params targetErrorSampler
  let assemble := fun
      (challenge : OffDiagonalChallenge q degree ringRank params.levels)
      (error : OffDiagonalErrorVector q degree ringRank params.levels) =>
    TLWE.batchAssemble (embedRingSecret q ringSecret) challenge
      (TGSW.gadgetPhase (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) (hidden outputCoordinate))) error
  have hData :
      tvDist
          (entryFromErrorVectorSampler params ActualErrors hidden ringSecret outputCoordinate)
          (entryFromErrorVectorSampler params TargetErrors hidden ringSecret outputCoordinate) ≤
        tvDist ActualErrors TargetErrors := by
    simpa only [entryFromErrorVectorSampler, Challenge, ActualErrors, TargetErrors,
      assemble, map_eq_bind_pure_comp, Function.comp_def] using
      (tvDist_bind_left_le_const' (m := ProbComp) Challenge
        (fun challenge => assemble challenge <$> ActualErrors)
        (fun challenge => assemble challenge <$> TargetErrors)
        (tvDist ActualErrors TargetErrors)
        (fun challenge => tvDist_map_le (m := ProbComp)
          (assemble challenge) ActualErrors TargetErrors))
  change tvDist
      (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
        control outputCoordinate)
      (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) ≤
    tvDist ActualErrors TargetErrors
  unfold tvDist at hData ⊢
  rw [residualizedCoordinateSampler_evalDist_eq_entryFromResidualError
    params sourceErrorSampler hidden ringSecret coordinate outputCoordinate control hCoordinate]
  rw [directEntrySampler_evalDist_eq_entryFromTargetError
    params targetErrorSampler hidden ringSecret outputCoordinate]
  exact hData

theorem tvDist_residualizedCoordinateSampler_directEntry_le_residualL2 [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hCoordinate : outputCoordinate ≠ coordinate) :
    tvDist
        (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
          control outputCoordinate)
        (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) ≤
      conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
        (hidden coordinate) ringSecret control :=
  (tvDist_residualizedCoordinateSampler_directEntry_le_residualError params
      sourceErrorSampler targetErrorSampler hidden ringSecret coordinate outputCoordinate
      control hCoordinate).trans
    (conditionalResidualErrorDistance_le_l2Loss params sourceErrorSampler
      targetErrorSampler (hidden coordinate) ringSecret control)

/-- The finite data on which one conditional off-diagonal comparison depends. -/
abbrev ConditionalDistanceWitness
    (params : Gadget.Base.Parameters q) :=
  BinarySecret lweDimension ×
    RingBinarySecret ringRank (degree + 1) ×
      RingGSWCiphertext q (degree + 1) ringRank params.levels

/-- Exact conditional distance for one fixed input/output coordinate pair and one finite
secret/control witness. -/
noncomputable def conditionalResidualDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate outputCoordinate : Fin lweDimension)
    (witness : ConditionalDistanceWitness (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) params) : ℝ :=
  tvDist
    (residualizedCoordinateSampler params sourceErrorSampler witness.1 witness.2.1
      coordinate witness.2.2 outputCoordinate)
    (directEntrySampler params targetErrorSampler witness.1 witness.2.1 outputCoordinate)

/-- Canonical finite worst-case off-diagonal operator loss.  The finite witness space is filtered
to controls in the exact source-generator support; adjoining zero makes the maximum total even
before using nonfailure of that generator.  Thus this is an attained, support-aware maximum rather
than an abstract supremum or a caller-provided distributional bound. -/
noncomputable def worstCaseConditionalResidualDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate outputCoordinate : Fin lweDimension) : ℝ := by
  classical
  exact (insert 0
    (((Finset.univ : Finset
        (ConditionalDistanceWitness (degree := degree) (ringRank := ringRank)
          (lweDimension := lweDimension) params)).filter fun
            witness : ConditionalDistanceWitness (degree := degree) (ringRank := ringRank)
              (lweDimension := lweDimension) params ↦
        witness.2.2 ∈ support
          (directEntrySampler params sourceErrorSampler witness.1 witness.2.1 coordinate)).image
      (conditionalResidualDistance (degree := degree) (ringRank := ringRank)
        (lweDimension := lweDimension) params sourceErrorSampler targetErrorSampler
        coordinate outputCoordinate))).max' (by simp)

/-- Every fixed conditional residual comparison is bounded by the canonical finite maximum. -/
theorem conditionalResidualDistance_le_worstCase [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate outputCoordinate : Fin lweDimension)
    (witness : ConditionalDistanceWitness (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) params)
    (hcontrol : witness.2.2 ∈ support
      (directEntrySampler params sourceErrorSampler witness.1 witness.2.1 coordinate)) :
    conditionalResidualDistance params sourceErrorSampler targetErrorSampler
        coordinate outputCoordinate witness ≤
      worstCaseConditionalResidualDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate outputCoordinate := by
  classical
  unfold worstCaseConditionalResidualDistance
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨witness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontrol⟩, rfl⟩

/-- The canonical worst-case conditional residual distance is nonnegative. -/
theorem worstCaseConditionalResidualDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate outputCoordinate : Fin lweDimension) :
    0 ≤ worstCaseConditionalResidualDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate outputCoordinate := by
  classical
  unfold worstCaseConditionalResidualDistance
  apply Finset.le_max'
  simp

/-- Direct sampler form of the canonical worst-case bound. -/
theorem tvDist_residualizedCoordinateSampler_directEntry_le_worstCase [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hcontrol : control ∈ support
      (directEntrySampler params sourceErrorSampler hidden ringSecret coordinate)) :
    tvDist
        (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret
          coordinate control outputCoordinate)
        (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) ≤
      worstCaseConditionalResidualDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate outputCoordinate := by
  exact conditionalResidualDistance_le_worstCase params sourceErrorSampler
    targetErrorSampler coordinate outputCoordinate (hidden, ringSecret, control) hcontrol

/-- Whole-BRK conditional residual normal form with one explicit diagonal exception. -/
noncomputable def residualizedKeyExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) := do
  let control ← directEntrySampler params errorSampler hidden ringSecret coordinate
  Fin.mOfFn lweDimension fun outputCoordinate =>
    residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate

/-- Conditional presentation of a fresh direct BRK after pulling its selected coordinate in
front.  The selected coordinate reuses the sampled control, while every other coordinate is an
independent direct TGSW entry. -/
noncomputable def referenceCoordinateSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  if outputCoordinate = coordinate then pure control
  else directEntrySampler params errorSampler hidden ringSecret outputCoordinate

/-- A fresh direct BRK written with its selected coordinate sampled first. -/
noncomputable def referenceKeyExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) := do
  let control ← directEntrySampler params errorSampler hidden ringSecret coordinate
  Fin.mOfFn lweDimension fun outputCoordinate =>
    referenceCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate

/-- The actual self-correlated output at the selected coordinate, averaged over its fresh source
control.  Unlike a support-wise conditional bound, this marginal retains any cancellation coming
from sampling the control. -/
noncomputable def diagonalExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let control ← directEntrySampler params errorSampler hidden ringSecret coordinate
  factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
    control coordinate

/-- Complete a supplied diagonal entry with fresh independent direct entries at every other
coordinate. -/
noncomputable def completeKeyFromDiagonal [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonal : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :=
  Fin.mOfFn lweDimension fun outputCoordinate =>
    if outputCoordinate = coordinate then pure diagonal
    else directEntrySampler params errorSampler hidden ringSecret outputCoordinate

/-- Conditional whole-key hybrid after replacing only the off-diagonal residual encryptions by
fresh direct entries.  Its diagonal remains the actual self-correlated shifted-CMux output. -/
noncomputable def offDiagonalReplacedCoordinateSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  if outputCoordinate = coordinate then
    factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate
  else directEntrySampler params errorSampler hidden ringSecret outputCoordinate

/-- Whole-key hybrid with the actual diagonal and independently fresh off-diagonal entries. -/
noncomputable def offDiagonalReplacedKeyExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) := do
  let control ← directEntrySampler params errorSampler hidden ringSecret coordinate
  Fin.mOfFn lweDimension fun outputCoordinate =>
    offDiagonalReplacedCoordinateSampler params errorSampler hidden ringSecret
      coordinate control outputCoordinate

/-- Complete a supplied diagonal entry using a possibly different target error sampler at every
other coordinate.  This is the completion kernel needed to compare a source-noise shifted key
with a fresh target-noise BRK. -/
noncomputable def completeTargetKeyFromDiagonal [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonal : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :=
  Fin.mOfFn lweDimension fun outputCoordinate =>
    if outputCoordinate = coordinate then pure diagonal
    else directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate

/-- Conditional whole-key hybrid whose diagonal is the actual source-noise shifted output and
whose off-diagonal entries are fresh direct encryptions under the target error sampler. -/
noncomputable def targetOffDiagonalReplacedCoordinateSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  if outputCoordinate = coordinate then
    factorizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
      control outputCoordinate
  else directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate

/-- Whole-key hybrid with the actual source-noise diagonal and independently fresh target-noise
off-diagonal entries. -/
noncomputable def targetOffDiagonalReplacedKeyExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    ProbComp (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) := do
  let control ← directEntrySampler params sourceErrorSampler hidden ringSecret coordinate
  Fin.mOfFn lweDimension fun outputCoordinate =>
    targetOffDiagonalReplacedCoordinateSampler params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate control outputCoordinate

/-- Actual control-weighted distance between the complete residualized key and the hybrid that
replaces every off-diagonal entry by the target sampler.  Keeping the expectation over the
generated source control is essential: a support-wise maximum can discard the random smoothing
that the native evaluator is meant to provide. -/
noncomputable def averagedOffDiagonalReplacementDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) : ℝ :=
  ∑' control,
    Pr[= control |
      directEntrySampler params sourceErrorSampler hidden ringSecret coordinate].toReal *
      tvDist
        (Fin.mOfFn lweDimension fun outputCoordinate =>
          residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
            control outputCoordinate)
        (Fin.mOfFn lweDimension fun outputCoordinate =>
          targetOffDiagonalReplacedCoordinateSampler params sourceErrorSampler
            targetErrorSampler hidden ringSecret coordinate control outputCoordinate)

theorem averagedOffDiagonalReplacementDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    0 ≤ averagedOffDiagonalReplacementDistance params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate := by
  unfold averagedOffDiagonalReplacementDistance
  exact tsum_nonneg fun _control ↦ mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)

/-- Generated-control average of the explicit residual-vector `L²` budget.  The finite sum over
off-diagonal coordinates records the complete key layout; the selected diagonal is excluded
because it is handled by the separate sharp diagonal reduction. -/
noncomputable def averagedOffDiagonalResidualL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) : ℝ :=
  ∑' control,
    Pr[= control |
      directEntrySampler params sourceErrorSampler hidden ringSecret coordinate].toReal *
      ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
        conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
          (hidden coordinate) ringSecret control

theorem averagedOffDiagonalResidualL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    0 ≤ averagedOffDiagonalResidualL2Loss params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate := by
  unfold averagedOffDiagonalResidualL2Loss
  exact tsum_nonneg fun control =>
    mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ =>
        conditionalResidualErrorL2Loss_nonneg params sourceErrorSampler targetErrorSampler
          (hidden coordinate) ringSecret control)

/-- Generated-control average after eliminating the control ciphertext altogether.  The only
conditioning variable is the independently sampled narrow control-error vector. -/
noncomputable def averagedOffDiagonalErrorOnlyL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (coordinate : Fin lweDimension) : ℝ :=
  ∑' controlError,
    Pr[= controlError |
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler].toReal *
      ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
        errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
          candidate controlError

theorem averagedOffDiagonalErrorOnlyL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (coordinate : Fin lweDimension) :
    0 ≤ averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate coordinate := by
  unfold averagedOffDiagonalErrorOnlyL2Loss
  exact tsum_nonneg fun controlError ↦
    mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun _ _ ↦
        errorOnlyResidualL2Loss_nonneg params sourceErrorSampler targetErrorSampler
          candidate controlError)

/-- Fully finite form of the generated-control average.  The outer expectation is the uniform
average over centered-binomial control coins; every inner loss is the exact fiber count above. -/
noncomputable def averagedCenteredBinomialResidualFiberL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (coordinate : Fin lweDimension) : ℝ :=
  let ControlCoins := RLWE.CenteredBinomial.ErrorVectorCoinTable
    (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  (Fintype.card ControlCoins : ℝ)⁻¹ *
    ∑ controlCoins : ControlCoins,
      ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
        centeredBinomialResidualFiberL2Loss params eta certificate candidate
          (RLWE.CenteredBinomial.errorVectorFromCoins q
            (TGSW.rowCount ringRank params.levels) (degree + 1) eta controlCoins)

/-- The generated-control residual `L²` expectation equals one explicit finite average of
explicit finite fiber-cardinality losses. -/
theorem averagedOffDiagonalErrorOnlyL2Loss_centeredBinomial_ringSampler_eq_fiber [NeZero q]
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        candidate coordinate =
      averagedCenteredBinomialResidualFiberL2Loss (degree := degree)
        (ringRank := ringRank)
        params eta certificate candidate coordinate := by
  let ControlCoins := RLWE.CenteredBinomial.ErrorVectorCoinTable
    (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  let decode := RLWE.CenteredBinomial.errorVectorFromCoins q
    (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  let cost := fun
      controlError : OffDiagonalErrorVector q degree ringRank params.levels ↦
    ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
      centeredBinomialResidualFiberL2Loss params eta certificate
        candidate controlError
  have hCost : ∀ controlError, 0 ≤ cost controlError := by
    intro controlError
    exact Finset.sum_nonneg fun _ _ ↦
      centeredBinomialResidualFiberL2Loss_nonneg
        (ringRank := ringRank) params eta certificate candidate controlError
  have hControl := RLWE.CenteredBinomial.sampleIID_sampler_evalDist_eq_uniformCoins
    q (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  have hMap := FormalProof4FHE.FiniteProduct.tsum_probOutput_map_toReal_mul
    ($ᵗ ControlCoins) decode cost hCost
  unfold averagedOffDiagonalErrorOnlyL2Loss
  simp_rw [errorOnlyResidualL2Loss_centeredBinomial_ringSampler_eq_fiber
    (ringRank := ringRank) params eta certificate candidate]
  change
    (∑' controlError,
      Pr[= controlError |
        ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)].toReal *
        cost controlError) = _
  calc
    _ = ∑' controlError,
        Pr[= controlError | decode <$> ($ᵗ ControlCoins)].toReal *
          cost controlError :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr
        hControl cost
    _ = ∑' controlCoins,
        Pr[= controlCoins | $ᵗ ControlCoins].toReal * cost (decode controlCoins) := hMap
    _ = (Fintype.card ControlCoins : ℝ)⁻¹ *
        ∑ controlCoins : ControlCoins, cost (decode controlCoins) := by
      rw [tsum_fintype]
      simp_rw [probOutput_uniformSample, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      rw [Finset.mul_sum]
    _ = _ := by
      rfl

/-- Exact candidate-sign invariance of the error-only expectation for every negation-symmetric
source-error sampler. -/
theorem averagedOffDiagonalErrorOnlyL2Loss_true_eq_false_of_negationSymmetric [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hSymmetric : Native.ScalarSecretRandomization.NegationSymmetric sourceErrorSampler)
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler true coordinate =
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler false coordinate := by
  let Errors : ProbComp (OffDiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let trueCost := fun
      controlError : OffDiagonalErrorVector q degree ringRank params.levels =>
    ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
      errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
        true controlError
  let falseCost := fun
      controlError : OffDiagonalErrorVector q degree ringRank params.levels =>
    ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
      errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
        false controlError
  have hFalseCost : ∀ controlError, 0 ≤ falseCost controlError := by
    intro controlError
    exact Finset.sum_nonneg fun _ _ =>
      errorOnlyResidualL2Loss_nonneg params sourceErrorSampler targetErrorSampler
        false controlError
  have hPoint : ∀ controlError, trueCost controlError = falseCost (-controlError) := by
    intro controlError
    unfold trueCost falseCost
    apply Finset.sum_congr rfl
    intro outputCoordinate hOutputCoordinate
    exact errorOnlyResidualL2Loss_true_eq_false_neg params
      sourceErrorSampler targetErrorSampler controlError
  have hNegation :
      evalDist
          ((fun controlError : OffDiagonalErrorVector q degree ringRank params.levels =>
              -controlError) <$> Errors) =
        evalDist Errors := by
    simpa only [Errors] using
      (Native.ScalarSecretRandomization.negate_sampleIID_evalDist
        (TGSW.rowCount ringRank params.levels) sourceErrorSampler hSymmetric)
  change
    (∑' controlError, Pr[= controlError | Errors].toReal * trueCost controlError) =
      ∑' controlError, Pr[= controlError | Errors].toReal * falseCost controlError
  calc
    _ = ∑' controlError,
        Pr[= controlError | Errors].toReal * falseCost (-controlError) := by
      exact tsum_congr fun controlError => congrArg
        (fun cost => Pr[= controlError | Errors].toReal * cost) (hPoint controlError)
    _ = ∑' controlError,
        Pr[= controlError |
          (fun error : OffDiagonalErrorVector q degree ringRank params.levels => -error) <$>
            Errors].toReal * falseCost controlError :=
      (FormalProof4FHE.FiniteProduct.tsum_probOutput_map_toReal_mul
        Errors (fun error => -error) falseCost hFalseCost).symm
    _ = ∑' controlError,
        Pr[= controlError | Errors].toReal * falseCost controlError :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr
        hNegation falseCost

/-- Centered-binomial specialization of exact candidate-sign invariance. -/
theorem averagedOffDiagonalErrorOnlyL2Loss_true_eq_false_centeredBinomial [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (eta : ℕ)
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetErrorSampler true coordinate =
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetErrorSampler false coordinate :=
  averagedOffDiagonalErrorOnlyL2Loss_true_eq_false_of_negationSymmetric
    (ringRank := ringRank) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) targetErrorSampler
    (RLWE.CenteredBinomial.probOutput_neg q (degree + 1) eta) coordinate

/-- The generated-control ciphertext expectation is exactly the error-only expectation.  Thus
the analytic off-diagonal obligation is independent of the ring secret, public control masks,
and gadget messages. -/
theorem averagedOffDiagonalResidualL2Loss_eq_errorOnly [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalResidualL2Loss params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate =
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) coordinate := by
  let Candidate := hidden coordinate
  let Direct := directEntrySampler params sourceErrorSampler hidden ringSecret coordinate
  let Witness := structuredControlWitnessSampler (ringRank := ringRank)
    params sourceErrorSampler
  let assemble := structuredControlFromWitness params Candidate ringSecret
  let ControlErrors :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let controlCost := fun
      control : RingGSWCiphertext q (degree + 1) ringRank params.levels ↦
    ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
      conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
        Candidate ringSecret control
  let errorCost := fun
      controlError : OffDiagonalErrorVector q degree ringRank params.levels ↦
    ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
      errorOnlyResidualL2Loss params sourceErrorSampler targetErrorSampler
        Candidate controlError
  have hDirect : evalDist Direct = evalDist (assemble <$> Witness) := by
    simpa only [Direct, Witness, assemble, Candidate, directEntrySampler] using
      (structuredControlWitnessSampler_evalDist_eq_directEncrypt
        (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) ringSecret).symm
  have hControlCost : ∀ control, 0 ≤ controlCost control := by
    intro control
    exact Finset.sum_nonneg fun _ _ ↦
      conditionalResidualErrorL2Loss_nonneg params sourceErrorSampler targetErrorSampler
        Candidate ringSecret control
  have hErrorCost : ∀ controlError, 0 ≤ errorCost controlError := by
    intro controlError
    exact Finset.sum_nonneg fun _ _ ↦
      errorOnlyResidualL2Loss_nonneg params sourceErrorSampler targetErrorSampler
        Candidate controlError
  have hPoint : ∀ witness, controlCost (assemble witness) = errorCost witness.2 := by
    intro witness
    unfold controlCost errorCost assemble Candidate
    apply Finset.sum_congr rfl
    intro outputCoordinate hOutputCoordinate
    exact conditionalResidualErrorL2Loss_structured_eq_errorOnly params
      sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret witness
  have hProjection : evalDist (Prod.snd <$> Witness) = evalDist ControlErrors := by
    simpa only [Witness, ControlErrors] using
      (structuredControlWitnessSampler_snd_evalDist
        (ringRank := ringRank) params sourceErrorSampler)
  change
    (∑' control, Pr[= control | Direct].toReal * controlCost control) =
      ∑' controlError,
        Pr[= controlError | ControlErrors].toReal * errorCost controlError
  calc
    _ = ∑' control,
        Pr[= control | assemble <$> Witness].toReal * controlCost control :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr
        hDirect controlCost
    _ = ∑' witness,
        Pr[= witness | Witness].toReal * controlCost (assemble witness) :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_map_toReal_mul
        Witness assemble controlCost hControlCost
    _ = ∑' witness,
        Pr[= witness | Witness].toReal * errorCost witness.2 := by
      exact tsum_congr fun witness ↦ congrArg
        (fun cost ↦ Pr[= witness | Witness].toReal * cost) (hPoint witness)
    _ = ∑' controlError,
        Pr[= controlError | Prod.snd <$> Witness].toReal * errorCost controlError :=
      (FormalProof4FHE.FiniteProduct.tsum_probOutput_map_toReal_mul
        Witness Prod.snd errorCost hErrorCost).symm
    _ = ∑' controlError,
        Pr[= controlError | ControlErrors].toReal * errorCost controlError :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr
        hProjection errorCost

/-- The original generated-control ciphertext-level expectation is bounded by the fully exposed
residual-vector `L²` expression. -/
theorem averagedOffDiagonalReplacementDistance_le_residualL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalReplacementDistance params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate ≤
      averagedOffDiagonalResidualL2Loss params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate := by
  let Residualized := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
      control outputCoordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    targetOffDiagonalReplacedCoordinateSampler params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate control outputCoordinate
  let loss := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    conditionalResidualErrorL2Loss params sourceErrorSampler targetErrorSampler
      (hidden coordinate) ringSecret control
  unfold averagedOffDiagonalReplacementDistance averagedOffDiagonalResidualL2Loss
  apply Summable.tsum_le_tsum
  · intro control
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    calc
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Replaced control)) ≤
          ∑ outputCoordinate,
            tvDist (Residualized control outputCoordinate)
              (Replaced control outputCoordinate) :=
        FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
          lweDimension (Residualized control) (Replaced control)
      _ ≤ ∑ outputCoordinate : Fin lweDimension,
          if outputCoordinate = coordinate then 0 else loss control := by
        apply Finset.sum_le_sum
        intro outputCoordinate _
        by_cases hCoordinate : outputCoordinate = coordinate
        · subst outputCoordinate
          simp [Residualized, Replaced, residualizedCoordinateSampler,
            targetOffDiagonalReplacedCoordinateSampler, tvDist_self]
        · simpa only [Residualized, Replaced,
            targetOffDiagonalReplacedCoordinateSampler, if_neg hCoordinate, loss] using
            (tvDist_residualizedCoordinateSampler_directEntry_le_residualL2
              params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
              outputCoordinate control hCoordinate)
      _ = ∑ _outputCoordinate ∈ Finset.univ.erase coordinate, loss control := by
        rw [← Finset.add_sum_erase Finset.univ
          (fun outputCoordinate : Fin lweDimension =>
            if outputCoordinate = coordinate then 0 else loss control)
          (Finset.mem_univ coordinate)]
        simp only [if_pos, zero_add]
        apply Finset.sum_congr rfl
        intro outputCoordinate hOutput
        rw [if_neg (Finset.ne_of_mem_erase hOutput)]
  · exact Summable.of_finite
  · exact Summable.of_finite

/-- Direct error-only version of the generated-control off-diagonal bound. -/
theorem averagedOffDiagonalReplacementDistance_le_errorOnlyL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalReplacementDistance params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate ≤
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) coordinate := by
  calc
    _ ≤ averagedOffDiagonalResidualL2Loss params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate :=
      averagedOffDiagonalReplacementDistance_le_residualL2Loss params
        sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
    _ = _ := averagedOffDiagonalResidualL2Loss_eq_errorOnly params
      sourceErrorSampler targetErrorSampler hidden ringSecret coordinate

/-- Convexity bounds the complete off-diagonal replacement hop by its exact generated-control
expectation. -/
theorem tvDist_residualizedKeyExperiment_targetOffDiagonalReplaced_le_expectation [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (residualizedKeyExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
          hidden ringSecret coordinate) ≤
      averagedOffDiagonalReplacementDistance params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate := by
  let Control := directEntrySampler params sourceErrorSampler hidden ringSecret coordinate
  let Residualized := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    Fin.mOfFn lweDimension fun outputCoordinate =>
      residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
        control outputCoordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    Fin.mOfFn lweDimension fun outputCoordinate =>
      targetOffDiagonalReplacedCoordinateSampler params sourceErrorSampler
        targetErrorSampler hidden ringSecret coordinate control outputCoordinate
  simpa only [residualizedKeyExperiment, targetOffDiagonalReplacedKeyExperiment,
    averagedOffDiagonalReplacementDistance, Control, Residualized, Replaced] using
      (FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation Control
        Residualized Replaced)

/-- Finite secret pair over which the adaptive correct-view theorem needs a uniform bound. -/
abbrev SecretPairWitness :=
  BinarySecret lweDimension × RingBinarySecret ringRank (degree + 1)

/-- Worst generated-control expectation over the finite native scalar/ring secret space. -/
noncomputable def worstCaseAveragedOffDiagonalReplacementDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) : ℝ := by
  classical
  exact (insert 0
    ((Finset.univ : Finset
      (SecretPairWitness (degree := degree) (ringRank := ringRank)
        (lweDimension := lweDimension))).image fun secrets ↦
      averagedOffDiagonalReplacementDistance params sourceErrorSampler targetErrorSampler
        secrets.1 secrets.2 coordinate)).max' (by simp)

/-- Worst generated-control residual `L²` budget over the finite native secret pair.  This is the
preferred off-diagonal analytic quantity: it contains only the effective error-vector masses and
the exact polynomial key-layout sum. -/
noncomputable def worstCaseAveragedOffDiagonalResidualL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) : ℝ := by
  classical
  exact (insert 0
    ((Finset.univ : Finset
      (SecretPairWitness (degree := degree) (ringRank := ringRank)
        (lweDimension := lweDimension))).image fun secrets =>
      averagedOffDiagonalResidualL2Loss params sourceErrorSampler targetErrorSampler
        secrets.1 secrets.2 coordinate)).max' (by simp)

/-- Worst error-only generated-control loss.  Only the selected plaintext bit remains to be
maximized; all scalar/ring secrets and public control masks have been eliminated. -/
noncomputable def worstCaseAveragedOffDiagonalErrorOnlyL2Loss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) : ℝ := by
  classical
  exact (insert 0
    ((Finset.univ : Finset Bool).image fun candidate =>
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate coordinate)).max' (by simp)

theorem averagedOffDiagonalReplacementDistance_le_worstCase [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalReplacementDistance params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate ≤
      worstCaseAveragedOffDiagonalReplacementDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalReplacementDistance
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(hidden, ringSecret), Finset.mem_univ _, rfl⟩

theorem averagedOffDiagonalResidualL2Loss_le_worstCase [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalResidualL2Loss params sourceErrorSampler targetErrorSampler
        hidden ringSecret coordinate ≤
      worstCaseAveragedOffDiagonalResidualL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalResidualL2Loss
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(hidden, ringSecret), Finset.mem_univ _, rfl⟩

theorem averagedOffDiagonalErrorOnlyL2Loss_le_worstCase [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (coordinate : Fin lweDimension) :
    averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate coordinate ≤
      worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalErrorOnlyL2Loss
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨candidate, Finset.mem_univ _, rfl⟩

theorem worstCaseAveragedOffDiagonalReplacementDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) :
    0 ≤ worstCaseAveragedOffDiagonalReplacementDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalReplacementDistance
  apply Finset.le_max'
  simp

theorem worstCaseAveragedOffDiagonalResidualL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) :
    0 ≤ worstCaseAveragedOffDiagonalResidualL2Loss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalResidualL2Loss
  apply Finset.le_max'
  simp

theorem worstCaseAveragedOffDiagonalErrorOnlyL2Loss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) :
    0 ≤ worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalErrorOnlyL2Loss
  apply Finset.le_max'
  simp

/-- Under negation-symmetric source noise, the Boolean worst case is exactly the `false` branch;
the `true` branch is its negation reindexing. -/
theorem worstCaseAveragedOffDiagonalErrorOnlyL2Loss_eq_false_of_negationSymmetric [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hSymmetric : Native.ScalarSecretRandomization.NegationSymmetric sourceErrorSampler)
    (coordinate : Fin lweDimension) :
    worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate =
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler false coordinate := by
  classical
  apply le_antisymm
  · unfold worstCaseAveragedOffDiagonalErrorOnlyL2Loss
    apply Finset.max'_le
    intro value hValue
    rcases Finset.mem_insert.mp hValue with rfl | hValue
    · exact averagedOffDiagonalErrorOnlyL2Loss_nonneg
        (ringRank := ringRank) params sourceErrorSampler targetErrorSampler false coordinate
    · rcases Finset.mem_image.mp hValue with ⟨candidate, _hCandidate, rfl⟩
      cases candidate with
      | false => exact le_rfl
      | true =>
          rw [averagedOffDiagonalErrorOnlyL2Loss_true_eq_false_of_negationSymmetric
            (ringRank := ringRank) params sourceErrorSampler targetErrorSampler
            hSymmetric coordinate]
  · exact averagedOffDiagonalErrorOnlyL2Loss_le_worstCase
      (ringRank := ringRank) params sourceErrorSampler targetErrorSampler false coordinate

/-- Centered-binomial specialization: no candidate maximum remains. -/
theorem worstCaseAveragedOffDiagonalErrorOnlyL2Loss_centeredBinomial_eq_false [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (eta : ℕ)
    (coordinate : Fin lweDimension) :
    worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetErrorSampler coordinate =
      averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetErrorSampler false coordinate :=
  worstCaseAveragedOffDiagonalErrorOnlyL2Loss_eq_false_of_negationSymmetric
    (ringRank := ringRank) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) targetErrorSampler
    (RLWE.CenteredBinomial.probOutput_neg q (degree + 1) eta) coordinate

/-- Eliminating honest control ciphertexts can only shrink the finite maximization domain: the
old secret-pair maximum is bounded by the new Boolean-only maximum. -/
theorem worstCaseAveragedOffDiagonalResidualL2Loss_le_errorOnly [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (coordinate : Fin lweDimension) :
    worstCaseAveragedOffDiagonalResidualL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate ≤
      worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler coordinate := by
  classical
  unfold worstCaseAveragedOffDiagonalResidualL2Loss
  apply Finset.max'_le
  intro value hValue
  rcases Finset.mem_insert.mp hValue with rfl | hValue
  · exact worstCaseAveragedOffDiagonalErrorOnlyL2Loss_nonneg
      (ringRank := ringRank) params sourceErrorSampler targetErrorSampler coordinate
  · rcases Finset.mem_image.mp hValue with ⟨secrets, _hSecrets, rfl⟩
    rw [averagedOffDiagonalResidualL2Loss_eq_errorOnly]
    exact averagedOffDiagonalErrorOnlyL2Loss_le_worstCase
      (ringRank := ringRank) params sourceErrorSampler targetErrorSampler
      (secrets.1 coordinate) coordinate

/-- Explicit independent-base form of the off-diagonal experiment. -/
noncomputable def factorizedEntryExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let base ← directEntrySampler params errorSampler hidden ringSecret outputCoordinate
  let perturbation ← perturbationSampler params errorSampler hidden ringSecret coordinate
  return TGSW.add base perturbation

/-- Residual-encryption form of the same off-diagonal experiment. -/
noncomputable def residualEntryExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let perturbation ← perturbationSampler params errorSampler hidden ringSecret coordinate
  TGSW.directEncryptWithResidual ringRank params.levels errorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden outputCoordinate))
    (TLWE.batchPhase (embedRingSecret q ringSecret) perturbation)

/-- Distinct native BRK entries factor into independent direct TGSW samplers before any
continuation using only those entries. -/
theorem generateDirectBootstrappingKey_two_coordinates_evalDist [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (first second : Fin lweDimension) (hne : first ≠ second)
    (hError : Pr[⊥ | errorSampler] = 0)
    (finish :
      RingGSWCiphertext q (degree + 1) ringRank params.levels →
      RingGSWCiphertext q (degree + 1) ringRank params.levels →
      ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels)) :
    evalDist (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
        ringRank params.levels lweDimension errorSampler
        (Gadget.Base.ringGadget params) hidden ringSecret >>= fun source =>
      finish (source first) (source second)) =
      evalDist (directEntrySampler params errorSampler hidden ringSecret first >>= fun firstEntry =>
        directEntrySampler params errorSampler hidden ringSecret second >>= fun secondEntry =>
          finish firstEntry secondEntry) := by
  let samplers := fun index : Fin lweDimension =>
    directEntrySampler params errorSampler hidden ringSecret index
  have hSamplers : ∀ index, Pr[⊥ | samplers index] = 0 := by
    intro index
    exact TGSW.Translation.probFailure_directEncrypt_eq_zero
      ringRank params.levels errorSampler (embedRingSecret q ringSecret)
      (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) (hidden index)) hError
  simpa only [BootstrapSecurity.generateDirectBootstrappingKey,
    directEntrySampler, samplers] using
    (FormalProof4FHE.FiniteProduct.evalDist_bind_fin_mOfFn_two_coordinates
      lweDimension samplers first second hne hSamplers finish)

/-- For an off-diagonal output, the retained fresh source entry is independent of both the
selected control entry and the uniform difference entry. -/
theorem correctEntryExperiment_evalDist_eq_factorized [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (hne : outputCoordinate ≠ coordinate)
    (hError : Pr[⊥ | errorSampler] = 0) :
    evalDist (correctEntryExperiment params errorSampler hidden ringSecret
        coordinate outputCoordinate) =
      evalDist (factorizedEntryExperiment params errorSampler hidden ringSecret
        coordinate outputCoordinate) := by
  let Source := BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension errorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let Difference :=
    $ᵗ BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let DifferenceEntry :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let finish := fun
      (base control : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    DifferenceEntry >>= fun differenceEntry =>
      pure (TGSW.add base
        (controlPerturbation params (hidden coordinate) control differenceEntry))
  have hEndpoint :
      evalDist (correctEntryExperiment params errorSampler hidden ringSecret
          coordinate outputCoordinate) =
        evalDist (Source >>= fun source =>
          Difference >>= fun difference =>
            pure (TGSW.add (source outputCoordinate)
              (controlPerturbation params (hidden coordinate) (source coordinate)
                (difference outputCoordinate)))) := by
    unfold correctEntryExperiment Source Difference
    simp_rw [selectBootstrappingKey_correct_add_controlPerturbation]
  rw [hEndpoint]
  have hDifference : evalDist (Source >>= fun source =>
      Difference >>= fun difference =>
        pure (TGSW.add (source outputCoordinate)
          (controlPerturbation params (hidden coordinate) (source coordinate)
            (difference outputCoordinate)))) =
      evalDist (Source >>= fun source =>
        DifferenceEntry >>= fun differenceEntry =>
          pure (TGSW.add (source outputCoordinate)
            (controlPerturbation params (hidden coordinate) (source coordinate)
              differenceEntry))) := by
    refine evalDist_bind_congr' Source fun source => ?_
    let postprocess := fun
        differenceEntry : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
      TGSW.add (source outputCoordinate)
        (controlPerturbation params (hidden coordinate) (source coordinate)
          differenceEntry)
    have hProjection :=
      FormalProof4FHE.FiniteProduct.evalDist_map_apply_uniformSample_fun
        (domain := Fin lweDimension)
        (codomain := RingGSWCiphertext q (degree + 1) ringRank params.levels)
        outputCoordinate
    have hMapped := evalDist_map_eq_of_evalDist_eq hProjection postprocess
    simpa only [Difference, DifferenceEntry, map_eq_bind_pure_comp,
      Function.comp_apply, Function.comp_def, bind_assoc, pure_bind] using hMapped
  rw [hDifference]
  have hSource := generateDirectBootstrappingKey_two_coordinates_evalDist
    params errorSampler hidden ringSecret outputCoordinate coordinate hne hError finish
  simpa only [Source, DifferenceEntry, finish, factorizedEntryExperiment,
    perturbationSampler, bind_assoc, pure_bind] using hSource

/-- Exact whole-BRK conditional factorization.  This simultaneously exposes every off-diagonal
base as fresh and independent while retaining the sole diagonal self-correlation explicitly. -/
theorem correctKeyExperiment_evalDist_eq_factorized [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (correctKeyExperiment params errorSampler hidden ringSecret coordinate) =
      evalDist (factorizedKeyExperiment params errorSampler hidden ringSecret coordinate) := by
  let Entry := fun outputCoordinate : Fin lweDimension =>
    directEntrySampler params errorSampler hidden ringSecret outputCoordinate
  let Source := Fin.mOfFn lweDimension Entry
  let Difference :=
    $ᵗ BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  let DifferenceEntry :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let fixed := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    if outputCoordinate = coordinate then pure control else Entry outputCoordinate
  let process := fun
      (control sourceEntry : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    DifferenceEntry >>= fun differenceEntry =>
      pure (TGSW.add sourceEntry
        (controlPerturbation params (hidden coordinate) control differenceEntry))
  let finish := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (source : BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) =>
    Difference >>= fun difference =>
      pure (fun outputCoordinate =>
        TGSW.add (source outputCoordinate)
          (controlPerturbation params (hidden coordinate) control
            (difference outputCoordinate)))
  have hEndpoint :
      correctKeyExperiment params errorSampler hidden ringSecret coordinate =
        (Source >>= fun source => finish (source coordinate) source) := by
    unfold correctKeyExperiment Source Entry finish Difference
    apply bind_congr
    intro source
    apply bind_congr
    intro difference
    apply congrArg (fun key : BootstrappingKey q (degree + 1) ringRank
      params.levels lweDimension =>
        (pure key : ProbComp
          (BootstrappingKey q (degree + 1) ringRank params.levels lweDimension)))
    funext outputCoordinate
    exact selectBootstrappingKey_correct_add_controlPerturbation
      params hidden coordinate outputCoordinate source difference
  rw [hEndpoint]
  have hPull :=
    FormalProof4FHE.FiniteProduct.evalDist_bind_fin_mOfFn_pull_coordinate
      lweDimension Entry coordinate finish
  rw [hPull]
  refine evalDist_bind_congr' (Entry coordinate) fun control => ?_
  have hDifference (source :
      BootstrappingKey q (degree + 1) ringRank params.levels lweDimension) :
      evalDist (finish control source) =
        evalDist (Fin.mOfFn lweDimension fun outputCoordinate =>
          process control (source outputCoordinate)) := by
    let transform := fun
        (difference : BootstrappingKey q (degree + 1) ringRank
          params.levels lweDimension)
        (outputCoordinate : Fin lweDimension) =>
      TGSW.add (source outputCoordinate)
        (controlPerturbation params (hidden coordinate) control
          (difference outputCoordinate))
    have hUniform := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := RingGSWCiphertext q (degree + 1) ringRank params.levels) lweDimension
    have hMapped := evalDist_map_eq_of_evalDist_eq hUniform.symm transform
    simp only [ProbComp.sampleIID, transform] at hMapped
    have hProduct := FormalProof4FHE.FiniteProduct.map_fin_mOfFn
      lweDimension (fun _ => DifferenceEntry)
      (fun outputCoordinate differenceEntry =>
        TGSW.add (source outputCoordinate)
          (controlPerturbation params (hidden coordinate) control differenceEntry))
    rw [hProduct] at hMapped
    simpa only [finish, Difference, DifferenceEntry, process,
      map_eq_bind_pure_comp, Function.comp_apply,
      Function.comp_def, bind_assoc, pure_bind] using hMapped
  calc
    _ = evalDist (Fin.mOfFn lweDimension (fixed control) >>= fun source =>
        Fin.mOfFn lweDimension fun outputCoordinate =>
          process control (source outputCoordinate)) := by
      refine evalDist_bind_congr' (Fin.mOfFn lweDimension (fixed control)) fun source => ?_
      exact hDifference source
    _ = evalDist (Fin.mOfFn lweDimension fun outputCoordinate =>
        fixed control outputCoordinate >>= process control) :=
      FormalProof4FHE.FiniteProduct.evalDist_presample_fin_mOfFn
        lweDimension (fixed control) (fun _ => process control)
    _ = _ := by
      apply congrArg evalDist
      apply congrArg (Fin.mOfFn lweDimension)
      funext outputCoordinate
      by_cases hCoordinate : outputCoordinate = coordinate
      · simp [factorizedCoordinateSampler, Entry, fixed, process, DifferenceEntry,
          hCoordinate]
      · simp [factorizedCoordinateSampler, Entry, fixed, process, DifferenceEntry,
          hCoordinate]

/-- Simultaneous exact residualization of every off-diagonal coordinate, conditional on the
shared selected control. -/
theorem factorizedKeyExperiment_evalDist_eq_residualized [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (factorizedKeyExperiment params errorSampler hidden ringSecret coordinate) =
      evalDist (residualizedKeyExperiment params errorSampler hidden ringSecret coordinate) := by
  unfold factorizedKeyExperiment residualizedKeyExperiment
  refine evalDist_bind_congr'
    (directEntrySampler params errorSampler hidden ringSecret coordinate) fun control => ?_
  apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
  intro outputCoordinate
  by_cases hCoordinate : outputCoordinate = coordinate
  · simp only [residualizedCoordinateSampler, if_pos hCoordinate]
  · have hTranslation := TGSW.Translation.add_independent_directEncrypt_evalDist
      ringRank params.levels errorSampler (embedRingSecret q ringSecret)
      (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) (hidden outputCoordinate))
      (fixedControlPerturbationSampler params (hidden coordinate) control)
    simpa only [factorizedCoordinateSampler, residualizedCoordinateSampler,
      fixedControlPerturbationSampler, directEntrySampler, if_neg hCoordinate,
      bind_assoc, pure_bind] using hTranslation

/-- The complete correct shifted-CMux BRK experiment has the residualized conditional normal
form, with no distributional premise outside the singled-out diagonal coordinate. -/
theorem correctKeyExperiment_evalDist_eq_residualized [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (correctKeyExperiment params errorSampler hidden ringSecret coordinate) =
      evalDist (residualizedKeyExperiment params errorSampler hidden ringSecret coordinate) :=
  (correctKeyExperiment_evalDist_eq_factorized params errorSampler hidden ringSecret
      coordinate).trans
    (factorizedKeyExperiment_evalDist_eq_residualized params errorSampler hidden ringSecret
      coordinate)

/-- Pulling one coordinate in front of a fresh direct BRK does not change its distribution. -/
theorem referenceKeyExperiment_evalDist_eq_generateDirectBootstrappingKey [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (referenceKeyExperiment params errorSampler hidden ringSecret coordinate) =
      evalDist (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
        ringRank params.levels lweDimension errorSampler
        (Gadget.Base.ringGadget params) hidden ringSecret) := by
  let Entry := fun outputCoordinate : Fin lweDimension =>
    directEntrySampler params errorSampler hidden ringSecret outputCoordinate
  simpa only [referenceKeyExperiment, referenceCoordinateSampler, Entry,
    BootstrapSecurity.generateDirectBootstrappingKey, directEntrySampler] using
    (FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
      lweDimension Entry coordinate)

/-- The off-diagonal-replaced whole key is exactly the averaged diagonal marginal followed by
fresh independent completion of all remaining coordinates. -/
theorem offDiagonalReplacedKeyExperiment_evalDist_eq_diagonalCompletion [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (offDiagonalReplacedKeyExperiment params errorSampler hidden ringSecret
        coordinate) =
      evalDist (diagonalExperiment params errorSampler hidden ringSecret coordinate >>=
        completeKeyFromDiagonal params errorSampler hidden ringSecret coordinate) := by
  let Control := directEntrySampler params errorSampler hidden ringSecret coordinate
  let Diagonal := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control coordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    offDiagonalReplacedCoordinateSampler params errorSampler hidden ringSecret
      coordinate control outputCoordinate
  unfold offDiagonalReplacedKeyExperiment diagonalExperiment
  simp only [bind_assoc]
  refine evalDist_bind_congr' Control fun control => ?_
  have hPull := FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    lweDimension (Replaced control) coordinate
  have hAtCoordinate : Replaced control coordinate = Diagonal control := by
    simp only [Replaced, Diagonal, offDiagonalReplacedCoordinateSampler, if_pos]
  rw [hAtCoordinate] at hPull
  calc
    _ = evalDist (Diagonal control >>= fun diagonal =>
        Fin.mOfFn lweDimension fun outputCoordinate =>
          if outputCoordinate = coordinate then pure diagonal
          else Replaced control outputCoordinate) := hPull.symm
    _ = _ := by
      refine evalDist_bind_congr' (Diagonal control) fun diagonal => ?_
      apply congrArg evalDist
      apply congrArg (Fin.mOfFn lweDimension)
      funext outputCoordinate
      by_cases hCoordinate : outputCoordinate = coordinate
      · simp [hCoordinate]
      · simp [Replaced,
          offDiagonalReplacedCoordinateSampler, hCoordinate]

/-- Replacing every off-diagonal residual encryption by its fresh direct counterpart costs only
the sum of the corresponding support-wise conditional distances; the diagonal is unchanged and
contributes zero to this hop. -/
theorem tvDist_residualizedKeyExperiment_offDiagonalReplaced_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (offDiagonalError : Fin lweDimension → ℝ)
    (hOffDiagonal : ∀ control ∈ support
        (directEntrySampler params errorSampler hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
              control outputCoordinate)
            (directEntrySampler params errorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (residualizedKeyExperiment params errorSampler hidden ringSecret coordinate)
        (offDiagonalReplacedKeyExperiment params errorSampler hidden ringSecret coordinate) ≤
      ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
        offDiagonalError outputCoordinate := by
  let Control := directEntrySampler params errorSampler hidden ringSecret coordinate
  let Residualized := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    offDiagonalReplacedCoordinateSampler params errorSampler hidden ringSecret
      coordinate control outputCoordinate
  let bound := ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
    offDiagonalError outputCoordinate
  have hConditional (control) (hcontrol : control ∈ support Control) :
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Replaced control)) ≤ bound := by
    calc
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Replaced control)) ≤
          ∑ outputCoordinate,
            tvDist (Residualized control outputCoordinate)
              (Replaced control outputCoordinate) :=
        FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
          lweDimension (Residualized control) (Replaced control)
      _ ≤ ∑ outputCoordinate : Fin lweDimension,
          if outputCoordinate = coordinate then 0
          else offDiagonalError outputCoordinate := by
        apply Finset.sum_le_sum
        intro outputCoordinate _
        by_cases hCoordinate : outputCoordinate = coordinate
        · subst outputCoordinate
          simp [Residualized, Replaced, residualizedCoordinateSampler,
            offDiagonalReplacedCoordinateSampler, tvDist_self]
        · simpa only [Residualized, Replaced,
            offDiagonalReplacedCoordinateSampler, if_neg hCoordinate] using
            hOffDiagonal control hcontrol outputCoordinate hCoordinate
      _ = bound := by
        rw [← Finset.add_sum_erase Finset.univ
          (fun outputCoordinate : Fin lweDimension =>
            if outputCoordinate = coordinate then 0
            else offDiagonalError outputCoordinate)
          (Finset.mem_univ coordinate)]
        simp only [if_pos, zero_add]
        apply Finset.sum_congr rfl
        intro outputCoordinate hOutput
        rw [if_neg (Finset.ne_of_mem_erase hOutput)]
  have hMixture := tvDist_bind_left_le_const (m := ProbComp) Control
    (fun control => Fin.mOfFn lweDimension (Residualized control))
    (fun control => Fin.mOfFn lweDimension (Replaced control))
    bound hConditional
  simpa only [residualizedKeyExperiment, offDiagonalReplacedKeyExperiment,
    Control, Residualized, Replaced, bound] using hMixture

/-- Independent completion cannot increase the distance between the averaged self-correlated
diagonal and one fresh direct entry. -/
theorem tvDist_offDiagonalReplacedKeyExperiment_referenceKeyExperiment_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (offDiagonalReplacedKeyExperiment params errorSampler hidden ringSecret coordinate)
        (referenceKeyExperiment params errorSampler hidden ringSecret coordinate) ≤
      tvDist
        (diagonalExperiment params errorSampler hidden ringSecret coordinate)
        (directEntrySampler params errorSampler hidden ringSecret coordinate) := by
  let Control := directEntrySampler params errorSampler hidden ringSecret coordinate
  let Completion := completeKeyFromDiagonal params errorSampler hidden ringSecret coordinate
  have hDataProcessing := tvDist_bind_right_le (m := ProbComp)
    Completion
    (diagonalExperiment params errorSampler hidden ringSecret coordinate)
    Control
  have hReference :
      evalDist (referenceKeyExperiment params errorSampler hidden ringSecret coordinate) =
        evalDist (Control >>= Completion) := by
    rfl
  unfold tvDist at hDataProcessing ⊢
  rw [offDiagonalReplacedKeyExperiment_evalDist_eq_diagonalCompletion
    params errorSampler hidden ringSecret coordinate, hReference]
  exact hDataProcessing

/-- **Sharpened whole-BRK diagonal isolation.**  The exceptional diagonal is charged only by
the distance of its averaged self-correlated marginal from one fresh direct entry.  No
support-wise worst-case diagonal bound is required.  All remaining costs are the conditionally
independent off-diagonal residual replacements. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_averagedDiagonal
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ) (offDiagonalError : Fin lweDimension → ℝ)
    (hDiagonal :
      tvDist
          (diagonalExperiment params errorSampler hidden ringSecret coordinate)
          (directEntrySampler params errorSampler hidden ringSecret coordinate) ≤
        diagonalError)
    (hOffDiagonal : ∀ control ∈ support
        (directEntrySampler params errorSampler hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
              control outputCoordinate)
            (directEntrySampler params errorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (correctKeyExperiment params errorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension errorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      diagonalError +
        ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
          offDiagonalError outputCoordinate := by
  let Residualized :=
    residualizedKeyExperiment params errorSampler hidden ringSecret coordinate
  let Replaced :=
    offDiagonalReplacedKeyExperiment params errorSampler hidden ringSecret coordinate
  let Reference :=
    referenceKeyExperiment params errorSampler hidden ringSecret coordinate
  let offDiagonalBound :=
    ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
      offDiagonalError outputCoordinate
  have hOff : tvDist Residualized Replaced ≤ offDiagonalBound := by
    simpa only [Residualized, Replaced, offDiagonalBound] using
      (tvDist_residualizedKeyExperiment_offDiagonalReplaced_le
        params errorSampler hidden ringSecret coordinate offDiagonalError hOffDiagonal)
  have hDiagonalCompletion : tvDist Replaced Reference ≤ diagonalError :=
    (tvDist_offDiagonalReplacedKeyExperiment_referenceKeyExperiment_le
      params errorSampler hidden ringSecret coordinate).trans hDiagonal
  have hNormalForm : tvDist Residualized Reference ≤
      diagonalError + offDiagonalBound := by
    have hTriangle := (tvDist_triangle Residualized Replaced Reference).trans
      (add_le_add hOff hDiagonalCompletion)
    simpa only [add_comm] using hTriangle
  unfold tvDist at hNormalForm ⊢
  rw [correctKeyExperiment_evalDist_eq_residualized
    params errorSampler hidden ringSecret coordinate]
  rw [← referenceKeyExperiment_evalDist_eq_generateDirectBootstrappingKey
    params errorSampler hidden ringSecret coordinate]
  simpa only [Residualized, Reference, offDiagonalBound] using hNormalForm

/-- The two-sampler off-diagonal hybrid is exactly the averaged source diagonal followed by
independent target-noise completion of every remaining coordinate. -/
theorem targetOffDiagonalReplacedKeyExperiment_evalDist_eq_diagonalCompletion [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler
        targetErrorSampler hidden ringSecret coordinate) =
      evalDist (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate >>=
        completeTargetKeyFromDiagonal params targetErrorSampler hidden ringSecret coordinate) := by
  let Control := directEntrySampler params sourceErrorSampler hidden ringSecret coordinate
  let Diagonal := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    factorizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
      control coordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    targetOffDiagonalReplacedCoordinateSampler params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate control outputCoordinate
  unfold targetOffDiagonalReplacedKeyExperiment diagonalExperiment
  simp only [bind_assoc]
  refine evalDist_bind_congr' Control fun control => ?_
  have hPull := FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    lweDimension (Replaced control) coordinate
  have hAtCoordinate : Replaced control coordinate = Diagonal control := by
    simp only [Replaced, Diagonal, targetOffDiagonalReplacedCoordinateSampler, if_pos]
  rw [hAtCoordinate] at hPull
  calc
    _ = evalDist (Diagonal control >>= fun diagonal =>
        Fin.mOfFn lweDimension fun outputCoordinate =>
          if outputCoordinate = coordinate then pure diagonal
          else Replaced control outputCoordinate) := hPull.symm
    _ = _ := by
      refine evalDist_bind_congr' (Diagonal control) fun diagonal => ?_
      apply congrArg evalDist
      apply congrArg (Fin.mOfFn lweDimension)
      funext outputCoordinate
      by_cases hCoordinate : outputCoordinate = coordinate
      · simp [hCoordinate]
      · simp [Replaced,
          targetOffDiagonalReplacedCoordinateSampler, hCoordinate]

/-- Sampling the selected target entry first and then completing the key with the target sampler
is distributionally identical to native direct BRK generation under that sampler. -/
theorem directTargetKey_evalDist_eq_coordinateCompletion [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist (directEntrySampler params targetErrorSampler hidden ringSecret coordinate >>=
        completeTargetKeyFromDiagonal params targetErrorSampler hidden ringSecret coordinate) =
      evalDist (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
        ringRank params.levels lweDimension targetErrorSampler
        (Gadget.Base.ringGadget params) hidden ringSecret) := by
  let Entry := fun outputCoordinate : Fin lweDimension =>
    directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate
  change evalDist (Entry coordinate >>= fun diagonal =>
      Fin.mOfFn lweDimension fun outputCoordinate =>
        if outputCoordinate = coordinate then pure diagonal else Entry outputCoordinate) =
    evalDist (Fin.mOfFn lweDimension Entry)
  exact FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    lweDimension Entry coordinate

/-- Replacing the source residual encryption at every off-diagonal coordinate with a fresh
target-noise entry costs the sum of the supplied conditional source-to-target bounds. -/
theorem tvDist_residualizedKeyExperiment_targetOffDiagonalReplaced_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (offDiagonalError : Fin lweDimension → ℝ)
    (hOffDiagonal : ∀ control ∈ support
        (directEntrySampler params sourceErrorSampler hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
              control outputCoordinate)
            (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (residualizedKeyExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
          hidden ringSecret coordinate) ≤
      ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
        offDiagonalError outputCoordinate := by
  let Control := directEntrySampler params sourceErrorSampler hidden ringSecret coordinate
  let Residualized := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
      control outputCoordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    targetOffDiagonalReplacedCoordinateSampler params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate control outputCoordinate
  let bound := ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
    offDiagonalError outputCoordinate
  have hConditional (control) (hcontrol : control ∈ support Control) :
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Replaced control)) ≤ bound := by
    calc
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Replaced control)) ≤
          ∑ outputCoordinate,
            tvDist (Residualized control outputCoordinate)
              (Replaced control outputCoordinate) :=
        FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
          lweDimension (Residualized control) (Replaced control)
      _ ≤ ∑ outputCoordinate : Fin lweDimension,
          if outputCoordinate = coordinate then 0
          else offDiagonalError outputCoordinate := by
        apply Finset.sum_le_sum
        intro outputCoordinate _
        by_cases hCoordinate : outputCoordinate = coordinate
        · subst outputCoordinate
          simp [Residualized, Replaced, residualizedCoordinateSampler,
            targetOffDiagonalReplacedCoordinateSampler, tvDist_self]
        · simpa only [Residualized, Replaced,
            targetOffDiagonalReplacedCoordinateSampler, if_neg hCoordinate] using
            hOffDiagonal control hcontrol outputCoordinate hCoordinate
      _ = bound := by
        rw [← Finset.add_sum_erase Finset.univ
          (fun outputCoordinate : Fin lweDimension =>
            if outputCoordinate = coordinate then 0
            else offDiagonalError outputCoordinate)
          (Finset.mem_univ coordinate)]
        simp only [if_pos, zero_add]
        apply Finset.sum_congr rfl
        intro outputCoordinate hOutput
        rw [if_neg (Finset.ne_of_mem_erase hOutput)]
  have hMixture := tvDist_bind_left_le_const (m := ProbComp) Control
    (fun control => Fin.mOfFn lweDimension (Residualized control))
    (fun control => Fin.mOfFn lweDimension (Replaced control))
    bound hConditional
  simpa only [residualizedKeyExperiment, targetOffDiagonalReplacedKeyExperiment,
    Control, Residualized, Replaced, bound] using hMixture

/-- Independent target completion cannot increase the distance between the averaged source
self-correlated diagonal and one fresh target-noise entry. -/
theorem tvDist_targetOffDiagonalReplaced_generateDirectBootstrappingKey_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
          hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension targetErrorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      tvDist
        (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (directEntrySampler params targetErrorSampler hidden ringSecret coordinate) := by
  let TargetEntry := directEntrySampler params targetErrorSampler hidden ringSecret coordinate
  let Completion :=
    completeTargetKeyFromDiagonal params targetErrorSampler hidden ringSecret coordinate
  have hDataProcessing := tvDist_bind_right_le (m := ProbComp)
    Completion
    (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate)
    TargetEntry
  unfold tvDist at hDataProcessing ⊢
  rw [targetOffDiagonalReplacedKeyExperiment_evalDist_eq_diagonalCompletion
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate]
  rw [← directTargetKey_evalDist_eq_coordinateCompletion
    params targetErrorSampler hidden ringSecret coordinate]
  exact hDataProcessing

/-- **Control-averaged two-sampler diagonal isolation.**  The selected diagonal is bounded
separately, while every off-diagonal replacement is charged by the actual generated-control
expectation, maximized only over the finite secret pair.  This avoids the generally too-strong
requirement that every supported control have a small conditional distance. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_averagedOffDiagonal
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal :
      tvDist
          (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate)
          (directEntrySampler params targetErrorSampler hidden ringSecret coordinate) ≤
        diagonalError) :
    tvDist
        (correctKeyExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension targetErrorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      diagonalError +
        worstCaseAveragedOffDiagonalReplacementDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler coordinate := by
  let Residualized :=
    residualizedKeyExperiment params sourceErrorSampler hidden ringSecret coordinate
  let Replaced :=
    targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate
  let TargetKey := BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension targetErrorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let offDiagonalError :=
    worstCaseAveragedOffDiagonalReplacementDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate
  have hOff : tvDist Residualized Replaced ≤ offDiagonalError :=
    (tvDist_residualizedKeyExperiment_targetOffDiagonalReplaced_le_expectation
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans
        (averagedOffDiagonalReplacementDistance_le_worstCase
          params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate)
  have hDiagonalCompletion : tvDist Replaced TargetKey ≤ diagonalError :=
    (tvDist_targetOffDiagonalReplaced_generateDirectBootstrappingKey_le
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans hDiagonal
  have hNormalForm : tvDist Residualized TargetKey ≤ diagonalError + offDiagonalError := by
    have hTriangle := (tvDist_triangle Residualized Replaced TargetKey).trans
      (add_le_add hOff hDiagonalCompletion)
    simpa only [add_comm] using hTriangle
  unfold tvDist at hNormalForm ⊢
  rw [correctKeyExperiment_evalDist_eq_residualized
    params sourceErrorSampler hidden ringSecret coordinate]
  simpa only [Residualized, TargetKey, offDiagonalError] using hNormalForm

/-- **Residual-`L²` control-averaged diagonal isolation.**  This strengthens the preceding
interface by replacing its ciphertext-level off-diagonal distance with the explicit finite
effective-error mass expression.  It is the intended endpoint for a smoothing or collision
estimate on the native internal-product residual. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_residualL2
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal :
      tvDist
          (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate)
          (directEntrySampler params targetErrorSampler hidden ringSecret coordinate) ≤
        diagonalError) :
    tvDist
        (correctKeyExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension targetErrorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      diagonalError +
        worstCaseAveragedOffDiagonalResidualL2Loss (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler coordinate := by
  let Residualized :=
    residualizedKeyExperiment params sourceErrorSampler hidden ringSecret coordinate
  let Replaced :=
    targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate
  let TargetKey := BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension targetErrorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let offDiagonalError :=
    worstCaseAveragedOffDiagonalResidualL2Loss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate
  have hOff : tvDist Residualized Replaced ≤ offDiagonalError :=
    (tvDist_residualizedKeyExperiment_targetOffDiagonalReplaced_le_expectation
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans
      ((averagedOffDiagonalReplacementDistance_le_residualL2Loss
        params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans
        (averagedOffDiagonalResidualL2Loss_le_worstCase
          params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate))
  have hDiagonalCompletion : tvDist Replaced TargetKey ≤ diagonalError :=
    (tvDist_targetOffDiagonalReplaced_generateDirectBootstrappingKey_le
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans hDiagonal
  have hNormalForm : tvDist Residualized TargetKey ≤ diagonalError + offDiagonalError := by
    have hTriangle := (tvDist_triangle Residualized Replaced TargetKey).trans
      (add_le_add hOff hDiagonalCompletion)
    simpa only [add_comm] using hTriangle
  unfold tvDist at hNormalForm ⊢
  rw [correctKeyExperiment_evalDist_eq_residualized
    params sourceErrorSampler hidden ringSecret coordinate]
  simpa only [Residualized, TargetKey, offDiagonalError] using hNormalForm

/-- **Error-only control-averaged diagonal isolation.**  This is the strongest construction-level
form: the off-diagonal term is an explicit expectation over narrow control errors and uniform
difference digits, maximized only over the selected Boolean message. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_errorOnlyL2
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ)
    (hDiagonal :
      tvDist
          (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate)
          (directEntrySampler params targetErrorSampler hidden ringSecret coordinate) ≤
        diagonalError) :
    tvDist
        (correctKeyExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension targetErrorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      diagonalError +
        worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler coordinate := by
  let Residualized :=
    residualizedKeyExperiment params sourceErrorSampler hidden ringSecret coordinate
  let Replaced :=
    targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate
  let TargetKey := BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension targetErrorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let offDiagonalError :=
    worstCaseAveragedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler coordinate
  have hOff : tvDist Residualized Replaced ≤ offDiagonalError :=
    (tvDist_residualizedKeyExperiment_targetOffDiagonalReplaced_le_expectation
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans
      ((averagedOffDiagonalReplacementDistance_le_errorOnlyL2Loss
        params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans
        (averagedOffDiagonalErrorOnlyL2Loss_le_worstCase
          params sourceErrorSampler targetErrorSampler (hidden coordinate) coordinate))
  have hDiagonalCompletion : tvDist Replaced TargetKey ≤ diagonalError :=
    (tvDist_targetOffDiagonalReplaced_generateDirectBootstrappingKey_le
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans hDiagonal
  have hNormalForm : tvDist Residualized TargetKey ≤ diagonalError + offDiagonalError := by
    have hTriangle := (tvDist_triangle Residualized Replaced TargetKey).trans
      (add_le_add hOff hDiagonalCompletion)
    simpa only [add_comm] using hTriangle
  unfold tvDist at hNormalForm ⊢
  rw [correctKeyExperiment_evalDist_eq_residualized
    params sourceErrorSampler hidden ringSecret coordinate]
  simpa only [Residualized, TargetKey, offDiagonalError] using hNormalForm

/-- **Two-sampler whole-BRK diagonal isolation.**  The correct source-noise shifted key is close
to a fresh target-noise BRK when its averaged diagonal and each conditional off-diagonal residual
are close to the corresponding target entries.  This is the interface used for centered-binomial
source keys and discrete-Gaussian residual keys. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_twoSamplers
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ) (offDiagonalError : Fin lweDimension → ℝ)
    (hDiagonal :
      tvDist
          (diagonalExperiment params sourceErrorSampler hidden ringSecret coordinate)
          (directEntrySampler params targetErrorSampler hidden ringSecret coordinate) ≤
        diagonalError)
    (hOffDiagonal : ∀ control ∈ support
        (directEntrySampler params sourceErrorSampler hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (residualizedCoordinateSampler params sourceErrorSampler hidden ringSecret coordinate
              control outputCoordinate)
            (directEntrySampler params targetErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (correctKeyExperiment params sourceErrorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension targetErrorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      diagonalError +
        ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
          offDiagonalError outputCoordinate := by
  let Residualized :=
    residualizedKeyExperiment params sourceErrorSampler hidden ringSecret coordinate
  let Replaced :=
    targetOffDiagonalReplacedKeyExperiment params sourceErrorSampler targetErrorSampler
      hidden ringSecret coordinate
  let TargetKey := BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
    ringRank params.levels lweDimension targetErrorSampler
    (Gadget.Base.ringGadget params) hidden ringSecret
  let offDiagonalBound :=
    ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
      offDiagonalError outputCoordinate
  have hOff : tvDist Residualized Replaced ≤ offDiagonalBound := by
    simpa only [Residualized, Replaced, offDiagonalBound] using
      (tvDist_residualizedKeyExperiment_targetOffDiagonalReplaced_le
        params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
        offDiagonalError hOffDiagonal)
  have hDiagonalCompletion : tvDist Replaced TargetKey ≤ diagonalError :=
    (tvDist_targetOffDiagonalReplaced_generateDirectBootstrappingKey_le
      params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate).trans hDiagonal
  have hNormalForm : tvDist Residualized TargetKey ≤
      diagonalError + offDiagonalBound := by
    have hTriangle := (tvDist_triangle Residualized Replaced TargetKey).trans
      (add_le_add hOff hDiagonalCompletion)
    simpa only [add_comm] using hTriangle
  unfold tvDist at hNormalForm ⊢
  rw [correctKeyExperiment_evalDist_eq_residualized
    params sourceErrorSampler hidden ringSecret coordinate]
  simpa only [Residualized, TargetKey, offDiagonalBound] using hNormalForm

/-- **Whole-BRK diagonal-isolation bound.**  The correct shifted-CMux key is close to a fresh
direct BRK whenever the one diagonal self-correlated coordinate and every off-diagonal residual
coordinate admit the displayed conditional bounds.  Thus the circular-security obligation is
confined to exactly one summand. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_sum [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ) (offDiagonalError : Fin lweDimension → ℝ)
    (hDiagonal : ∀ control ∈ support
        (directEntrySampler params errorSampler hidden ringSecret coordinate),
      tvDist
          (factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
            control coordinate)
          (pure control) ≤ diagonalError)
    (hOffDiagonal : ∀ control ∈ support
        (directEntrySampler params errorSampler hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
              control outputCoordinate)
            (directEntrySampler params errorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (correctKeyExperiment params errorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension errorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      ∑ outputCoordinate,
        if outputCoordinate = coordinate then diagonalError
        else offDiagonalError outputCoordinate := by
  let Control := directEntrySampler params errorSampler hidden ringSecret coordinate
  let Residualized := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate
  let Reference := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) =>
    referenceCoordinateSampler params errorSampler hidden ringSecret coordinate
      control outputCoordinate
  let bound := ∑ outputCoordinate : Fin lweDimension,
    if outputCoordinate = coordinate then diagonalError
    else offDiagonalError outputCoordinate
  have hConditional (control) (hcontrol : control ∈ support Control) :
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Reference control)) ≤ bound := by
    calc
      tvDist (Fin.mOfFn lweDimension (Residualized control))
          (Fin.mOfFn lweDimension (Reference control)) ≤
          ∑ outputCoordinate,
            tvDist (Residualized control outputCoordinate)
              (Reference control outputCoordinate) :=
        FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
          lweDimension (Residualized control) (Reference control)
      _ ≤ bound := by
        apply Finset.sum_le_sum
        intro outputCoordinate _
        by_cases hCoordinate : outputCoordinate = coordinate
        · subst outputCoordinate
          simpa only [Residualized, Reference, residualizedCoordinateSampler,
            referenceCoordinateSampler, if_pos] using
            hDiagonal control hcontrol
        · simpa only [Residualized, Reference, referenceCoordinateSampler,
            if_neg hCoordinate] using
            hOffDiagonal control hcontrol outputCoordinate hCoordinate
  have hMixture :
      tvDist
          (Control >>= fun control => Fin.mOfFn lweDimension (Residualized control))
          (Control >>= fun control => Fin.mOfFn lweDimension (Reference control)) ≤
        bound :=
    tvDist_bind_left_le_const (m := ProbComp) Control
      (fun control => Fin.mOfFn lweDimension (Residualized control))
      (fun control => Fin.mOfFn lweDimension (Reference control))
      bound hConditional
  unfold tvDist at hMixture ⊢
  rw [correctKeyExperiment_evalDist_eq_residualized
    params errorSampler hidden ringSecret coordinate]
  rw [← referenceKeyExperiment_evalDist_eq_generateDirectBootstrappingKey
    params errorSampler hidden ringSecret coordinate]
  simpa only [residualizedKeyExperiment, referenceKeyExperiment,
    Control, Residualized, Reference, bound] using hMixture

/-- The diagonal-isolation bound with the exceptional coordinate displayed separately from the
sum of all off-diagonal errors. -/
theorem tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonalError : ℝ) (offDiagonalError : Fin lweDimension → ℝ)
    (hDiagonal : ∀ control ∈ support
        (directEntrySampler params errorSampler hidden ringSecret coordinate),
      tvDist
          (factorizedCoordinateSampler params errorSampler hidden ringSecret coordinate
            control coordinate)
          (pure control) ≤ diagonalError)
    (hOffDiagonal : ∀ control ∈ support
        (directEntrySampler params errorSampler hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (residualizedCoordinateSampler params errorSampler hidden ringSecret coordinate
              control outputCoordinate)
            (directEntrySampler params errorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError outputCoordinate) :
    tvDist
        (correctKeyExperiment params errorSampler hidden ringSecret coordinate)
        (BootstrapSecurity.generateDirectBootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension errorSampler
          (Gadget.Base.ringGadget params) hidden ringSecret) ≤
      diagonalError +
        ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
          offDiagonalError outputCoordinate := by
  have h := tvDist_correctKeyExperiment_generateDirectBootstrappingKey_le_sum
    params errorSampler hidden ringSecret coordinate diagonalError offDiagonalError
    hDiagonal hOffDiagonal
  have hSum :
      (∑ outputCoordinate : Fin lweDimension,
          if outputCoordinate = coordinate then diagonalError
          else offDiagonalError outputCoordinate) =
        diagonalError +
          ∑ outputCoordinate ∈ Finset.univ.erase coordinate,
            offDiagonalError outputCoordinate := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun outputCoordinate : Fin lweDimension =>
        if outputCoordinate = coordinate then diagonalError
        else offDiagonalError outputCoordinate)
      (Finset.mem_univ coordinate)]
    simp only [if_pos]
    apply congrArg (diagonalError + ·)
    apply Finset.sum_congr rfl
    intro outputCoordinate hOutput
    rw [if_neg (Finset.ne_of_mem_erase hOutput)]
  rwa [hSum] at h

/-- Exact construction-level residual normal form for every off-diagonal correct output entry. -/
theorem factorizedEntryExperiment_evalDist_eq_residual [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension) :
    evalDist (factorizedEntryExperiment params errorSampler hidden ringSecret
        coordinate outputCoordinate) =
      evalDist (residualEntryExperiment params errorSampler hidden ringSecret
        coordinate outputCoordinate) := by
  simpa only [factorizedEntryExperiment, residualEntryExperiment, directEntrySampler] using
    (TGSW.Translation.add_independent_directEncrypt_evalDist
      ringRank params.levels errorSampler (embedRingSecret q ringSecret)
      (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) (hidden outputCoordinate))
      (perturbationSampler params errorSampler hidden ringSecret coordinate))

/-- Combined off-diagonal endpoint: the executable correct shifted-CMux entry is exactly the
corresponding direct TGSW residual-encryption mixture. -/
theorem correctEntryExperiment_evalDist_eq_residual [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (hne : outputCoordinate ≠ coordinate)
    (hError : Pr[⊥ | errorSampler] = 0) :
    evalDist (correctEntryExperiment params errorSampler hidden ringSecret
        coordinate outputCoordinate) =
      evalDist (residualEntryExperiment params errorSampler hidden ringSecret
        coordinate outputCoordinate) :=
  (correctEntryExperiment_evalDist_eq_factorized params errorSampler hidden ringSecret
      coordinate outputCoordinate hne hError).trans
    (factorizedEntryExperiment_evalDist_eq_residual params errorSampler hidden ringSecret
      coordinate outputCoordinate)

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm
