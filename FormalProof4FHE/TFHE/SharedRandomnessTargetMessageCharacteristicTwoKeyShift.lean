/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomialCharacteristicTwo
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAdditiveKeyShift
import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveRelativeKeyShift

set_option autoImplicit false

/-!
# Exact Relative Material Randomization in Characteristic Two

At coefficient modulus two, coefficientwise binary XOR is ordinary ring addition.  The additive
rank-one TGSW shear can therefore move the source BRK encryption key by an arbitrary normalized
relative mask.  The ring-extension table is simpler: ordinary additive key transport changes its
source key, while a public body translation adds the suffix-mask gadget messages.

Positive-width centered-binomial ring noise modulo two is exactly uniform, so the BRK row-error
shear is invariant.  Combining the two transforms instantiates the complete
`RelativeKeyShiftMaterialEvaluator` with zero loss.

This is a diagnostic closure of the full relative-key interface, not a practical TFHE parameter
theorem.  The same centered-binomial sampler is uniform modulo two, so it has no narrow correctness
margin; at every practical modulus greater than two, coefficientwise XOR is not an additive ring
shift and the nonlinear relative-key obligation remains.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
open FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native

/-! ## Centered-binomial shear invariance modulo two -/

/-- Positive-width centered-binomial ring errors modulo two are invariant under every rank-one
additive TGSW row shear. -/
theorem rankOneAdditiveShiftNoiseInvariant_centeredBinomial_two
    (degree levels eta : ℕ) (delta : RLWE.Rq 2 degree) :
    RankOneAdditiveShiftNoiseInvariant (levels := levels)
      (RLWE.CenteredBinomial.sampler 2 degree (eta + 1)) delta := by
  let count := TGSW.rowCount 1 levels
  let errorSampler := RLWE.CenteredBinomial.sampler 2 degree (eta + 1)
  let errors := ProbComp.sampleIID count errorSampler
  let UniformErrors : ProbComp (Fin count → RLWE.Rq 2 degree) :=
    $ᵗ (Fin count → RLWE.Rq 2 degree)
  have hcoordinate : evalDist errorSampler =
      evalDist ($ᵗ (RLWE.Rq 2 degree)) := by
    exact RLWE.CenteredBinomial.sampler_two_evalDist_eq_uniform degree eta
  have hiid : evalDist errors = evalDist UniformErrors := by
    calc
      evalDist errors =
          evalDist (ProbComp.sampleIID count ($ᵗ (RLWE.Rq 2 degree))) := by
        exact FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr count
          (fun _ ↦ errorSampler) (fun _ ↦ $ᵗ (RLWE.Rq 2 degree))
          (fun _ ↦ hcoordinate)
      _ = evalDist UniformErrors :=
        FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform count
  unfold RankOneAdditiveShiftNoiseInvariant
  change evalDist (rankOneAdditiveShiftErrorShear delta <$> errors) =
    evalDist errors
  calc
    evalDist (rankOneAdditiveShiftErrorShear delta <$> errors) =
        evalDist (rankOneAdditiveShiftErrorShear delta <$> UniformErrors) :=
      evalDist_map_eq_of_evalDist_eq hiid
        (rankOneAdditiveShiftErrorShear delta)
    _ = evalDist UniformErrors :=
      evalDist_map_bijective_uniform_cross
        (α := Fin count → RLWE.Rq 2 degree)
        (β := Fin count → RLWE.Rq 2 degree)
        (rankOneAdditiveShiftErrorShear delta)
        (rankOneAdditiveShiftErrorShear_bijective delta)
    _ = evalDist errors := hiid.symm

/-- The same uniformity argument discharges the global-complement shear. -/
theorem rankOneComplementNoiseInvariant_centeredBinomial_two
    (degree levels eta : ℕ) (offset : RLWE.Rq 2 degree) :
    RankOneComplementNoiseInvariant (levels := levels)
      (RLWE.CenteredBinomial.sampler 2 degree (eta + 1)) offset := by
  let count := TGSW.rowCount 1 levels
  let source := RLWE.CenteredBinomial.sampler 2 degree (eta + 1)
  let sourceErrors := ProbComp.sampleIID count source
  let uniformErrors := ProbComp.sampleIID count ($ᵗ (RLWE.Rq 2 degree))
  have hcoordinate : evalDist source =
      evalDist ($ᵗ (RLWE.Rq 2 degree)) :=
    RLWE.CenteredBinomial.sampler_two_evalDist_eq_uniform degree eta
  have hiid : evalDist sourceErrors = evalDist uniformErrors :=
    FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr count
      (fun _ ↦ source) (fun _ ↦ $ᵗ (RLWE.Rq 2 degree))
      (fun _ ↦ hcoordinate)
  unfold RankOneComplementNoiseInvariant
  change evalDist (rankOneComplementErrorShear offset <$> sourceErrors) =
    evalDist sourceErrors
  calc
    evalDist (rankOneComplementErrorShear offset <$> sourceErrors) =
        evalDist (rankOneComplementErrorShear offset <$> uniformErrors) :=
      evalDist_map_eq_of_evalDist_eq hiid (rankOneComplementErrorShear offset)
    _ = evalDist uniformErrors :=
      rankOneComplementNoiseInvariant_uniform offset
    _ = evalDist sourceErrors := hiid.symm

/-- Hence the quantitative complement defect is literally zero. -/
theorem rankOneComplementNoiseDistance_centeredBinomial_two_eq_zero
    (degree levels eta : ℕ) (offset : RLWE.Rq 2 degree) :
    rankOneComplementNoiseDistance (levels := levels)
      (RLWE.CenteredBinomial.sampler 2 degree (eta + 1)) offset = 0 := by
  unfold rankOneComplementNoiseDistance tvDist
  rw [rankOneComplementNoiseInvariant_centeredBinomial_two degree levels eta offset]
  exact SPMF.tvDist_self _

/-- Negation is the identity on every binary-coefficient native polynomial. -/
theorem neg_eq_self_rq_two {degree : ℕ} (value : RLWE.Rq 2 degree) :
    -value = value := by
  change RLWE.CenteredBinomial.negError 2 degree value = value
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      rw [show
        (RLWE.CenteredBinomial.negError 2 (degree + 1) value).get coefficient =
          -(value.get coefficient : ZMod 2) by
        simp [RLWE.CenteredBinomial.negError]]
      let scalar : ZMod 2 := value.get coefficient
      have hval : scalar.val = 0 ∨ scalar.val = 1 := by
        have hlt : scalar.val < 2 := ZMod.val_lt scalar
        apply Nat.le_one_iff_eq_zero_or_eq_one.mp
        omega
      rcases hval with hzero | hone
      · have hscalar : scalar = 0 := by
          rw [← ZMod.natCast_zmod_val scalar, hzero]
          rfl
        simp [scalar, hscalar]
      · have hscalar : scalar = 1 := by
          rw [← ZMod.natCast_zmod_val scalar, hone]
          rfl
        change -scalar = scalar
        rw [hscalar]
        exact ZMod.neg_eq_self_mod_two 1

/-- Every ring-error sampler is negation symmetric in coefficient characteristic two. -/
theorem negationSymmetric_rq_two
    {degree : ℕ} (sampler : ProbComp (RLWE.Rq 2 degree)) :
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric sampler := by
  intro error
  rw [neg_eq_self_rq_two]

/-! ## Exact ring-extension transport -/

/-- Add a public message vector to the bodies of a complete TLWE batch. -/
def addBatchMessage {R : Type} [Add R] {dimension samples : ℕ}
    (shift : Fin samples → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  (ciphertext.1, ciphertext.2 + shift)

/-- Public body addition changes only the declared message vector. -/
theorem addBatchMessage_batchAssemble
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error shift : Fin samples → R) :
    addBatchMessage shift
        (TLWE.batchAssemble secret challenge message error) =
      TLWE.batchAssemble secret challenge (message + shift) error := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [addBatchMessage, TLWE.batchAssemble, Pi.add_apply]
    abel

/-- In characteristic two, masking a suffix ring key adds the corresponding public gadget-message
vector to the old ring-extension messages. -/
theorem ringKeySwitchMessages_masked_two
    {degree suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq 2 degree)
    (suffixSecret suffixMask : RingBinarySecret suffixRank degree) :
    ringKeySwitchMessages 2 degree suffixRank levels gadget
        (maskedRingSecret suffixSecret suffixMask) =
      ringKeySwitchMessages 2 degree suffixRank levels gadget suffixSecret +
        ringKeySwitchMessages 2 degree suffixRank levels gadget suffixMask := by
  cases degree with
  | zero =>
      funext row
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree =>
      funext row
      obtain ⟨⟨component, level⟩, rfl⟩ := finProdFinEquiv.surjective row
      simp only [ringKeySwitchMessages, Equiv.symm_apply_apply, Pi.add_apply]
      change embedBinaryPolynomial 2 (degree + 1)
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            (suffixSecret component) (suffixMask component)) * gadget level = _
      rw [embedBinaryPolynomial_masked_eq_add_of_two_eq_zero
        (q := 2) (ZMod.natCast_self 2)]
      exact add_mul _ _ _

/-- Simultaneously additively shift the rank-one source key and the suffix message polynomial of
every ring-extension row. -/
def transformRingExtensionKeyTwo
    {degree suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq 2 degree)
    (sourceMask : RingBinarySecret 1 degree)
    (suffixMask : RingBinarySecret suffixRank degree)
    (extensionKey : RingKeySwitchKey 2 degree 1 suffixRank levels) :
    RingKeySwitchKey 2 degree 1 suffixRank levels :=
  addBatchMessage
    (ringKeySwitchMessages 2 degree suffixRank levels gadget suffixMask)
    (additiveTranslateBatch (embedRingSecret 2 sourceMask) extensionKey)

/-- Deterministic normal form of the complete characteristic-two extension-key transform. -/
theorem transformRingExtensionKeyTwo_batchAssemble
    {degree suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq 2 degree)
    (sourceSecret sourceMask : RingBinarySecret 1 degree)
    (suffixSecret suffixMask : RingBinarySecret suffixRank degree)
    (challenge : Matrix (Fin 1) (Fin (suffixRank * levels))
      (RLWE.Rq 2 degree))
    (error : Fin (suffixRank * levels) → RLWE.Rq 2 degree) :
    transformRingExtensionKeyTwo gadget sourceMask suffixMask
        (TLWE.batchAssemble (embedRingSecret 2 sourceSecret) challenge
          (ringKeySwitchMessages 2 degree suffixRank levels gadget suffixSecret)
          error) =
      TLWE.batchAssemble
        (embedRingSecret 2 (maskedRingSecret sourceSecret sourceMask)) challenge
          (ringKeySwitchMessages 2 degree suffixRank levels gadget
          (maskedRingSecret suffixSecret suffixMask)) error := by
  cases degree with
  | zero =>
      apply Prod.ext
      · funext component row
        apply LatticeCrypto.Poly.ext_get_eq
        intro coefficient
        exact coefficient.elim0
      · funext row
        apply LatticeCrypto.Poly.ext_get_eq
        intro coefficient
        exact coefficient.elim0
  | succ degree =>
      rw [embedRingSecret_masked_eq_add_of_two_eq_zero
        (q := 2) (ZMod.natCast_self 2)]
      rw [ringKeySwitchMessages_masked_two]
      unfold transformRingExtensionKeyTwo
      rw [additiveTranslateBatch_batchAssemble]
      exact addBatchMessage_batchAssemble
        (embedRingSecret 2 sourceSecret + embedRingSecret 2 sourceMask)
        challenge
        (ringKeySwitchMessages 2 (degree + 1) suffixRank levels gadget suffixSecret)
        error
        (ringKeySwitchMessages 2 (degree + 1) suffixRank levels gadget suffixMask)

/-- The ring-extension sampler is transported exactly for every error distribution. -/
theorem transformRingExtensionKeyTwo_generate_evalDist
    {degree suffixRank levels : ℕ}
    (errorSampler : ProbComp (RLWE.Rq 2 degree))
    (gadget : Fin levels → RLWE.Rq 2 degree)
    (sourceSecret sourceMask : RingBinarySecret 1 degree)
    (suffixSecret suffixMask : RingBinarySecret suffixRank degree) :
    evalDist (transformRingExtensionKeyTwo gadget sourceMask suffixMask <$>
        generateRingKeySwitchKey 2 degree 1 suffixRank levels errorSampler gadget
          sourceSecret suffixSecret) =
      evalDist (generateRingKeySwitchKey 2 degree 1 suffixRank levels errorSampler
        gadget (maskedRingSecret sourceSecret sourceMask)
          (maskedRingSecret suffixSecret suffixMask)) := by
  let samples := suffixRank * levels
  let errors := ProbComp.sampleIID samples errorSampler
  let sourceMessages :=
    ringKeySwitchMessages 2 degree suffixRank levels gadget suffixSecret
  let targetMessages := ringKeySwitchMessages 2 degree suffixRank levels gadget
    (maskedRingSecret suffixSecret suffixMask)
  let targetSecret :=
    embedRingSecret 2 (maskedRingSecret sourceSecret sourceMask)
  let finish := fun
      (challenge : Matrix (Fin 1) (Fin samples) (RLWE.Rq 2 degree))
      (error : Fin samples → RLWE.Rq 2 degree) ↦
    (pure (TLWE.batchAssemble targetSecret challenge targetMessages error) :
      ProbComp (RingKeySwitchKey 2 degree 1 suffixRank levels))
  unfold generateRingKeySwitchKey
  rw [show TLWE.batchEncrypt 1 (suffixRank * levels) errorSampler
      (embedRingSecret 2 sourceSecret) sourceMessages =
      (($ᵗ Matrix (Fin 1) (Fin samples) (RLWE.Rq 2 degree)) >>=
        fun challenge ↦ errors >>= fun error ↦
          pure (TLWE.batchAssemble (embedRingSecret 2 sourceSecret)
            challenge sourceMessages error)) by
    simp [TLWE.batchEncrypt, samples, errors, sourceMessages, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  calc
    _ = evalDist
        (($ᵗ Matrix (Fin 1) (Fin samples) (RLWE.Rq 2 degree)) >>=
          fun challenge ↦ errors >>= fun error ↦ finish challenge error) := by
      refine evalDist_bind_congr'
        ($ᵗ Matrix (Fin 1) (Fin samples) (RLWE.Rq 2 degree))
        fun challenge ↦ ?_
      refine evalDist_bind_congr' errors fun error ↦ ?_
      simpa only [samples, sourceMessages, targetMessages, targetSecret, finish] using
        congrArg evalDist (congrArg
          (fun value ↦
            (pure value :
              ProbComp (RingKeySwitchKey 2 degree 1 suffixRank levels)))
          (transformRingExtensionKeyTwo_batchAssemble gadget sourceSecret
            sourceMask suffixSecret suffixMask challenge error))
    _ = _ := by
      simp [TLWE.batchEncrypt, samples, errors, targetMessages, targetSecret,
        finish, monad_norm]

/-! ## Complete material evaluator -/

/-- Public characteristic-two transform after the BRK plaintext vector has already been
normalized to the shifted target key. -/
def transformRelativeKeyShiftMaterialTwo
    {degree suffixRank levels : ℕ}
    (gadget : Fin levels → RLWE.Rq 2 (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree)
    (material : Auxiliary 2 (degree + 1) 1 suffixRank levels) :
    Auxiliary 2 (degree + 1) 1 suffixRank levels :=
  let mask := liftRelativeNestedMask relativeMask
  (additiveShiftBootstrappingKey (embedRingSecret 2 mask.1 0) material.1,
    transformRingExtensionKeyTwo gadget mask.1 mask.2 material.2)

/-- The complete message-normalized material is transported to the XOR-shifted nested key with
exactly zero loss in characteristic two. -/
theorem transformRelativeKeyShiftMaterialTwo_sample_evalDist
    {degree suffixRank levels eta : ℕ}
    (extensionErrorSampler : ProbComp (RLWE.Rq 2 (degree + 1)))
    (gadget : Fin levels → RLWE.Rq 2 (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (relativeMask : RelativeNestedMask suffixRank degree) :
    evalDist (transformRelativeKeyShiftMaterialTwo gadget relativeMask <$>
        sampleRelativeMessageShiftedMaterial 2 degree suffixRank levels (eta + 1)
          extensionErrorSampler gadget secret relativeMask) =
      evalDist (sampleEvaluationMaterial 2 (degree + 1) 1 suffixRank levels
        (RLWE.CenteredBinomial.sampler 2 (degree + 1) (eta + 1))
        extensionErrorSampler gadget
        (act secret (liftRelativeNestedMask relativeMask))) := by
  let mask := liftRelativeNestedMask relativeMask
  let shiftedSecret := act secret mask
  let sourceBootstrappingKey :=
    Native.generateBootstrappingKey 2 (degree + 1) 1 levels
      (targetScalarDimension 1 suffixRank (degree + 1))
      (RLWE.CenteredBinomial.sampler 2 (degree + 1) (eta + 1)) gadget
      (targetMessages shiftedSecret.1 shiftedSecret.2) secret.1
  let targetBootstrappingKey :=
    Native.generateBootstrappingKey 2 (degree + 1) 1 levels
      (targetScalarDimension 1 suffixRank (degree + 1))
      (RLWE.CenteredBinomial.sampler 2 (degree + 1) (eta + 1)) gadget
      (targetMessages shiftedSecret.1 shiftedSecret.2) shiftedSecret.1
  let sourceExtensionKey := generateRingExtensionKey 2 (degree + 1) 1 suffixRank
    levels extensionErrorSampler gadget secret.1 secret.2
  let targetExtensionKey := generateRingExtensionKey 2 (degree + 1) 1 suffixRank
    levels extensionErrorSampler gadget shiftedSecret.1 shiftedSecret.2
  let transformBootstrap :
      Native.BootstrappingKey 2 (degree + 1) 1 levels
        (targetScalarDimension 1 suffixRank (degree + 1)) →
      Native.BootstrappingKey 2 (degree + 1) 1 levels
        (targetScalarDimension 1 suffixRank (degree + 1)) :=
    additiveShiftBootstrappingKey (embedRingSecret 2 mask.1 0)
  let transformExtension :
      RingExtensionKey 2 (degree + 1) 1 suffixRank levels →
        RingExtensionKey 2 (degree + 1) 1 suffixRank levels :=
    transformRingExtensionKeyTwo gadget mask.1 mask.2
  have hbootstrap :
      evalDist (transformBootstrap <$> sourceBootstrappingKey) =
        evalDist targetBootstrappingKey := by
    simpa only [transformBootstrap, sourceBootstrappingKey,
      targetBootstrappingKey, shiftedSecret, mask, act] using
      (additiveShiftBootstrappingKey_masked_zmod_two_evalDist
        (RLWE.CenteredBinomial.sampler 2 (degree + 1) (eta + 1)) gadget
        (targetMessages
          (act secret (liftRelativeNestedMask relativeMask)).1
          (act secret (liftRelativeNestedMask relativeMask)).2)
        secret.1 (liftRelativeNestedMask relativeMask).1
        (rankOneAdditiveShiftNoiseInvariant_centeredBinomial_two
          (degree + 1) levels eta
          (embedRingSecret 2 (liftRelativeNestedMask relativeMask).1 0)))
  have hextension :
      evalDist (transformExtension <$> sourceExtensionKey) =
        evalDist targetExtensionKey := by
    simpa only [transformExtension, sourceExtensionKey, targetExtensionKey,
      generateRingExtensionKey, shiftedSecret, mask, act] using
      (transformRingExtensionKeyTwo_generate_evalDist extensionErrorSampler gadget
        secret.1 (liftRelativeNestedMask relativeMask).1 secret.2
        (liftRelativeNestedMask relativeMask).2)
  change evalDist
      ((fun pair ↦ (transformBootstrap pair.1, transformExtension pair.2)) <$>
        (sourceBootstrappingKey >>= fun left ↦
          sourceExtensionKey >>= fun right ↦ pure (left, right))) =
    evalDist (targetBootstrappingKey >>= fun left ↦
      targetExtensionKey >>= fun right ↦ pure (left, right))
  exact
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.independentPair_map_evalDist_congr
      sourceBootstrappingKey sourceExtensionKey targetBootstrappingKey
      targetExtensionKey transformBootstrap transformExtension hbootstrap hextension

/-- Zero-loss instantiation of the exact nonlinear-core interface at coefficient modulus two. -/
def characteristicTwoRelativeKeyShiftMaterialEvaluator
    (degree suffixRank levels eta : ℕ)
    (extensionErrorSampler : ProbComp (RLWE.Rq 2 (degree + 1)))
    (gadget : Fin levels → RLWE.Rq 2 (degree + 1)) :
    RelativeKeyShiftMaterialEvaluator 2 degree suffixRank levels (eta + 1)
      extensionErrorSampler
      (RLWE.CenteredBinomial.sampler 2 (degree + 1) (eta + 1))
      extensionErrorSampler gadget where
  evaluateKeyShift := fun relativeMask material ↦
    pure (transformRelativeKeyShiftMaterialTwo gadget relativeMask material)
  error := 0
  error_nonneg := le_rfl
  keyShiftDistance_le := by
    intro secret relativeMask
    unfold tvDist
    rw [show evalDist
        (sampleRelativeMessageShiftedMaterial 2 degree suffixRank levels (eta + 1)
            extensionErrorSampler gadget secret relativeMask >>=
          fun material ↦
            pure (transformRelativeKeyShiftMaterialTwo gadget relativeMask material)) =
        evalDist (transformRelativeKeyShiftMaterialTwo gadget relativeMask <$>
          sampleRelativeMessageShiftedMaterial 2 degree suffixRank levels (eta + 1)
            extensionErrorSampler gadget secret relativeMask) by
      simp [map_eq_bind_pure_comp]]
    rw [transformRelativeKeyShiftMaterialTwo_sample_evalDist]
    exact le_of_eq (SPMF.tvDist_self _)

@[simp]
theorem characteristicTwoRelativeKeyShiftMaterialEvaluator_error
    (degree suffixRank levels eta : ℕ)
    (extensionErrorSampler : ProbComp (RLWE.Rq 2 (degree + 1)))
    (gadget : Fin levels → RLWE.Rq 2 (degree + 1)) :
    (characteristicTwoRelativeKeyShiftMaterialEvaluator degree suffixRank levels eta
      extensionErrorSampler gadget).error = 0 := rfl

/-- The already checked relative/tape/anchor compiler is fully instantiated at modulus two. -/
def characteristicTwoRelativeThenGlobalViewRandomization
    (degree suffixRank levels queryCount eta : ℕ)
    (extensionErrorSampler : ProbComp (RLWE.Rq 2 (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod 2))
    (gadget : Fin levels → RLWE.Rq 2 (degree + 1)) :=
  (characteristicTwoRelativeKeyShiftMaterialEvaluator degree suffixRank levels eta
      extensionErrorSampler gadget).toRelativeThenGlobalViewRandomization
    (queryCount := queryCount) inputErrorSampler
    (negationSymmetric_rq_two extensionErrorSampler)

/-- The complete fresh-nested-key view randomizer, including the adaptive tape and anchor, has
zero total-variation loss in the characteristic-two diagnostic instance. -/
theorem characteristicTwoRelativeThenGlobalViewRandomization_error
    (degree suffixRank levels queryCount eta : ℕ)
    (extensionErrorSampler : ProbComp (RLWE.Rq 2 (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod 2))
    (gadget : Fin levels → RLWE.Rq 2 (degree + 1)) :
    (characteristicTwoRelativeThenGlobalViewRandomization degree suffixRank levels
      queryCount eta extensionErrorSampler inputErrorSampler gadget).error = 0 := by
  rw [show
      (characteristicTwoRelativeThenGlobalViewRandomization degree suffixRank levels
        queryCount eta extensionErrorSampler inputErrorSampler gadget).error =
        (characteristicTwoRelativeKeyShiftMaterialEvaluator degree suffixRank levels eta
          extensionErrorSampler gadget).error +
          globalComplementViewError (suffixRank := suffixRank) (levels := levels)
            (RLWE.CenteredBinomial.sampler 2 (degree + 1) (eta + 1)) by rfl]
  rw [characteristicTwoRelativeKeyShiftMaterialEvaluator_error]
  unfold globalComplementViewError
  rw [rankOneComplementNoiseDistance_centeredBinomial_two_eq_zero]
  simp

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
