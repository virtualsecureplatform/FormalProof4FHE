/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CoefficientStructuredLWE
import FormalProof4FHE.TFHE.ScalarSecretRandomization
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleCircularSearch
import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision

/-!
# Full-Secret Randomization Boundary for Shared-Randomness One-Cycle TFHE

The CircLWE search-to-decision randomization adds a public mask to the complete encryption key.
For the shared-randomness TFHE layout, the corresponding fresh-key action must randomize the
complete binary master key, because its prefix is simultaneously the scalar TLWE key and part of
the rank-one RLWE key.

This module separates the two relevant facts.

* Coefficientwise XOR by a uniform binary master mask gives an exactly fresh binary master key
  and preserves the shared prefix/suffix geometry.
* Public additive and scalar-affine LWE/RLWE ciphertext maps exactly transport encryption keys by
  `s ↦ s + d` and `s ↦ u * s + d`, respectively.
* Global complement lifts exactly to the suffix-only KSK for every negation-symmetric scalar
  error law.
* On a rank-one TGSW ciphertext, the complete public complement conjugation is exact and exposes
  the necessary row-error shear `(e_mask,e_body) ↦ (e_mask+d*e_body,-e_body)`.

In characteristic two, addition implements the binary XOR action exactly.  At every native
modulus `q > 2`, addition cannot implement even one nontrivial binary coefficient toggle.  In the
larger scalar-affine class, the only possible XOR masks are identity and global complement.  That
two-element action cannot produce a fresh binary key with at least two coefficients, even under
arbitrary randomized selection.  This is a precise obstruction to these natural public algebraic
randomizers; it is not an impossibility theorem for nonlinear homomorphic evaluators or for
circular security itself.  The KSK complement needs only ordinary symmetry, whereas a narrow-noise
BRK complement additionally needs invariance under the displayed shear.  Uniform ring errors
satisfy that stronger law exactly; negation symmetry of centered binomial or discrete Gaussian
noise alone does not establish it.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-! ## Exact XOR randomization of the complete binary master key -/

/-- Coefficientwise XOR action on a complete binary ring key. -/
def maskedRingSecret {rank degree : ℕ}
    (secret mask : RingBinarySecret rank degree) : RingBinarySecret rank degree :=
  fun component ↦
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
      (secret component) (mask component)

/-- Applying the same fixed source key twice as an XOR mask is the identity. -/
@[simp]
theorem maskedRingSecret_involutive {rank degree : ℕ}
    (secret mask : RingBinarySecret rank degree) :
    maskedRingSecret secret (maskedRingSecret secret mask) = mask := by
  funext component coefficient
  exact LWE.MultiKeyAffine.maskedBit_involutive
    (secret component coefficient) (mask component coefficient)

/-- XOR with one fixed complete ring key, packaged as a permutation. -/
def maskedRingSecretEquiv {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) :
    RingBinarySecret rank degree ≃ RingBinarySecret rank degree where
  toFun := maskedRingSecret secret
  invFun := maskedRingSecret secret
  left_inv := maskedRingSecret_involutive secret
  right_inv := maskedRingSecret_involutive secret

/-- A uniform complete binary master mask XORed with a fixed master key is exactly fresh. -/
theorem maskedRingSecret_uniform_evalDist {rank degree : ℕ}
    (secret : RingBinarySecret rank degree) :
    evalDist (maskedRingSecret secret <$> ($ᵗ RingBinarySecret rank degree)) =
      evalDist ($ᵗ RingBinarySecret rank degree) :=
  evalDist_map_bijective_uniform_cross
    (α := RingBinarySecret rank degree) (β := RingBinarySecret rank degree)
    (maskedRingSecret secret) (maskedRingSecretEquiv secret).bijective

/-- The same fresh-key law, stated with the exact master-secret sampler used by the one-cycle
search problem.  This discharges the secret-law field of a future native view randomizer. -/
theorem oneCycle_searchSecretLaw
    (prefixDimension suffixDimension : ℕ)
    (secret : AuxiliaryInput.Search.Secret prefixDimension suffixDimension) :
    evalDist (maskedRingSecret secret <$>
        Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) =
      evalDist (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) := by
  simpa only [Native.sampleRingSecret] using maskedRingSecret_uniform_evalDist secret

/-- Full-master XOR restricts to the checked scalar XOR action on the shared prefix. -/
theorem prefixSecret_maskedRingSecret
    {prefixDimension suffixDimension : ℕ}
    (secret mask : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    prefixSecret (maskedRingSecret secret mask) =
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        (prefixSecret secret) (prefixSecret mask) := by
  rfl

/-- Full-master XOR also restricts to coefficientwise XOR on the independent suffix. -/
theorem suffixSecret_maskedRingSecret
    {prefixDimension suffixDimension : ℕ}
    (secret mask : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    suffixSecret (maskedRingSecret secret mask) =
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        (suffixSecret secret) (suffixSecret mask) := by
  rfl

/-- Masking nested prefix/suffix keys preserves the shared-randomness nesting relation exactly. -/
theorem maskedRingSecret_nestedRingSecret
    {prefixDimension suffixDimension : ℕ}
    (prefixKey prefixMask : BinarySecret prefixDimension)
    (suffixKey suffixMask : BinarySecret suffixDimension) :
    maskedRingSecret
        (nestedRingSecret prefixKey suffixKey)
        (nestedRingSecret prefixMask suffixMask) =
      nestedRingSecret
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          prefixKey prefixMask)
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          suffixKey suffixMask) := by
  funext component coordinate
  have hcomponent : component = 0 := Subsingleton.elim _ _
  subst component
  refine Fin.addCases ?_ ?_ coordinate
  · intro prefixCoordinate
    simp [maskedRingSecret, nestedRingSecret,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]
  · intro suffixCoordinate
    simp [maskedRingSecret, nestedRingSecret,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]

/-! ## The public additive key transport used by CircLWE -/

/-- Add the public correction `⟨delta, challenge⟩` to every ciphertext body. -/
def additiveTranslateBatch {R : Type} [CommRing R] {dimension samples : ℕ}
    (delta : Fin dimension → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  (ciphertext.1, ciphertext.2 + vecMul delta ciphertext.1)

/-- Public body correction transports a deterministic LWE batch from `secret` to
`secret + delta` with exactly the same message and error. -/
theorem additiveTranslateBatch_batchAssemble
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret delta : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) :
    additiveTranslateBatch delta
        (TLWE.batchAssemble secret challenge message error) =
      TLWE.batchAssemble (secret + delta) challenge message error := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [additiveTranslateBatch, TLWE.batchAssemble, Pi.add_apply,
      Matrix.vecMul, dotProduct]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    abel

/-- Addition by a fixed element is a permutation of a finite additive group. -/
def addSecretEquiv {R : Type} [AddGroup R] (secret : R) : R ≃ R where
  toFun mask := secret + mask
  invFun freshSecret := -secret + freshSecret
  left_inv mask := by simp
  right_inv freshSecret := by simp

/-- The paper's additive action gives a fresh secret when the mask is uniform over the complete
finite coefficient ring. -/
theorem add_uniform_evalDist {R : Type}
    [AddGroup R] [Fintype R] [SampleableType R] (secret : R) :
    evalDist ((fun mask ↦ secret + mask) <$> ($ᵗ R)) = evalDist ($ᵗ R) :=
  evalDist_map_bijective_uniform_cross
    (α := R) (β := R) (fun mask ↦ secret + mask) (addSecretEquiv secret).bijective

/-! ## The larger public scalar-affine RLWE transport -/

/-- Multiply every public challenge entry by one ring unit. -/
def scaleChallenge {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun coordinate sample ↦ (multiplier : R) * challenge coordinate sample

@[simp]
theorem scaleChallenge_inv_scaleChallenge
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    scaleChallenge multiplier⁻¹ (scaleChallenge multiplier challenge) = challenge := by
  funext coordinate sample
  simp [scaleChallenge]

@[simp]
theorem scaleChallenge_scaleChallenge_inv
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) (challenge : Matrix (Fin dimension) (Fin samples) R) :
    scaleChallenge multiplier (scaleChallenge multiplier⁻¹ challenge) = challenge := by
  funext coordinate sample
  simp [scaleChallenge]

/-- Unit scaling is a permutation of the complete public challenge matrix. -/
theorem scaleChallenge_bijective
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) :
    Function.Bijective
      (scaleChallenge multiplier :
        Matrix (Fin dimension) (Fin samples) R →
          Matrix (Fin dimension) (Fin samples) R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨scaleChallenge multiplier⁻¹,
      scaleChallenge_inv_scaleChallenge multiplier,
      scaleChallenge_scaleChallenge_inv multiplier⟩

/-- Consequently, inverse unit scaling preserves an exactly uniform RLWE challenge law. -/
theorem scaleChallenge_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ} (multiplier : Rˣ) :
    evalDist (scaleChallenge multiplier <$>
        ($ᵗ Matrix (Fin dimension) (Fin samples) R)) =
      evalDist ($ᵗ Matrix (Fin dimension) (Fin samples) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin samples) R)
    (β := Matrix (Fin dimension) (Fin samples) R)
    (scaleChallenge multiplier) (scaleChallenge_bijective multiplier)

/-- Apply the same scalar-affine map to every component of a module/RLWE secret. -/
def scalarAffineSecret {R : Type} [CommRing R] {dimension : ℕ}
    (multiplier : Rˣ) (offset secret : Fin dimension → R) : Fin dimension → R :=
  fun coordinate ↦ (multiplier : R) * secret coordinate + offset coordinate

/-- Exact inner-product identity behind public scalar-affine key transport. -/
theorem vecMul_scalarAffineSecret_scaleChallenge_inv
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) (offset secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    vecMul (scalarAffineSecret multiplier offset secret)
        (scaleChallenge multiplier⁻¹ challenge) =
      vecMul secret challenge +
        vecMul offset (scaleChallenge multiplier⁻¹ challenge) := by
  funext sample
  simp only [Matrix.vecMul, dotProduct, scalarAffineSecret, scaleChallenge,
    Pi.add_apply]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  calc
    ((multiplier : R) * secret coordinate) *
        (((multiplier⁻¹ : Rˣ) : R) * challenge coordinate sample) =
      ((multiplier : R) * ((multiplier⁻¹ : Rˣ) : R)) *
        (secret coordinate * challenge coordinate sample) := by ring
    _ = secret coordinate * challenge coordinate sample := by simp

/-- Public scalar-affine ciphertext transform: inverse-scale the challenge and add the public
offset phase to the body. -/
def scalarAffineTranslateBatch {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) (offset : Fin dimension → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  let challenge := scaleChallenge multiplier⁻¹ ciphertext.1
  (challenge, ciphertext.2 + vecMul offset challenge)

/-- The scalar-affine public transform preserves message and error exactly while changing the
encryption key from `secret` to `multiplier * secret + offset`. -/
theorem scalarAffineTranslateBatch_batchAssemble
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (multiplier : Rˣ) (offset secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) :
    scalarAffineTranslateBatch multiplier offset
        (TLWE.batchAssemble secret challenge message error) =
      TLWE.batchAssemble (scalarAffineSecret multiplier offset secret)
        (scaleChallenge multiplier⁻¹ challenge) message error := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [scalarAffineTranslateBatch, TLWE.batchAssemble, Pi.add_apply]
    rw [show vecMul (scalarAffineSecret multiplier offset secret)
          (scaleChallenge multiplier⁻¹ challenge) sample =
        (vecMul secret challenge +
          vecMul offset (scaleChallenge multiplier⁻¹ challenge)) sample by
      exact congrFun
        (vecMul_scalarAffineSecret_scaleChallenge_inv
          multiplier offset secret challenge) sample]
    simp only [Pi.add_apply]
    abel

/-- Scalar-affine key transport also preserves the complete fresh batch-encryption law.  The
inverse-scaled public challenge is still uniform, while the message and error samples are left
unchanged. -/
theorem scalarAffineTranslateBatch_batchEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ} (errorSampler : ProbComp R)
    (multiplier : Rˣ) (offset secret : Fin dimension → R)
    (message : Fin samples → R) :
    evalDist (scalarAffineTranslateBatch multiplier offset <$>
        TLWE.batchEncrypt dimension samples errorSampler secret message) =
      evalDist (TLWE.batchEncrypt dimension samples errorSampler
        (scalarAffineSecret multiplier offset secret) message) := by
  let errors := ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin dimension) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble (scalarAffineSecret multiplier offset secret)
          challenge message error) :
          ProbComp (TLWE.BatchCiphertext R dimension samples))
  rw [show TLWE.batchEncrypt dimension samples errorSampler secret message =
      (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble secret challenge message error)) by
    simp [TLWE.batchEncrypt, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          finish (scaleChallenge multiplier⁻¹ challenge) error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun challenge => ?_
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [finish] using congrArg evalDist
        (congrArg pure (scalarAffineTranslateBatch_batchAssemble
          multiplier offset secret challenge message error))
    _ = evalDist ((scaleChallenge multiplier⁻¹ <$>
          ($ᵗ Matrix (Fin dimension) (Fin samples) R)) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      rw [evalDist_bind, scaleChallenge_uniform_evalDist multiplier⁻¹,
        ← evalDist_bind]
    _ = _ := by
      simp [TLWE.batchEncrypt, errors, finish, monad_norm]

/-! ## Complementing a batch message under symmetric noise -/

/-- Negate every TLWE row and add one public row-wise phase.  At a fixed key this changes the
message vector from `message` to `shift - message` and negates the error vector. -/
def complementBatchMessage {R : Type} [Ring R] {dimension samples : ℕ}
    (shift : Fin samples → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  (-ciphertext.1, -ciphertext.2 + shift)

theorem complementBatchMessage_batchAssemble
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error shift : Fin samples → R) :
    complementBatchMessage shift
        (TLWE.batchAssemble secret challenge message error) =
      TLWE.batchAssemble secret (-challenge) (shift - message) (-error) := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [complementBatchMessage, TLWE.batchAssemble, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply, Matrix.vecMul, dotProduct, Matrix.neg_apply]
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
    ring

/-- If the scalar/ring error law is invariant under negation, the public batch-message
complement is an exact distributional transport. -/
theorem complementBatchMessage_batchEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ} (errorSampler : ProbComp R)
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (secret : Fin dimension → R) (message shift : Fin samples → R) :
    evalDist (complementBatchMessage shift <$>
        TLWE.batchEncrypt dimension samples errorSampler secret message) =
      evalDist (TLWE.batchEncrypt dimension samples errorSampler secret
        (shift - message)) := by
  have hnegateChallenge :
      (fun challenge : Matrix (Fin dimension) (Fin samples) R => -challenge) =
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateChallenge := by
    funext challenge coordinate sample
    rfl
  let errors := ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin dimension) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble secret challenge (shift - message) error) :
          ProbComp (TLWE.BatchCiphertext R dimension samples))
  rw [show TLWE.batchEncrypt dimension samples errorSampler secret message =
      (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble secret challenge message error)) by
    simp [TLWE.batchEncrypt, errors, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish (-challenge) (-error)) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun challenge => ?_
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [finish] using congrArg evalDist
        (congrArg pure (complementBatchMessage_batchAssemble
          secret challenge message error shift))
    _ = evalDist (((fun challenge : Matrix (Fin dimension) (Fin samples) R => -challenge) <$>
          ($ᵗ Matrix (Fin dimension) (Fin samples) R)) >>= fun challenge =>
        ((fun error : Fin samples → R => -error) <$> errors) >>= fun error =>
          finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        ((fun error : Fin samples → R => -error) <$> errors) >>= fun error =>
          finish challenge error) := by
      rw [evalDist_bind, hnegateChallenge,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negateChallenge_uniform_evalDist,
        ← evalDist_bind]
    _ = evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error => finish challenge error) := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R)
        fun _ => ?_
      rw [evalDist_bind,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negate_sampleIID_evalDist
          samples errorSampler hsymmetric,
        ← evalDist_bind]
    _ = _ := by
      simp [TLWE.batchEncrypt, errors, finish, monad_norm]

/-! ## Characteristic-two agreement -/

/-- Boolean XOR embedding agrees with ring addition exactly in characteristic two. -/
theorem embed_maskedBit_eq_add_of_two_eq_zero
    {R : Type} [Ring R] (hTwo : (2 : R) = 0) (secret mask : Bool) :
    embedBit (R := R) (LWE.MultiKeyAffine.maskedBit secret mask) =
      embedBit secret + embedBit mask := by
  cases secret <;> cases mask <;>
    simp [LWE.MultiKeyAffine.maskedBit, embedBit]
  rw [one_add_one_eq_two, hTwo]

/-- At coefficient characteristic two, embedding a masked binary polynomial is addition of the
embedded source and mask polynomials. -/
theorem embedBinaryPolynomial_masked_eq_add_of_two_eq_zero
    {q degree : ℕ} (hTwo : (2 : ZMod q) = 0)
    (secret mask : BinarySecret degree) :
    embedBinaryPolynomial q degree
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret mask) =
      embedBinaryPolynomial q degree secret + embedBinaryPolynomial q degree mask := by
  apply
    (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q degree).injective
  funext coefficient
  simp only [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients]
  exact embed_maskedBit_eq_add_of_two_eq_zero hTwo
    (secret coefficient) (mask coefficient)

/-- The characteristic-two identity lifts componentwise to a complete native ring secret. -/
theorem embedRingSecret_masked_eq_add_of_two_eq_zero
    {q rank degree : ℕ} (hTwo : (2 : ZMod q) = 0)
    (secret mask : RingBinarySecret rank degree) :
    embedRingSecret q (maskedRingSecret secret mask) =
      embedRingSecret q secret + embedRingSecret q mask := by
  funext component
  exact embedBinaryPolynomial_masked_eq_add_of_two_eq_zero hTwo
    (secret component) (mask component)

/-- Existence of the mask-only additive key correction used by the direct CircLWE
randomization route. -/
def AdditiveXorTransport (q rank degree : ℕ)
    (mask : RingBinarySecret rank degree) : Prop :=
  ∃ delta : Fin rank → RLWE.Rq q degree,
    ∀ secret : RingBinarySecret rank degree,
      embedRingSecret q (maskedRingSecret secret mask) =
        embedRingSecret q secret + delta

/-- Every complete binary mask has an additive implementation at coefficient modulus two. -/
theorem additiveXorTransport_zmod_two {rank degree : ℕ}
    (mask : RingBinarySecret rank degree) :
    AdditiveXorTransport 2 rank degree mask := by
  refine ⟨embedRingSecret 2 mask, ?_⟩
  intro secret
  exact embedRingSecret_masked_eq_add_of_two_eq_zero
    (q := 2) (ZMod.natCast_self 2) secret mask

/-- Consequently, at coefficient modulus two, the public additive ciphertext translation
implements complete binary XOR key transport exactly. -/
theorem additiveTranslateBatch_batchAssemble_masked_zmod_two
    {rank degree samples : ℕ}
    (secret mask : RingBinarySecret rank (degree + 1))
    (challenge : Matrix (Fin rank) (Fin samples) (RLWE.Rq 2 (degree + 1)))
    (message error : Fin samples → RLWE.Rq 2 (degree + 1)) :
    additiveTranslateBatch (embedRingSecret 2 mask)
        (TLWE.batchAssemble (embedRingSecret 2 secret) challenge message error) =
      TLWE.batchAssemble (embedRingSecret 2 (maskedRingSecret secret mask))
        challenge message error := by
  rw [embedRingSecret_masked_eq_add_of_two_eq_zero
    (q := 2) (ZMod.natCast_self 2)]
  exact additiveTranslateBatch_batchAssemble
    (embedRingSecret 2 secret) (embedRingSecret 2 mask) challenge message error

/-! ## Obstruction at native moduli larger than two -/

/-- Outside characteristic two, no single additive correction toggles both possible embedded
bit values. -/
theorem no_constant_additive_xor_toggle
    {R : Type} [Ring R] (hTwo : (2 : R) ≠ 0) :
    ¬ ∃ delta : R, ∀ secret : Bool,
      embedBit (R := R) (LWE.MultiKeyAffine.maskedBit secret true) =
        embedBit secret + delta := by
  rintro ⟨delta, hdelta⟩
  have hfalse := hdelta false
  have htrue := hdelta true
  simp [LWE.MultiKeyAffine.maskedBit, embedBit] at hfalse htrue
  apply hTwo
  rw [← one_add_one_eq_two]
  calc
    1 + 1 = 1 + delta := congrArg (fun value ↦ 1 + value) hfalse
    _ = 0 := htrue.symm

/-- A modulus strictly larger than two has nonzero `2`. -/
theorem zmod_two_ne_zero_of_two_lt {q : ℕ} (hq : 2 < q) :
    (2 : ZMod q) ≠ 0 := by
  intro hzero
  have hcast : (Nat.cast 2 : ZMod q) = 0 := by simpa using hzero
  exact (Nat.not_dvd_of_pos_of_lt (by omega) hq)
    ((ZMod.natCast_eq_zero_iff 2 q).mp hcast)

/-- At `q > 2`, a nontrivial coefficientwise XOR mask cannot be represented by adding one
mask-dependent polynomial uniformly for all binary source polynomials. -/
theorem no_additive_binaryPolynomial_xor_transport
    {q degree : ℕ} (hq : 2 < q) (mask : BinarySecret degree)
    (coefficient : Fin degree) (hmask : mask coefficient = true) :
    ¬ ∃ delta : RLWE.Rq q degree, ∀ secret : BinarySecret degree,
      embedBinaryPolynomial q degree
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            secret mask) =
        embedBinaryPolynomial q degree secret + delta := by
  intro htransport
  apply no_constant_additive_xor_toggle (zmod_two_ne_zero_of_two_lt hq)
  obtain ⟨delta, hdelta⟩ := htransport
  refine ⟨FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
    q degree delta coefficient, ?_⟩
  intro secretBit
  have h := congrArg
    (fun polynomial ↦
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        q degree polynomial coefficient)
    (hdelta (fun _ ↦ secretBit))
  simpa only [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret, Pi.add_apply,
    hmask] using h

/-- The polynomial obstruction lifts to the exact complete native master-key type.  If any
coefficient of the public binary mask is set, there is no mask-only additive ring vector that
implements full-master XOR for every binary master key at `q > 2`. -/
theorem no_additive_ringSecret_xor_transport
    {q rank degree : ℕ} (hq : 2 < q)
    (mask : RingBinarySecret rank degree)
    (component : Fin rank) (coefficient : Fin degree)
    (hmask : mask component coefficient = true) :
    ¬ ∃ delta : Fin rank → RLWE.Rq q degree,
      ∀ secret : RingBinarySecret rank degree,
        embedRingSecret q (maskedRingSecret secret mask) =
          embedRingSecret q secret + delta := by
  intro htransport
  apply no_additive_binaryPolynomial_xor_transport hq (mask component) coefficient hmask
  obtain ⟨delta, hdelta⟩ := htransport
  refine ⟨delta component, ?_⟩
  intro polynomial
  have h := congrFun (hdelta (fun _ ↦ polynomial)) component
  simpa only [embedRingSecret, maskedRingSecret, Pi.add_apply] using h

/-- At a modulus larger than two, a complete binary mask has an additive implementation exactly
when every one of its coefficients is false. -/
theorem additiveXorTransport_iff_all_false
    {q rank degree : ℕ} (hq : 2 < q)
    (mask : RingBinarySecret rank degree) :
    AdditiveXorTransport q rank degree mask ↔
      ∀ component coefficient, mask component coefficient = false := by
  constructor
  · intro htransport component coefficient
    cases hbit : mask component coefficient with
    | false => rfl
    | true =>
        exact False.elim
          (no_additive_ringSecret_xor_transport hq mask component coefficient hbit
            htransport)
  · intro hfalse
    refine ⟨fun _ ↦ embedBinaryPolynomial q degree (fun _ ↦ false), ?_⟩
    intro secret
    have hmasked : maskedRingSecret secret mask = secret := by
      funext component coefficient
      simp [maskedRingSecret,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        hfalse component coefficient, LWE.MultiKeyAffine.maskedBit]
    rw [hmasked]
    funext component
    apply
      (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        q degree).injective
    funext coefficient
    simp [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients, embedBit]

/-- Direct specialization to the exact shared-randomness one-cycle search secret.  Toggling any
master coefficient at `q > 2` rules out the mask-only additive transport used by the standard
CircLWE search-to-decision randomizer. -/
theorem no_additive_oneCycle_searchSecret_xor_transport
    {q prefixDimension suffixDimension : ℕ} (hq : 2 < q)
    (mask : AuxiliaryInput.Search.Secret prefixDimension suffixDimension)
    (coefficient : Fin (prefixDimension + suffixDimension))
    (hmask : mask 0 coefficient = true) :
    ¬ AdditiveXorTransport q 1 (prefixDimension + suffixDimension) mask :=
  no_additive_ringSecret_xor_transport hq mask 0 coefficient hmask

/-! ## Classification of scalar-affine ring transports -/

/-- The all-false binary coefficient polynomial. -/
def allFalsePolynomial (degree : ℕ) : BinarySecret degree := fun _ ↦ false

/-- The all-true binary coefficient polynomial. -/
def allTruePolynomial (degree : ℕ) : BinarySecret degree := fun _ ↦ true

/-- The binary coefficient polynomial supported at exactly one coordinate. -/
def basisPolynomial {degree : ℕ} (coordinate : Fin degree) : BinarySecret degree :=
  fun input ↦ decide (input = coordinate)

@[simp]
theorem maskedSecret_allFalsePolynomial {degree : ℕ}
    (mask : BinarySecret degree) :
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
        (allFalsePolynomial degree) mask = mask := by
  funext coefficient
  simp [FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
    allFalsePolynomial, LWE.MultiKeyAffine.maskedBit]

@[simp]
theorem embedBinaryPolynomial_allFalse (q degree : ℕ) :
    embedBinaryPolynomial q degree (allFalsePolynomial degree) = 0 := by
  apply
    (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q degree).injective
  funext coefficient
  simp [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_zero,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
    allFalsePolynomial, embedBit]

/-- Coefficient extraction commutes with negation in the executable ring carrier. -/
theorem coefficientEquiv_neg (q degree : ℕ) (value : RLWE.Rq q degree) :
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        q degree (-value) =
      -FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        q degree value := by
  funext coefficient
  exact LatticeCrypto.NegacyclicRing.coeff_neg
    (RLWE.negacyclicRing q degree) value coefficient

/-- The basis polynomial at coefficient zero is the ring unit at positive degree. -/
theorem embedBinaryPolynomial_basis_zero_eq_one
    {q degree : ℕ} [NeZero q] :
    embedBinaryPolynomial q (degree + 1)
        (basisPolynomial (0 : Fin (degree + 1))) = 1 := by
  apply
    (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q (degree + 1)).injective
  funext coefficient
  rw [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial]
  change embedBit (basisPolynomial (0 : Fin (degree + 1)) coefficient) =
    LatticeCrypto.Poly.toPi (1 : RLWE.Rq q (degree + 1)) coefficient
  rw [BlindRotation.rq_one_coefficient]
  simp [basisPolynomial, embedBit]

/-- If the selected mask bit is false, toggling a one-hot source adds that one-hot polynomial to
the embedded mask. -/
theorem embedBinaryPolynomial_masked_basis_of_false
    {q degree : ℕ} (mask : BinarySecret degree) (coordinate : Fin degree)
    (hmask : mask coordinate = false) :
    embedBinaryPolynomial q degree
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          (basisPolynomial coordinate) mask) =
      embedBinaryPolynomial q degree (basisPolynomial coordinate) +
        embedBinaryPolynomial q degree mask := by
  apply
    (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q degree).injective
  funext coefficient
  simp only [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
    Pi.add_apply]
  by_cases hcoordinate : coefficient = coordinate
  · subst coefficient
    simp [basisPolynomial,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
      LWE.MultiKeyAffine.maskedBit, hmask, embedBit]
  · cases hcoefficient : mask coefficient <;>
      simp [basisPolynomial, hcoordinate,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        LWE.MultiKeyAffine.maskedBit, hcoefficient, embedBit]

/-- If the selected mask bit is true, toggling a one-hot source subtracts that one-hot polynomial
from the embedded mask. -/
theorem embedBinaryPolynomial_masked_basis_of_true
    {q degree : ℕ} (mask : BinarySecret degree) (coordinate : Fin degree)
    (hmask : mask coordinate = true) :
    embedBinaryPolynomial q degree
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          (basisPolynomial coordinate) mask) =
      -embedBinaryPolynomial q degree (basisPolynomial coordinate) +
        embedBinaryPolynomial q degree mask := by
  apply
    (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q degree).injective
  funext coefficient
  simp only [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    coefficientEquiv_neg,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
    Pi.add_apply, Pi.neg_apply]
  by_cases hcoordinate : coefficient = coordinate
  · subst coefficient
    simp [basisPolynomial,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
      LWE.MultiKeyAffine.maskedBit, hmask, embedBit]
  · cases hcoefficient : mask coefficient <;>
      simp [basisPolynomial, hcoordinate,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        LWE.MultiKeyAffine.maskedBit, hcoefficient, embedBit]

/-- Complementing every binary coefficient is the scalar-affine ring map `s ↦ -s + 1⃗`. -/
theorem embedBinaryPolynomial_masked_allTrue
    {q degree : ℕ} (secret : BinarySecret degree) :
    embedBinaryPolynomial q degree
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret (allTruePolynomial degree)) =
      -embedBinaryPolynomial q degree secret +
        embedBinaryPolynomial q degree (allTruePolynomial degree) := by
  apply
    (FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
      q degree).injective
  funext coefficient
  simp only [FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add,
    coefficientEquiv_neg,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
    FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
    Pi.add_apply, Pi.neg_apply]
  cases hsecret : secret coefficient <;>
    simp [hsecret, allTruePolynomial,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
      LWE.MultiKeyAffine.maskedBit, embedBit]

/-- Even allowing an arbitrary public ring multiplier and offset, can coefficientwise XOR by the
fixed mask be expressed as one scalar-affine ring map for every binary source polynomial? -/
def ScalarAffineXorTransport (q degree : ℕ) (mask : BinarySecret degree) : Prop :=
  ∃ multiplier offset : RLWE.Rq q degree,
    ∀ secret : BinarySecret degree,
      embedBinaryPolynomial q degree
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            secret mask) =
        multiplier * embedBinaryPolynomial q degree secret + offset

/-- In a ring where two is nonzero, one and negative one are distinct. -/
theorem one_ne_neg_one_of_two_ne_zero
    {R : Type} [Ring R] (hTwo : (2 : R) ≠ 0) : (1 : R) ≠ -1 := by
  intro hone
  apply hTwo
  calc
    (2 : R) = 1 + 1 := one_add_one_eq_two.symm
    _ = 1 + (-1) := congrArg (fun value : R ↦ 1 + value) hone
    _ = 0 := by simp

/-- A one-hot binary polynomial is not equal to its negative when `2 ≠ 0`. -/
theorem embedBinaryPolynomial_basis_ne_neg
    {q degree : ℕ} (hTwo : (2 : ZMod q) ≠ 0)
    (coordinate : Fin degree) :
    embedBinaryPolynomial q degree (basisPolynomial coordinate) ≠
      -embedBinaryPolynomial q degree (basisPolynomial coordinate) := by
  intro heq
  have hcoefficient := congrArg
    (fun polynomial ↦
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
        q degree polynomial coordinate) heq
  have hone : (1 : ZMod q) = -1 := by
    simpa [coefficientEquiv_neg,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_embedBinaryPolynomial,
      FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE.binaryCoefficients,
      basisPolynomial, embedBit] using hcoefficient
  exact one_ne_neg_one_of_two_ne_zero hTwo hone

/-- Any scalar-affine implementation at `q > 2` forces every mask coefficient to agree with the
constant coefficient. -/
theorem scalarAffineXorTransport_imp_constant
    {q degree : ℕ} [NeZero q] (hq : 2 < q)
    (mask : BinarySecret (degree + 1))
    (htransport : ScalarAffineXorTransport q (degree + 1) mask) :
    ∀ coordinate, mask coordinate = mask 0 := by
  obtain ⟨multiplier, offset, hmap⟩ := htransport
  have hzero := hmap (allFalsePolynomial (degree + 1))
  rw [maskedSecret_allFalsePolynomial,
    embedBinaryPolynomial_allFalse, mul_zero, zero_add] at hzero
  have hoffset : offset = embedBinaryPolynomial q (degree + 1) mask := hzero.symm
  have hconstant := hmap (basisPolynomial (0 : Fin (degree + 1)))
  rw [embedBinaryPolynomial_basis_zero_eq_one, mul_one, hoffset] at hconstant
  cases hmaskZero : mask (0 : Fin (degree + 1)) with
  | false =>
      rw [embedBinaryPolynomial_masked_basis_of_false mask 0 hmaskZero,
        embedBinaryPolynomial_basis_zero_eq_one] at hconstant
      have hmultiplier : multiplier = 1 := (add_right_cancel hconstant).symm
      intro coordinate
      cases hmaskCoordinate : mask coordinate with
      | false => rfl
      | true =>
          exfalso
          have hcoordinate := hmap (basisPolynomial coordinate)
          rw [embedBinaryPolynomial_masked_basis_of_true mask coordinate
              hmaskCoordinate,
            hmultiplier, one_mul, hoffset] at hcoordinate
          have heq :
              embedBinaryPolynomial q (degree + 1) (basisPolynomial coordinate) =
                -embedBinaryPolynomial q (degree + 1) (basisPolynomial coordinate) :=
            (add_right_cancel hcoordinate).symm
          exact embedBinaryPolynomial_basis_ne_neg
            (zmod_two_ne_zero_of_two_lt hq) coordinate heq
  | true =>
      rw [embedBinaryPolynomial_masked_basis_of_true mask 0 hmaskZero,
        embedBinaryPolynomial_basis_zero_eq_one] at hconstant
      have hmultiplier : multiplier = -1 := (add_right_cancel hconstant).symm
      intro coordinate
      cases hmaskCoordinate : mask coordinate with
      | true => rfl
      | false =>
          exfalso
          have hcoordinate := hmap (basisPolynomial coordinate)
          rw [embedBinaryPolynomial_masked_basis_of_false mask coordinate
              hmaskCoordinate,
            hmultiplier, neg_one_mul, hoffset] at hcoordinate
          have heq :
              embedBinaryPolynomial q (degree + 1) (basisPolynomial coordinate) =
                -embedBinaryPolynomial q (degree + 1) (basisPolynomial coordinate) :=
            add_right_cancel hcoordinate
          exact embedBinaryPolynomial_basis_ne_neg
            (zmod_two_ne_zero_of_two_lt hq) coordinate heq

/-- The all-false mask is implemented by the identity ring map. -/
theorem scalarAffineXorTransport_of_all_false
    {q degree : ℕ} (mask : BinarySecret (degree + 1))
    (hfalse : ∀ coordinate, mask coordinate = false) :
    ScalarAffineXorTransport q (degree + 1) mask := by
  refine ⟨1, 0, ?_⟩
  intro secret
  have hmasked :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret mask = secret := by
    funext coordinate
    simp [FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
      hfalse coordinate, LWE.MultiKeyAffine.maskedBit]
  rw [hmasked]
  simp only [one_mul, add_zero]

/-- The all-true mask is implemented by the global-complement map `s ↦ -s + 1⃗`. -/
theorem scalarAffineXorTransport_of_all_true
    {q degree : ℕ} (mask : BinarySecret (degree + 1))
    (htrue : ∀ coordinate, mask coordinate = true) :
    ScalarAffineXorTransport q (degree + 1) mask := by
  have hmask : mask = allTruePolynomial (degree + 1) := by
    funext coordinate
    exact htrue coordinate
  subst mask
  refine ⟨-1, embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)), ?_⟩
  intro secret
  rw [embedBinaryPolynomial_masked_allTrue]
  simp only [neg_one_mul]

/-- Complete classification: at every `q > 2`, scalar-affine ring transport implements exactly
the two constant XOR masks, identity and global complement. -/
theorem scalarAffineXorTransport_iff_constant
    {q degree : ℕ} (hq : 2 < q) (mask : BinarySecret (degree + 1)) :
    ScalarAffineXorTransport q (degree + 1) mask ↔
      (∀ coordinate, mask coordinate = false) ∨
        (∀ coordinate, mask coordinate = true) := by
  letI : NeZero q := ⟨by omega⟩
  constructor
  · intro htransport
    have hconstant := scalarAffineXorTransport_imp_constant hq mask htransport
    cases hzero : mask (0 : Fin (degree + 1)) with
    | false =>
        left
        intro coordinate
        simpa only [hzero] using hconstant coordinate
    | true =>
        right
        intro coordinate
        simpa only [hzero] using hconstant coordinate
  · rintro (hfalse | htrue)
    · exact scalarAffineXorTransport_of_all_false mask hfalse
    · exact scalarAffineXorTransport_of_all_true mask htrue

/-! ## Exact quotient left by global complement -/

/-- The relative binary key records every nonconstant coefficient against coefficient zero.
It is the complete invariant of the identity/global-complement action. -/
def relativeBinarySecret {degree : ℕ}
    (secret : BinarySecret (degree + 1)) : BinarySecret degree :=
  fun coordinate ↦ LWE.MultiKeyAffine.maskedBit (secret 0) (secret coordinate.succ)

/-- Reconstruct a positive-length binary key from its coefficient-zero anchor and relative key. -/
def assembleRelativeBinarySecret {degree : ℕ}
    (anchor : Bool) (relative : BinarySecret degree) : BinarySecret (degree + 1) :=
  Fin.cases anchor fun coordinate ↦
    LWE.MultiKeyAffine.maskedBit anchor (relative coordinate)

@[simp]
theorem relativeBinarySecret_assembleRelativeBinarySecret
    {degree : ℕ} (anchor : Bool) (relative : BinarySecret degree) :
    relativeBinarySecret (assembleRelativeBinarySecret anchor relative) = relative := by
  funext coordinate
  exact LWE.MultiKeyAffine.maskedBit_involutive anchor (relative coordinate)

@[simp]
theorem assembleRelativeBinarySecret_relativeBinarySecret
    {degree : ℕ} (secret : BinarySecret (degree + 1)) :
    assembleRelativeBinarySecret (secret 0) (relativeBinarySecret secret) = secret := by
  funext coordinate
  refine Fin.cases ?_ (fun tailCoordinate ↦ ?_) coordinate
  · rfl
  · exact LWE.MultiKeyAffine.maskedBit_involutive
      (secret 0) (secret tailCoordinate.succ)

/-- A positive-length binary secret is exactly a relative key together with one global anchor
bit.  The latter is the only coordinate randomized by global complement. -/
def relativeBinarySecretEquiv (degree : ℕ) :
    BinarySecret (degree + 1) ≃ BinarySecret degree × Bool where
  toFun secret := (relativeBinarySecret secret, secret 0)
  invFun decomposed := assembleRelativeBinarySecret decomposed.2 decomposed.1
  left_inv := assembleRelativeBinarySecret_relativeBinarySecret
  right_inv decomposed := by
    apply Prod.ext
    · exact relativeBinarySecret_assembleRelativeBinarySecret decomposed.2 decomposed.1
    · rfl

/-- The complete binary key decomposes into an independent uniform relative key and one uniform
global anchor bit. -/
theorem relativeBinarySecretEquiv_uniform_evalDist (degree : ℕ) :
    evalDist (relativeBinarySecretEquiv degree <$>
        ($ᵗ BinarySecret (degree + 1))) =
      evalDist ($ᵗ (BinarySecret degree × Bool)) :=
  evalDist_map_bijective_uniform_cross
    (α := BinarySecret (degree + 1)) (β := BinarySecret degree × Bool)
    (relativeBinarySecretEquiv degree) (relativeBinarySecretEquiv degree).bijective

/-- In particular, the relative invariant of a fresh complete binary key is itself fresh and
uniform. -/
theorem relativeBinarySecret_uniform_evalDist (degree : ℕ) :
    evalDist (relativeBinarySecret <$> ($ᵗ BinarySecret (degree + 1))) =
      evalDist ($ᵗ BinarySecret degree) := by
  calc
    evalDist (relativeBinarySecret <$> ($ᵗ BinarySecret (degree + 1))) =
        evalDist (Prod.fst <$> (relativeBinarySecretEquiv degree <$>
          ($ᵗ BinarySecret (degree + 1)))) := by
      simp [relativeBinarySecretEquiv, Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ (BinarySecret degree × Bool))) := by
      exact evalDist_map_eq_of_evalDist_eq
        (relativeBinarySecretEquiv_uniform_evalDist degree) Prod.fst
    _ = evalDist ($ᵗ BinarySecret degree) := evalDist_map_fst_uniformSample_prod

/-- Select identity or global complement using one Boolean action bit. -/
def globalComplementAction {degree : ℕ}
    (secret : BinarySecret degree) (toggle : Bool) : BinarySecret degree :=
  FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
    secret (fun _ ↦ toggle)

/-- Global complement changes the anchor but preserves every relative key bit exactly. -/
@[simp]
theorem relativeBinarySecret_globalComplementAction
    {degree : ℕ} (secret : BinarySecret (degree + 1)) (toggle : Bool) :
    relativeBinarySecret (globalComplementAction secret toggle) =
      relativeBinarySecret secret := by
  funext coordinate
  cases hzero : secret 0 <;>
    cases hcoordinate : secret coordinate.succ <;>
      cases toggle <;>
        simp [relativeBinarySecret, globalComplementAction,
          FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
          LWE.MultiKeyAffine.maskedBit, hzero, hcoordinate]

/-- Under the exact decomposition equivalence, global complement fixes the relative key and XORs
only the anchor bit. -/
theorem relativeBinarySecretEquiv_globalComplementAction
    {degree : ℕ} (secret : BinarySecret (degree + 1)) (toggle : Bool) :
    relativeBinarySecretEquiv degree (globalComplementAction secret toggle) =
      (relativeBinarySecret secret,
        LWE.MultiKeyAffine.maskedBit (secret 0) toggle) := by
  apply Prod.ext
  · exact relativeBinarySecret_globalComplementAction secret toggle
  · rfl

/-- Full coefficientwise XOR decomposes into independent XOR on the relative key and on the
global anchor bit. -/
theorem relativeBinarySecretEquiv_maskedSecret
    {degree : ℕ} (secret mask : BinarySecret (degree + 1)) :
    relativeBinarySecretEquiv degree
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret mask) =
      (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          (relativeBinarySecret secret) (relativeBinarySecret mask),
        LWE.MultiKeyAffine.maskedBit (secret 0) (mask 0)) := by
  apply Prod.ext
  · funext coordinate
    cases hsecretZero : secret 0 <;>
      cases hsecretCoordinate : secret coordinate.succ <;>
        cases hmaskZero : mask 0 <;>
          cases hmaskCoordinate : mask coordinate.succ <;>
            simp [relativeBinarySecret, relativeBinarySecretEquiv,
              FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
              LWE.MultiKeyAffine.maskedBit, hsecretZero, hsecretCoordinate,
              hmaskZero, hmaskCoordinate]
  · rfl

/-- Lift a relative mask to the unique complete mask whose global anchor bit is false. -/
def relativeMaskLift {degree : ℕ}
    (relativeMask : BinarySecret degree) : BinarySecret (degree + 1) :=
  assembleRelativeBinarySecret false relativeMask

@[simp]
theorem relativeBinarySecret_relativeMaskLift
    {degree : ℕ} (relativeMask : BinarySecret degree) :
    relativeBinarySecret (relativeMaskLift relativeMask) = relativeMask :=
  relativeBinarySecret_assembleRelativeBinarySecret false relativeMask

@[simp]
theorem relativeMaskLift_zero
    {degree : ℕ} (relativeMask : BinarySecret degree) :
    relativeMaskLift relativeMask 0 = false := by
  rfl

/-- Every full XOR action factors exactly into a normalized relative-mask action followed by the
publicly scalar-affine global-complement action. -/
theorem maskedSecret_eq_relativeMask_then_globalComplement
    {degree : ℕ} (secret mask : BinarySecret (degree + 1)) :
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret mask =
      globalComplementAction
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret
          (relativeMaskLift (relativeBinarySecret mask)))
        (mask 0) := by
  funext coordinate
  refine Fin.cases ?_ (fun tailCoordinate ↦ ?_) coordinate
  · cases hsecret : secret 0 <;> cases hmask : mask 0 <;>
      simp [globalComplementAction,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
        relativeMaskLift, assembleRelativeBinarySecret,
        LWE.MultiKeyAffine.maskedBit, hsecret, hmask]
  · cases hsecretCoordinate : secret tailCoordinate.succ <;>
      cases hmaskZero : mask 0 <;>
        cases hmaskCoordinate : mask tailCoordinate.succ <;>
          simp [globalComplementAction, relativeBinarySecret, relativeMaskLift,
            assembleRelativeBinarySecret,
            FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
            LWE.MultiKeyAffine.maskedBit, hsecretCoordinate,
            hmaskZero, hmaskCoordinate]

/-- The factored action takes a relative mask and a global-complement bit as separate inputs. -/
def relativeGlobalAction {degree : ℕ}
    (secret : BinarySecret (degree + 1))
    (decomposedMask : BinarySecret degree × Bool) : BinarySecret (degree + 1) :=
  globalComplementAction
    (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret
      (relativeMaskLift decomposedMask.1))
    decomposedMask.2

/-- Decomposing a complete mask and applying the factored action is exactly ordinary full XOR. -/
@[simp]
theorem relativeGlobalAction_relativeBinarySecretEquiv
    {degree : ℕ} (secret mask : BinarySecret (degree + 1)) :
    relativeGlobalAction secret (relativeBinarySecretEquiv degree mask) =
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret mask := by
  exact (maskedSecret_eq_relativeMask_then_globalComplement secret mask).symm

/-- The factored mask space has the exact fresh-secret law.  Hence a future construction only
needs a nonlinear evaluator for normalized relative masks; the final independent anchor step is
already supplied by global scalar-affine transport. -/
theorem relativeGlobalAction_uniform_evalDist
    {degree : ℕ} (secret : BinarySecret (degree + 1)) :
    evalDist (relativeGlobalAction secret <$>
        ($ᵗ (BinarySecret degree × Bool))) =
      evalDist ($ᵗ BinarySecret (degree + 1)) := by
  calc
    evalDist (relativeGlobalAction secret <$>
        ($ᵗ (BinarySecret degree × Bool))) =
      evalDist (relativeGlobalAction secret <$>
        (relativeBinarySecretEquiv degree <$>
          ($ᵗ BinarySecret (degree + 1)))) := by
      exact evalDist_map_eq_of_evalDist_eq
        (relativeBinarySecretEquiv_uniform_evalDist degree).symm
        (relativeGlobalAction secret)
    _ = evalDist
        (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret secret <$>
          ($ᵗ BinarySecret (degree + 1))) := by
      simp only [Functor.map_map,
        relativeGlobalAction_relativeBinarySecretEquiv]
    _ = evalDist ($ᵗ BinarySecret (degree + 1)) :=
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret_uniform_evalDist secret

/-- Sampling identity/global complement uniformly refreshes exactly the one anchor bit while the
complete relative key remains fixed. -/
theorem globalComplementAction_decomposed_uniform_evalDist
    {degree : ℕ} (secret : BinarySecret (degree + 1)) :
    evalDist (relativeBinarySecretEquiv degree <$>
        (globalComplementAction secret <$> ($ᵗ Bool))) =
      evalDist ((fun anchor ↦ (relativeBinarySecret secret, anchor)) <$>
        ($ᵗ Bool)) := by
  let anchorEquiv : Bool ≃ Bool :=
    { toFun := LWE.MultiKeyAffine.maskedBit (secret 0)
      invFun := LWE.MultiKeyAffine.maskedBit (secret 0)
      left_inv := LWE.MultiKeyAffine.maskedBit_involutive (secret 0)
      right_inv := LWE.MultiKeyAffine.maskedBit_involutive (secret 0) }
  have hanchor :
      evalDist (LWE.MultiKeyAffine.maskedBit (secret 0) <$> ($ᵗ Bool)) =
        evalDist ($ᵗ Bool) :=
    evalDist_map_bijective_uniform_cross
      (α := Bool) (β := Bool)
      (LWE.MultiKeyAffine.maskedBit (secret 0)) anchorEquiv.bijective
  rw [Functor.map_map]
  have haction :
      (fun toggle ↦ relativeBinarySecretEquiv degree
        (globalComplementAction secret toggle)) =
        fun toggle ↦
          (relativeBinarySecret secret,
            LWE.MultiKeyAffine.maskedBit (secret 0) toggle) := by
    funext toggle
    exact relativeBinarySecretEquiv_globalComplementAction secret toggle
  rw [haction]
  simpa only [Functor.map_map, Function.comp_apply] using
    (evalDist_map_eq_of_evalDist_eq hanchor
      (fun anchor ↦ (relativeBinarySecret secret, anchor)))

/-! ## Exact global-complement transport for the suffix-only KSK -/

/-- Complementing every source bit changes the KSK message table from `sᵢ gⱼ` to
`gⱼ - sᵢ gⱼ`. -/
theorem keySwitchMessages_globalComplementAction
    {R : Type} [CommRing R] {sourceDimension levels : ℕ}
    (gadget : Fin levels → R) (sourceSecret : BinarySecret sourceDimension) :
    Native.keySwitchMessages sourceDimension levels gadget
        (globalComplementAction sourceSecret true) =
      Native.keySwitchMessages sourceDimension levels gadget
          (allTruePolynomial sourceDimension) -
        Native.keySwitchMessages sourceDimension levels gadget sourceSecret := by
  funext row
  obtain ⟨⟨coordinate, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases hsecret : sourceSecret coordinate <;>
    simp [Native.keySwitchMessages_apply, globalComplementAction,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
      allTruePolynomial, LWE.MultiKeyAffine.maskedBit, hsecret, embedBit]

/-- Publicly negate all KSK rows and add the all-one gadget table.  This complements the source
secret encrypted by the table without changing its target key. -/
def complementKeySwitchSource
    {q targetDimension sourceDimension levels : ℕ}
    (gadget : Fin levels → ZMod q)
    (keySwitchKey : Native.KeySwitchKey q targetDimension sourceDimension levels) :
    Native.KeySwitchKey q targetDimension sourceDimension levels :=
  complementBatchMessage
    (Native.keySwitchMessages sourceDimension levels gadget
      (allTruePolynomial sourceDimension)) keySwitchKey

/-- Under any negation-symmetric scalar noise, source complementation is an exact KSK
distribution identity. -/
theorem complementKeySwitchSource_generate_evalDist
    {q targetDimension sourceDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension) :
    evalDist (complementKeySwitchSource gadget <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget sourceSecret targetSecret) =
      evalDist (Native.generateKeySwitchKey q targetDimension sourceDimension levels
        errorSampler gadget (globalComplementAction sourceSecret true) targetSecret) := by
  change evalDist (complementBatchMessage
      (Native.keySwitchMessages sourceDimension levels gadget
        (allTruePolynomial sourceDimension)) <$>
      TLWE.batchEncrypt targetDimension (sourceDimension * levels) errorSampler
        (embedBinarySecret targetSecret)
        (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)) =
    evalDist (TLWE.batchEncrypt targetDimension (sourceDimension * levels)
      errorSampler (embedBinarySecret targetSecret)
      (Native.keySwitchMessages sourceDimension levels gadget
        (globalComplementAction sourceSecret true)))
  rw [keySwitchMessages_globalComplementAction]
  exact complementBatchMessage_batchEncrypt_evalDist errorSampler hsymmetric
    (embedBinarySecret targetSecret)
    (Native.keySwitchMessages sourceDimension levels gadget sourceSecret)
    (Native.keySwitchMessages sourceDimension levels gadget
      (allTruePolynomial sourceDimension))

/-- Joint public KSK action for the shared-randomness one-cycle layout: complement the suffix
source key and apply the existing exact XOR transport to the prefix target key. -/
def globalComplementKeySwitchKey
    {q targetDimension sourceDimension levels : ℕ}
    (gadget : Fin levels → ZMod q)
    (keySwitchKey : Native.KeySwitchKey q targetDimension sourceDimension levels) :
    Native.KeySwitchKey q targetDimension sourceDimension levels :=
  FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformKeySwitchKey
    (allTruePolynomial targetDimension)
    (complementKeySwitchSource gadget keySwitchKey)

/-- The suffix-only KSK is therefore fully compatible with global complementation of the single
master key.  This removes the KSK from the remaining one-cycle randomization obstruction. -/
theorem globalComplementKeySwitchKey_generate_evalDist
    {q targetDimension sourceDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension) :
    evalDist (globalComplementKeySwitchKey gadget <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget sourceSecret targetSecret) =
      evalDist (Native.generateKeySwitchKey q targetDimension sourceDimension levels
        errorSampler gadget (globalComplementAction sourceSecret true)
          (globalComplementAction targetSecret true)) := by
  let targetTransform :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformKeySwitchKey
      (q := q) (sourceDimension := sourceDimension) (levels := levels)
      (allTruePolynomial targetDimension)
  calc
    _ = evalDist (targetTransform <$>
        (complementKeySwitchSource gadget <$>
          Native.generateKeySwitchKey q targetDimension sourceDimension levels
            errorSampler gadget sourceSecret targetSecret)) := by
      rw [Functor.map_map]
      rfl
    _ = evalDist (targetTransform <$>
        Native.generateKeySwitchKey q targetDimension sourceDimension levels
          errorSampler gadget (globalComplementAction sourceSecret true)
            targetSecret) :=
      evalDist_map_eq_of_evalDist_eq
        (complementKeySwitchSource_generate_evalDist errorSampler hsymmetric gadget
          sourceSecret targetSecret) targetTransform
    _ = evalDist (Native.generateKeySwitchKey q targetDimension sourceDimension levels
        errorSampler gadget (globalComplementAction sourceSecret true)
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            targetSecret (allTruePolynomial targetDimension))) := by
      exact
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.transformKeySwitchKey_generate_evalDist
          errorSampler gadget (globalComplementAction sourceSecret true) targetSecret
            (allTruePolynomial targetDimension)
    _ = _ := rfl

/-- Exact specialization to the suffix-only KSK in the shared-randomness one-cycle cloud key.
Both its suffix source key and prefix target key are complemented by one action on the complete
master ring key. -/
theorem globalComplementKeySwitchKey_generateOneCycle_evalDist
    {q prefixDimension suffixDimension levels : ℕ} [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (gadget : Fin levels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (globalComplementKeySwitchKey gadget <$>
        Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
          suffixDimension levels errorSampler gadget ringSecret) =
      evalDist (Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
        suffixDimension levels errorSampler gadget
        (maskedRingSecret ringSecret
          (fun _ _ ↦ true : RingBinarySecret 1
            (prefixDimension + suffixDimension)))) := by
  let masterMask : RingBinarySecret 1 (prefixDimension + suffixDimension) :=
    fun _ _ ↦ true
  have hsuffix :
      suffixSecret (maskedRingSecret ringSecret masterMask) =
        globalComplementAction (suffixSecret ringSecret) true := by
    rw [suffixSecret_maskedRingSecret]
    rfl
  have hprefix :
      prefixSecret (maskedRingSecret ringSecret masterMask) =
        globalComplementAction (prefixSecret ringSecret) true := by
    rw [prefixSecret_maskedRingSecret]
    rfl
  change evalDist (globalComplementKeySwitchKey gadget <$>
      Native.generateKeySwitchKey q prefixDimension suffixDimension levels
        errorSampler gadget (suffixSecret ringSecret) (prefixSecret ringSecret)) =
    evalDist (Native.generateKeySwitchKey q prefixDimension suffixDimension levels
      errorSampler gadget
        (suffixSecret (maskedRingSecret ringSecret masterMask))
        (prefixSecret (maskedRingSecret ringSecret masterMask)))
  rw [hsuffix, hprefix]
  exact globalComplementKeySwitchKey_generate_evalDist errorSampler hsymmetric gadget
    (suffixSecret ringSecret) (prefixSecret ringSecret)

/-! ## Rank-one BRK complementation and its exact noise boundary -/

/-- The mask-block row at one gadget level in a rank-one TGSW ciphertext. -/
def rankOneMaskRow {levels : ℕ} (level : Fin levels) :
    Fin (TGSW.rowCount 1 levels) :=
  finProdFinEquiv ((0 : Fin (1 + 1)), level)

/-- The body-block row at one gadget level in a rank-one TGSW ciphertext. -/
def rankOneBodyRow {levels : ℕ} (level : Fin levels) :
    Fin (TGSW.rowCount 1 levels) :=
  finProdFinEquiv (Fin.last 1, level)

@[simp]
theorem rankOne_rowIndex_maskRow {levels : ℕ} (level : Fin levels) :
    TGSW.rowIndex (rankOneMaskRow level) = ((0 : Fin (1 + 1)), level) := by
  simp [TGSW.rowIndex, rankOneMaskRow]

@[simp]
theorem rankOne_rowIndex_bodyRow {levels : ℕ} (level : Fin levels) :
    TGSW.rowIndex (rankOneBodyRow level) = (Fin.last 1, level) := by
  simp [TGSW.rowIndex, rankOneBodyRow]

theorem rankOne_row_eq_maskRow_of_index_eq_zero
    {levels : ℕ} (row : Fin (TGSW.rowCount 1 levels))
    (hmask : (TGSW.rowIndex row).1 = 0) :
    row = rankOneMaskRow (TGSW.rowIndex row).2 := by
  calc
    row = finProdFinEquiv (TGSW.rowIndex row) :=
      (finProdFinEquiv.apply_symm_apply row).symm
    _ = finProdFinEquiv ((0 : Fin (1 + 1)), (TGSW.rowIndex row).2) := by
      congr 1
      exact Prod.ext hmask rfl
    _ = rankOneMaskRow (TGSW.rowIndex row).2 := rfl

theorem rankOne_row_eq_bodyRow_of_index_ne_zero
    {levels : ℕ} (row : Fin (TGSW.rowCount 1 levels))
    (hmask : (TGSW.rowIndex row).1 ≠ 0) :
    row = rankOneBodyRow (TGSW.rowIndex row).2 := by
  have hblock : (TGSW.rowIndex row).1 = Fin.last 1 := by
    simpa using Fin.eq_one_of_ne_zero (TGSW.rowIndex row).1 hmask
  calc
    row = finProdFinEquiv (TGSW.rowIndex row) :=
      (finProdFinEquiv.apply_symm_apply row).symm
    _ = finProdFinEquiv (Fin.last 1, (TGSW.rowIndex row).2) := by
      congr 1
      exact Prod.ext hblock rfl
    _ = rankOneBodyRow (TGSW.rowIndex row).2 := rfl

@[simp]
theorem rankOne_gadgetPhase_maskRow
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (message : R)
    (level : Fin levels) :
    TGSW.gadgetPhase secret gadget message (rankOneMaskRow level) =
      -(secret 0 * (message * gadget level)) := by
  simpa [rankOneMaskRow] using
    (TGSW.gadgetPhase_castSucc secret gadget message (0 : Fin 1) level)

@[simp]
theorem rankOne_gadgetPhase_bodyRow
    {R : Type} [Ring R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (message : R)
    (level : Fin levels) :
    TGSW.gadgetPhase secret gadget message (rankOneBodyRow level) =
      message * gadget level := by
  simpa [rankOneBodyRow] using
    (TGSW.gadgetPhase_last secret gadget message level)

/-- Error action forced by globally complementing a rank-one TGSW secret and message.  For each
level it maps `(e_mask, e_body)` to `(e_mask + d * e_body, -e_body)`. -/
def rankOneComplementErrorShear {R : Type} [Ring R] {levels : ℕ}
    (offset : R) (error : Fin (TGSW.rowCount 1 levels) → R) :
    Fin (TGSW.rowCount 1 levels) → R :=
  fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      error (rankOneMaskRow indexed.2) + offset * error (rankOneBodyRow indexed.2)
    else
      -error (rankOneBodyRow indexed.2)

@[simp]
theorem rankOneComplementErrorShear_maskRow
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) (level : Fin levels) :
    rankOneComplementErrorShear offset error (rankOneMaskRow level) =
      error (rankOneMaskRow level) + offset * error (rankOneBodyRow level) := by
  simp [rankOneComplementErrorShear, rankOneMaskRow, TGSW.rowIndex]

@[simp]
theorem rankOneComplementErrorShear_bodyRow
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) (level : Fin levels) :
    rankOneComplementErrorShear offset error (rankOneBodyRow level) =
      -error (rankOneBodyRow level) := by
  simp [rankOneComplementErrorShear, rankOneBodyRow, TGSW.rowIndex]

/-- The rank-one error shear is an involution. -/
@[simp]
theorem rankOneComplementErrorShear_involutive
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    rankOneComplementErrorShear offset
        (rankOneComplementErrorShear offset error) = error := by
  classical
  funext row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  fin_cases block
  · simp [rankOneComplementErrorShear, rankOneMaskRow, rankOneBodyRow,
      TGSW.rowIndex]
  · simp [rankOneComplementErrorShear, rankOneBodyRow,
      TGSW.rowIndex]

/-- Hence the error shear is a permutation of the complete rank-one TGSW error vector. -/
theorem rankOneComplementErrorShear_bijective
    {R : Type} [Ring R] {levels : ℕ} (offset : R) :
    Function.Bijective
      (rankOneComplementErrorShear offset :
        (Fin (TGSW.rowCount 1 levels) → R) →
          Fin (TGSW.rowCount 1 levels) → R) :=
  Function.Involutive.bijective (rankOneComplementErrorShear_involutive offset)

/-- The combined challenge action arising from affine key transport followed by TGSW
conjugation.  At each level it sends `(a_mask, a_body)` to
`(-a_mask - d*a_body + g, a_body)`. -/
def rankOneGlobalComplementChallenge {R : Type} [Ring R] {levels : ℕ}
    (offset : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  fun coordinate row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      -challenge coordinate (rankOneMaskRow indexed.2) -
          offset * challenge coordinate (rankOneBodyRow indexed.2) + gadget indexed.2
    else
      challenge coordinate (rankOneBodyRow indexed.2)

/-- The public challenge action is also an involution. -/
@[simp]
theorem rankOneGlobalComplementChallenge_involutive
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    rankOneGlobalComplementChallenge offset gadget
        (rankOneGlobalComplementChallenge offset gadget challenge) = challenge := by
  classical
  funext coordinate row
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  fin_cases block
  · simp [rankOneGlobalComplementChallenge, rankOneMaskRow, rankOneBodyRow,
      TGSW.rowIndex]
    abel
  · simp [rankOneGlobalComplementChallenge, rankOneBodyRow,
      TGSW.rowIndex]

theorem rankOneGlobalComplementChallenge_bijective
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (gadget : Fin levels → R) :
    Function.Bijective
      (rankOneGlobalComplementChallenge offset gadget :
        Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R →
          Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
  Function.Involutive.bijective
    (rankOneGlobalComplementChallenge_involutive offset gadget)

/-- Therefore the combined public challenge action preserves the exact uniform challenge law. -/
theorem rankOneGlobalComplementChallenge_uniform_evalDist
    {R : Type} [Ring R] [Fintype R] [SampleableType R]
    {levels : ℕ} (offset : R) (gadget : Fin levels → R) :
    evalDist (rankOneGlobalComplementChallenge offset gadget <$>
        ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)) =
      evalDist ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (β := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (rankOneGlobalComplementChallenge offset gadget)
    (rankOneGlobalComplementChallenge_bijective offset gadget)

/-- Exact noise condition needed by native narrow-noise BRK complementation.  Ordinary
negation symmetry controls the body row but does not by itself control the mask-row shear
`e_mask + d*e_body`. -/
def RankOneComplementNoiseInvariant {R : Type} [Ring R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) : Prop :=
  evalDist (rankOneComplementErrorShear offset <$>
      ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler) =
    evalDist (ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler)

/-- Uniform row errors satisfy the shear condition because the shear is a permutation. -/
theorem rankOneComplementNoiseInvariant_uniform
    {R : Type} [Ring R] [Fintype R] [SampleableType R]
    {levels : ℕ} (offset : R) :
    RankOneComplementNoiseInvariant (levels := levels) ($ᵗ R) offset := by
  unfold RankOneComplementNoiseInvariant
  calc
    evalDist (rankOneComplementErrorShear offset <$>
        ProbComp.sampleIID (TGSW.rowCount 1 levels) ($ᵗ R)) =
      evalDist (rankOneComplementErrorShear offset <$>
        ($ᵗ (Fin (TGSW.rowCount 1 levels) → R))) :=
      evalDist_map_eq_of_evalDist_eq
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
          (alpha := R) (TGSW.rowCount 1 levels))
        (rankOneComplementErrorShear offset)
    _ = evalDist ($ᵗ (Fin (TGSW.rowCount 1 levels) → R)) :=
      evalDist_map_bijective_uniform_cross
        (α := Fin (TGSW.rowCount 1 levels) → R)
        (β := Fin (TGSW.rowCount 1 levels) → R)
        (rankOneComplementErrorShear offset)
        (rankOneComplementErrorShear_bijective offset)
    _ = evalDist (ProbComp.sampleIID (TGSW.rowCount 1 levels) ($ᵗ R)) :=
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := R) (TGSW.rowCount 1 levels)).symm

/-! ## Quantitative comparison of a narrow error law with its shear -/

/-- Exact statistical defect of the rank-one mask/body error shear.  Unlike
`RankOneComplementNoiseInvariant`, this quantity remains useful when the two distributions are
only close rather than equal. -/
noncomputable def rankOneComplementNoiseDistance {R : Type} [Ring R]
    {levels : ℕ} (errorSampler : ProbComp R) (offset : R) : ℝ :=
  tvDist
    (rankOneComplementErrorShear offset <$>
      ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler)
    (ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler)

/-- The rank-one shear written on the mask/body split of its error rows. -/
def rankOneComplementErrorPair {R : Type} [Ring R] {levels : ℕ}
    (offset : R)
    (errors : FormalProof4FHE.SharedRandomness.Output R levels) :
    FormalProof4FHE.SharedRandomness.Output R levels :=
  (fun level ↦ errors.1 level + offset * errors.2 level, -errors.2)

/-- Reindex the flattened rank-one rows as their mask/body pair. -/
def rankOneErrorPairEquiv (R : Type) (levels : ℕ) :
    (Fin (TGSW.rowCount 1 levels) → R) ≃
      FormalProof4FHE.SharedRandomness.Output R levels :=
  (FormalProof4FHE.LWE.ParallelBatch.outputEquiv R 2 levels).trans
    (finTwoArrowEquiv (Fin levels → R))

@[simp]
theorem rankOneErrorPairEquiv_fst
    {R : Type} {levels : ℕ} (errors : Fin (TGSW.rowCount 1 levels) → R)
    (level : Fin levels) :
    (rankOneErrorPairEquiv R levels errors).1 level =
      errors (rankOneMaskRow level) := by
  rfl

@[simp]
theorem rankOneErrorPairEquiv_snd
    {R : Type} {levels : ℕ} (errors : Fin (TGSW.rowCount 1 levels) → R)
    (level : Fin levels) :
    (rankOneErrorPairEquiv R levels errors).2 level =
      errors (rankOneBodyRow level) := by
  rfl

/-- Splitting the sheared row vector is exactly the explicit mask/body pair shear. -/
theorem rankOneErrorPairEquiv_shear
    {R : Type} [Ring R] {levels : ℕ} (offset : R)
    (errors : Fin (TGSW.rowCount 1 levels) → R) :
    rankOneErrorPairEquiv R levels
        (rankOneComplementErrorShear offset errors) =
      rankOneComplementErrorPair offset
        (rankOneErrorPairEquiv R levels errors) := by
  apply Prod.ext
  · funext level
    simp [rankOneComplementErrorPair]
  · funext level
    simp [rankOneComplementErrorPair]

/-- The row-pair reindexing sends one IID `2 * levels` vector to two independent IID
`levels`-vectors. -/
theorem rankOneErrorPairEquiv_sampleIID_evalDist
    {R : Type} [Finite R] (levels : ℕ) (errorSampler : ProbComp R) :
    evalDist (rankOneErrorPairEquiv R levels <$>
        ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler) =
      evalDist
        (FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler) := by
  have hblocks :=
    FormalProof4FHE.LWE.ParallelBatch.outputEquiv_sampleIID_evalDist
      2 levels errorSampler
  have hpairs := evalDist_map_eq_of_evalDist_eq hblocks
    (finTwoArrowEquiv (Fin levels → R))
  change evalDist ((fun errors ↦
      (finTwoArrowEquiv (Fin levels → R))
        (FormalProof4FHE.LWE.ParallelBatch.outputEquiv R 2 levels errors)) <$>
      ProbComp.sampleIID (2 * levels) errorSampler) = _
  have hpairs' :
      evalDist ((fun errors ↦
        (finTwoArrowEquiv (Fin levels → R))
          (FormalProof4FHE.LWE.ParallelBatch.outputEquiv R 2 levels errors)) <$>
        ProbComp.sampleIID (2 * levels) errorSampler) =
      evalDist ((finTwoArrowEquiv (Fin levels → R)) <$>
        Fin.mOfFn 2 (fun _ ↦ ProbComp.sampleIID levels errorSampler)) := by
    simpa only [Functor.map_map, Function.comp_apply] using hpairs
  rw [hpairs']
  simp [Fin.mOfFn,
    FormalProof4FHE.SharedRandomness.pairedErrorSampler, monad_norm]

/-- Total variation is preserved by a deterministic equivalence. -/
theorem tvDist_map_equiv_probComp {A B : Type} (equiv : A ≃ B)
    (left right : ProbComp A) :
    tvDist (equiv <$> left) (equiv <$> right) = tvDist left right := by
  apply le_antisymm
  · exact tvDist_map_le (m := ProbComp) equiv left right
  · have h := tvDist_map_le (m := ProbComp) equiv.symm
      (equiv <$> left) (equiv <$> right)
    simpa only [Functor.map_map, Equiv.symm_apply_apply, id_map'] using h

/-- The flattened-vector shear defect is exactly exposed by its mask/body-pair presentation. -/
theorem rankOneComplementNoiseDistance_le_pairDistance
    {R : Type} [Ring R] [Finite R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) :
    rankOneComplementNoiseDistance (levels := levels) errorSampler offset ≤
      tvDist
        (rankOneComplementErrorPair offset <$>
          FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler)
        (FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler) := by
  let errors := ProbComp.sampleIID (TGSW.rowCount 1 levels) errorSampler
  let paired := FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler
  let split := rankOneErrorPairEquiv R levels
  have horiginal : evalDist (split <$> errors) = evalDist paired :=
    rankOneErrorPairEquiv_sampleIID_evalDist levels errorSampler
  have hsheared :
      evalDist (split <$>
        (rankOneComplementErrorShear offset <$> errors)) =
        evalDist (rankOneComplementErrorPair offset <$> paired) := by
    calc
      _ = evalDist (rankOneComplementErrorPair offset <$>
          (split <$> errors)) := by
        apply congrArg evalDist
        simp only [Functor.map_map]
        congr 1
        funext errors
        exact rankOneErrorPairEquiv_shear offset errors
      _ = _ := evalDist_map_eq_of_evalDist_eq horiginal
        (rankOneComplementErrorPair offset)
  unfold rankOneComplementNoiseDistance
  have hdata := tvDist_map_equiv_probComp split
    (rankOneComplementErrorShear offset <$> errors) errors
  unfold tvDist at hdata ⊢
  rw [hsheared, horiginal] at hdata
  exact le_of_eq hdata.symm

/-- Translate the mask-error vector by the body-dependent rank-one shear residual. -/
def rankOneComplementMaskShift {R : Type} [Ring R] {levels : ℕ}
    (offset : R) (body mask : Fin levels → R) : Fin levels → R :=
  fun level ↦ offset * body level + mask level

/-- Uniform pointwise bound required to absorb the body-dependent mask translation. -/
def RankOneComplementConditionalShiftBound {R : Type} [Ring R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) (bound : ℝ) : Prop :=
  ∀ body : Fin levels → R,
    tvDist
        (rankOneComplementMaskShift offset body <$>
          ProbComp.sampleIID levels errorSampler)
        (ProbComp.sampleIID levels errorSampler) ≤ bound

/-- Negation symmetry removes the body-row sign change.  The remaining pair distance is bounded
by the worst conditional translation distance of the independent mask-error vector. -/
theorem rankOneComplementErrorPair_pairedErrorSampler_tvDist_le
    {R : Type} [CommRing R] [Finite R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) (bound : ℝ)
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (hshift : RankOneComplementConditionalShiftBound
      (levels := levels) errorSampler offset bound) :
    tvDist
        (rankOneComplementErrorPair offset <$>
          FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler)
        (FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler) ≤
      bound := by
  let errors := ProbComp.sampleIID levels errorSampler
  let transformed := errors >>= fun body ↦
    (fun mask ↦ (rankOneComplementMaskShift offset body mask, -body)) <$> errors
  let middle := errors >>= fun body ↦
    (fun mask ↦ (mask, -body)) <$> errors
  have htransformed :
      evalDist (rankOneComplementErrorPair offset <$>
          FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler) =
        evalDist transformed := by
    unfold FormalProof4FHE.SharedRandomness.pairedErrorSampler transformed
    simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    rw [evalDist_bind_bind_swap]
    apply evalDist_bind_congr'
    intro body
    apply evalDist_bind_congr'
    intro mask
    congr 2
    apply Prod.ext
    · funext level
      simp [rankOneComplementErrorPair, rankOneComplementMaskShift]
      ac_rfl
    · rfl
  have hmiddle :
      evalDist middle =
        evalDist
          (FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler) := by
    have hneg :=
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.negate_sampleIID_evalDist
        levels errorSampler hsymmetric
    calc
      evalDist middle = evalDist ((-·) <$> errors >>= fun body ↦
          (fun mask ↦ (mask, body)) <$> errors) := by
        unfold middle
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      _ = evalDist (errors >>= fun body ↦
          (fun mask ↦ (mask, body)) <$> errors) := by
        rw [evalDist_bind, hneg, ← evalDist_bind]
      _ = evalDist
          (FormalProof4FHE.SharedRandomness.pairedErrorSampler levels errorSampler) := by
        calc
          evalDist (errors >>= fun body ↦
              (fun mask ↦ (mask, body)) <$> errors) =
            evalDist (errors >>= fun body ↦
              errors >>= fun mask ↦ pure (mask, body)) := by
                refine evalDist_bind_congr' errors fun body ↦ ?_
                rw [map_eq_bind_pure_comp]
                apply congrArg evalDist
                apply bind_congr
                intro mask
                rfl
          _ = evalDist (errors >>= fun mask ↦
              errors >>= fun body ↦ pure (mask, body)) :=
            evalDist_bind_bind_swap errors errors
              (fun body mask ↦ (pure (mask, body) :
                ProbComp ((Fin levels → R) × (Fin levels → R))))
          _ = _ := by
            simp [errors,
              FormalProof4FHE.SharedRandomness.pairedErrorSampler]
  have hdistance : tvDist transformed middle ≤ bound := by
    unfold transformed middle
    refine tvDist_bind_left_le_const' errors _ _ bound ?_
    intro body
    have hdata := tvDist_map_le (m := ProbComp)
      (fun mask : Fin levels → R ↦ (mask, -body))
      (rankOneComplementMaskShift offset body <$> errors) errors
    simpa only [Functor.map_map, Function.comp_apply] using
      hdata.trans (hshift body)
  unfold tvDist at hdistance ⊢
  rw [htransformed, ← hmiddle]
  exact hdistance

/-- A pointwise conditional mask-shift bound controls the complete rank-one shear defect. -/
theorem rankOneComplementNoiseDistance_le_conditionalShiftBound
    {R : Type} [CommRing R] [Finite R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) (bound : ℝ)
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (hshift : RankOneComplementConditionalShiftBound
      (levels := levels) errorSampler offset bound) :
    rankOneComplementNoiseDistance (levels := levels) errorSampler offset ≤ bound :=
  (rankOneComplementNoiseDistance_le_pairDistance errorSampler offset).trans
    (rankOneComplementErrorPair_pairedErrorSampler_tvDist_le
      errorSampler offset bound hsymmetric hshift)

/-- A scalar translation envelope lifts through the independent mask rows with one hybrid per
gadget level. -/
theorem rankOneComplementConditionalShiftBound_of_addShiftDistance
    {R : Type} [CommRing R] [Finite R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) (perLevelBound : ℝ)
    (hshift : ∀ error : R,
      FormalProof4FHE.FiniteProduct.addShiftDistance
        errorSampler (offset * error) ≤ perLevelBound) :
    RankOneComplementConditionalShiftBound (levels := levels)
      errorSampler offset ((levels : ℝ) * perLevelBound) := by
  intro body
  calc
    tvDist
        (rankOneComplementMaskShift offset body <$>
          ProbComp.sampleIID levels errorSampler)
        (ProbComp.sampleIID levels errorSampler) ≤
      ∑ level, FormalProof4FHE.FiniteProduct.addShiftDistance
        errorSampler (offset * body level) := by
      change tvDist
          ((fun values level ↦ offset * body level + values level) <$>
            Fin.mOfFn levels (fun _ ↦ errorSampler))
          (Fin.mOfFn levels (fun _ ↦ errorSampler)) ≤ _
      exact FormalProof4FHE.FiniteProduct.tvDist_add_fin_mOfFn_le_sum
        levels errorSampler (fun level ↦ offset * body level)
    _ ≤ ∑ _level : Fin levels, perLevelBound := by
      apply Finset.sum_le_sum
      intro level _
      exact hshift (body level)
    _ = (levels : ℝ) * perLevelBound := by simp

/-- Fully scalar sufficient condition for bounding the rank-one shear defect. -/
theorem rankOneComplementNoiseDistance_le_mul_addShiftDistance
    {R : Type} [CommRing R] [Finite R] {levels : ℕ}
    (errorSampler : ProbComp R) (offset : R) (perLevelBound : ℝ)
    (hsymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        errorSampler)
    (hshift : ∀ error : R,
      FormalProof4FHE.FiniteProduct.addShiftDistance
        errorSampler (offset * error) ≤ perLevelBound) :
    rankOneComplementNoiseDistance (levels := levels) errorSampler offset ≤
      (levels : ℝ) * perLevelBound :=
  rankOneComplementNoiseDistance_le_conditionalShiftBound
    errorSampler offset ((levels : ℝ) * perLevelBound) hsymmetric
      (rankOneComplementConditionalShiftBound_of_addShiftDistance
        errorSampler offset perLevelBound hshift)

/-- Row challenge operation used after the ordinary affine key transport. -/
def rankOneConjugateChallenge {R : Type} [Ring R] {levels : ℕ}
    (offset : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  fun coordinate row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      challenge coordinate (rankOneMaskRow indexed.2) +
          offset * challenge coordinate (rankOneBodyRow indexed.2) + gadget indexed.2
    else
      -challenge coordinate (rankOneBodyRow indexed.2)

/-- Corresponding phase operation at the already-complemented encryption key. -/
def rankOneConjugateMessage {R : Type} [Ring R] {levels : ℕ}
    (secret : Fin 1 → R) (offset : R) (gadget : Fin levels → R)
    (message : Fin (TGSW.rowCount 1 levels) → R) :
    Fin (TGSW.rowCount 1 levels) → R :=
  fun row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      message (rankOneMaskRow indexed.2) +
          offset * message (rankOneBodyRow indexed.2) - secret 0 * gadget indexed.2
    else
      gadget indexed.2 - message (rankOneBodyRow indexed.2)

/-- Public row conjugation.  A mask row receives `offset` times its matching body row and a
public gadget challenge; a body row is negated and receives a public gadget body. -/
def rankOneConjugateRows {R : Type} [Ring R] {levels : ℕ}
    (offset : R) (gadget : Fin levels → R)
    (ciphertext : TGSW.Ciphertext R 1 levels) : TGSW.Ciphertext R 1 levels :=
  (rankOneConjugateChallenge offset gadget ciphertext.1,
    fun row ↦
      let indexed := TGSW.rowIndex row
      if indexed.1 = 0 then
        ciphertext.2 (rankOneMaskRow indexed.2) +
          offset * ciphertext.2 (rankOneBodyRow indexed.2)
      else
        gadget indexed.2 - ciphertext.2 (rankOneBodyRow indexed.2))

/-- Exact deterministic row law.  Conjugation changes the phase as above and forces precisely
the rank-one error shear. -/
theorem rankOneConjugateRows_batchAssemble
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (offset : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (message error : Fin (TGSW.rowCount 1 levels) → R) :
    rankOneConjugateRows offset gadget
        (TLWE.batchAssemble secret challenge message error) =
      TLWE.batchAssemble secret
        (rankOneConjugateChallenge offset gadget challenge)
        (rankOneConjugateMessage secret offset gadget message)
        (rankOneComplementErrorShear offset error) := by
  classical
  apply Prod.ext
  · rfl
  · funext row
    by_cases hmask : (TGSW.rowIndex row).1 = 0
    · rw [rankOne_row_eq_maskRow_of_index_eq_zero row hmask]
      simp [rankOneConjugateRows, rankOneConjugateChallenge,
        rankOneConjugateMessage,
        TLWE.batchAssemble, Matrix.vecMul, dotProduct]
      ring
    · rw [rankOne_row_eq_bodyRow_of_index_ne_zero row hmask]
      simp [rankOneConjugateRows, rankOneConjugateChallenge,
        rankOneConjugateMessage, TLWE.batchAssemble,
        Matrix.vecMul, dotProduct]
      ring

/-- Conjugating the old rank-one gadget phase after changing `s` to `d-s` gives exactly the
gadget phase for complemented message `1-m`. -/
theorem rankOneConjugateMessage_gadgetPhase
    {R : Type} [CommRing R] {levels : ℕ}
    (secretValue offset message : R) (gadget : Fin levels → R) :
    rankOneConjugateMessage (fun _ ↦ offset - secretValue) offset gadget
        (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) =
      TGSW.gadgetPhase (fun _ ↦ offset - secretValue) gadget (1 - message) := by
  classical
  funext row
  by_cases hmask : (TGSW.rowIndex row).1 = 0
  · rw [rankOne_row_eq_maskRow_of_index_eq_zero row hmask]
    simp [rankOneConjugateMessage]
    ring
  · rw [rankOne_row_eq_bodyRow_of_index_ne_zero row hmask]
    simp [rankOneConjugateMessage]
    ring

/-- Combining inverse `-1` challenge scaling with row conjugation is the involutive global
challenge action defined above. -/
theorem rankOneConjugateChallenge_scale_negOne
    {R : Type} [CommRing R] {levels : ℕ}
    (offset : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    rankOneConjugateChallenge offset gadget
        (scaleChallenge (-1 : Rˣ)⁻¹ challenge) =
      rankOneGlobalComplementChallenge offset gadget challenge := by
  classical
  funext coordinate row
  by_cases hmask : (TGSW.rowIndex row).1 = 0
  · rw [rankOne_row_eq_maskRow_of_index_eq_zero row hmask]
    simp [rankOneConjugateChallenge, rankOneGlobalComplementChallenge,
      scaleChallenge, sub_eq_add_neg]
  · rw [rankOne_row_eq_bodyRow_of_index_ne_zero row hmask]
    simp [rankOneConjugateChallenge, rankOneGlobalComplementChallenge,
      scaleChallenge]

@[simp]
theorem scalarAffineSecret_negOne_constant
    {R : Type} [CommRing R] (offset secretValue : R) :
    scalarAffineSecret (-1 : Rˣ) (fun _ : Fin 1 ↦ offset)
        (fun _ : Fin 1 ↦ secretValue) =
      fun _ ↦ offset - secretValue := by
  funext coordinate
  simp [scalarAffineSecret]
  abel

/-- Complete public rank-one TGSW action: first transport the encryption key by
`s ↦ -s+d`, then conjugate the extended gadget rows and complement the plaintext. -/
def globalComplementTGSW {R : Type} [CommRing R] {levels : ℕ}
    (offset : R) (gadget : Fin levels → R)
    (ciphertext : TGSW.Ciphertext R 1 levels) : TGSW.Ciphertext R 1 levels :=
  rankOneConjugateRows offset gadget
    (scalarAffineTranslateBatch (-1 : Rˣ) (fun _ ↦ offset) ciphertext)

/-- Deterministic normal form of the complete public action.  It maps a direct TGSW transcript
under `(s,m)` to a direct transcript under `(d-s,1-m)`, with permuted challenge and sheared
error vector. -/
theorem globalComplementTGSW_batchAssemble
    {R : Type} [CommRing R] {levels : ℕ}
    (secretValue offset message : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    globalComplementTGSW offset gadget
        (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
          (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error) =
      TLWE.batchAssemble (fun _ ↦ offset - secretValue)
        (rankOneGlobalComplementChallenge offset gadget challenge)
        (TGSW.gadgetPhase (fun _ ↦ offset - secretValue) gadget (1 - message))
        (rankOneComplementErrorShear offset error) := by
  unfold globalComplementTGSW
  rw [scalarAffineTranslateBatch_batchAssemble]
  rw [rankOneConjugateRows_batchAssemble]
  rw [scalarAffineSecret_negOne_constant]
  rw [rankOneConjugateChallenge_scale_negOne]
  rw [rankOneConjugateMessage_gadgetPhase]

/-- Under exactly the shear-invariance condition identified above, the public global-complement
action transports the normalized direct TGSW distribution without loss. -/
theorem globalComplementTGSW_directEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue offset message : R)
    (gadget : Fin levels → R)
    (hnoise : RankOneComplementNoiseInvariant
      (levels := levels) errorSampler offset) :
    evalDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) := by
  let samples := TGSW.rowCount 1 levels
  let errors := ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble (fun _ ↦ offset - secretValue) challenge
          (TGSW.gadgetPhase (fun _ ↦ offset - secretValue) gadget (1 - message))
          error) : ProbComp (TGSW.Ciphertext R 1 levels))
  rw [show TGSW.directEncrypt 1 levels errorSampler
      (fun _ ↦ secretValue) gadget message =
      (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
        errors >>= fun error =>
          pure (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
            (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error)) by
    simp [TGSW.directEncrypt, TLWE.batchEncrypt, samples, errors, monad_norm]]
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
      simp [TGSW.directEncrypt, TLWE.batchEncrypt, samples, errors, finish,
        monad_norm]

/-- The same exact law for the actual native structured TGSW sampler.  Native-to-direct
normalization and its inverse introduce no statistical error. -/
theorem globalComplementTGSW_encrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue offset message : R)
    (gadget : Fin levels → R)
    (hnoise : RankOneComplementNoiseInvariant
      (levels := levels) errorSampler offset) :
    evalDist (globalComplementTGSW offset gadget <$>
        TGSW.encrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) := by
  calc
    _ = evalDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message) :=
      evalDist_map_eq_of_evalDist_eq
        (TGSW.encrypt_evalDist_eq_directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
        (globalComplementTGSW offset gadget)
    _ = evalDist (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) :=
      globalComplementTGSW_directEncrypt_evalDist errorSampler secretValue
        offset message gadget hnoise
    _ = _ :=
      (TGSW.encrypt_evalDist_eq_directEncrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)).symm

/-- Quantitative direct-row complement law.  The public challenge conjugation is exact, so the
only statistical loss is the explicitly named error-shear distance. -/
theorem globalComplementTGSW_directEncrypt_tvDist_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue offset message : R)
    (gadget : Fin levels → R) :
    tvDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) ≤
      rankOneComplementNoiseDistance (levels := levels) errorSampler offset := by
  let samples := TGSW.rowCount 1 levels
  let errors := ProbComp.sampleIID samples errorSampler
  let shearedErrors :=
    rankOneComplementErrorShear (levels := levels) offset <$> errors
  let finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (error : Fin samples → R) =>
        (pure (TLWE.batchAssemble (fun _ ↦ offset - secretValue) challenge
          (TGSW.gadgetPhase (fun _ ↦ offset - secretValue) gadget (1 - message))
          error) : ProbComp (TGSW.Ciphertext R 1 levels))
  let shearedExperiment :=
    ($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
      shearedErrors >>= fun error => finish challenge error
  let targetExperiment :=
    ($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
      errors >>= fun error => finish challenge error
  have hsource :
      evalDist (globalComplementTGSW offset gadget <$>
          TGSW.directEncrypt 1 levels errorSampler
            (fun _ ↦ secretValue) gadget message) =
        evalDist shearedExperiment := by
    rw [show TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ secretValue) gadget message =
        (($ᵗ Matrix (Fin 1) (Fin samples) R) >>= fun challenge =>
          errors >>= fun error =>
            pure (TLWE.batchAssemble (fun _ ↦ secretValue) challenge
              (TGSW.gadgetPhase (fun _ ↦ secretValue) gadget message) error)) by
      simp [TGSW.directEncrypt, TLWE.batchEncrypt, samples, errors, monad_norm]]
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
          shearedErrors >>= fun error => finish challenge error) := by
        simp [shearedErrors, map_eq_bind_pure_comp, Function.comp_apply,
          bind_assoc]
        rfl
      _ = evalDist shearedExperiment := by
        unfold shearedExperiment
        rw [evalDist_bind,
          rankOneGlobalComplementChallenge_uniform_evalDist offset gadget,
          ← evalDist_bind]
  have htarget :
      evalDist (TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ offset - secretValue) gadget (1 - message)) =
        evalDist targetExperiment := by
    simp [TGSW.directEncrypt, TLWE.batchEncrypt, targetExperiment, finish,
      samples, errors, monad_norm]
  have hdistance : tvDist shearedExperiment targetExperiment ≤
      rankOneComplementNoiseDistance (levels := levels) errorSampler offset := by
    unfold shearedExperiment targetExperiment
    refine (tvDist_bind_left_le_const'
      ($ᵗ Matrix (Fin 1) (Fin samples) R)
      (fun challenge => shearedErrors >>= fun error => finish challenge error)
      (fun challenge => errors >>= fun error => finish challenge error)
      (rankOneComplementNoiseDistance (levels := levels) errorSampler offset) ?_)
    intro challenge
    exact (tvDist_bind_right_le (finish challenge) shearedErrors errors).trans_eq
      (by rfl)
  rw [show tvDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) =
      tvDist shearedExperiment targetExperiment by
        unfold tvDist
        rw [hsource, htarget]]
  exact hdistance

/-- Quantitative law for the actual structured native TGSW sampler. -/
theorem globalComplementTGSW_encrypt_tvDist_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secretValue offset message : R)
    (gadget : Fin levels → R) :
    tvDist (globalComplementTGSW offset gadget <$>
        TGSW.encrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) ≤
      rankOneComplementNoiseDistance (levels := levels) errorSampler offset := by
  have hsource := evalDist_map_eq_of_evalDist_eq
    (TGSW.encrypt_evalDist_eq_directEncrypt 1 levels errorSampler
      (fun _ ↦ secretValue) gadget message)
    (globalComplementTGSW offset gadget)
  have htarget := TGSW.encrypt_evalDist_eq_directEncrypt
    1 levels errorSampler (fun _ ↦ offset - secretValue) gadget (1 - message)
  rw [show tvDist (globalComplementTGSW offset gadget <$>
        TGSW.encrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) =
      tvDist (globalComplementTGSW offset gadget <$>
        TGSW.directEncrypt 1 levels errorSampler
          (fun _ ↦ secretValue) gadget message)
      (TGSW.directEncrypt 1 levels errorSampler
        (fun _ ↦ offset - secretValue) gadget (1 - message)) by
        unfold tvDist
        rw [hsource, htarget]]
  exact globalComplementTGSW_directEncrypt_tvDist_le
    errorSampler secretValue offset message gadget

/-- In particular, the wide uniform-error endpoint admits unconditional exact global
complementation. -/
theorem globalComplementTGSW_uniformError_encrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (secretValue offset message : R) (gadget : Fin levels → R) :
    evalDist (globalComplementTGSW offset gadget <$>
        TGSW.encrypt 1 levels ($ᵗ R) (fun _ ↦ secretValue) gadget message) =
      evalDist (TGSW.encrypt 1 levels ($ᵗ R)
        (fun _ ↦ offset - secretValue) gadget (1 - message)) :=
  globalComplementTGSW_encrypt_evalDist ($ᵗ R) secretValue offset message gadget
    (rankOneComplementNoiseInvariant_uniform offset)

/-- Apply the rank-one TGSW action independently to every BRK coordinate. -/
def globalComplementBootstrappingKey
    {q degree levels lweDimension : ℕ}
    (offset : RLWE.Rq q degree) (gadget : Fin levels → RLWE.Rq q degree)
    (bootstrappingKey : Native.BootstrappingKey q degree 1 levels lweDimension) :
    Native.BootstrappingKey q degree 1 levels lweDimension :=
  fun coordinate ↦ globalComplementTGSW offset gadget (bootstrappingKey coordinate)

/-- Conditional narrow-noise BRK theorem.  For a positive ring degree, the public action maps a
BRK under `(ringSecret,lweSecret)` to the BRK under their joint global complement.  The only
extra hypothesis is invariance of one IID TGSW error vector under the explicit shear above. -/
theorem globalComplementBootstrappingKey_generate_evalDist
    {q degree levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (hnoise : RankOneComplementNoiseInvariant (levels := levels) errorSampler
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))) :
    evalDist (globalComplementBootstrappingKey
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        gadget <$>
      Native.generateBootstrappingKey q (degree + 1) 1 levels lweDimension
        errorSampler gadget lweSecret ringSecret) =
      evalDist (Native.generateBootstrappingKey q (degree + 1) 1 levels lweDimension
        errorSampler gadget (globalComplementAction lweSecret true)
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
  simpa only [Native.generateBootstrappingKey, complementedRingSecret] using
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.mOfFn_map_evalDist_congr
      lweDimension
      (fun coordinate ↦
        TGSW.encrypt 1 levels errorSampler (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1) (lweSecret coordinate)))
      (fun coordinate ↦
        TGSW.encrypt 1 levels errorSampler
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
        exact globalComplementTGSW_encrypt_evalDist errorSampler secretValue
          offset (embedConstantBit q (degree + 1) (lweSecret coordinate))
          gadget hnoise)

/-- Quantitative narrow-noise BRK theorem.  Independent TGSW entries contribute one shear
distance per scalar-key coordinate. -/
theorem globalComplementBootstrappingKey_generate_tvDist_le
    {q degree levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1)) :
    tvDist (globalComplementBootstrappingKey
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        gadget <$>
      Native.generateBootstrappingKey q (degree + 1) 1 levels lweDimension
        errorSampler gadget lweSecret ringSecret)
      (Native.generateBootstrappingKey q (degree + 1) 1 levels lweDimension
        errorSampler gadget (globalComplementAction lweSecret true)
        (maskedRingSecret ringSecret
          (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))) ≤
      (lweDimension : ℝ) *
        rankOneComplementNoiseDistance (levels := levels) errorSampler
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) := by
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
  change tvDist
      ((fun values coordinate ↦ globalComplementTGSW offset gadget
          (values coordinate)) <$>
        Fin.mOfFn lweDimension (fun coordinate ↦
          TGSW.encrypt 1 levels errorSampler (embedRingSecret q ringSecret)
            gadget (embedConstantBit q (degree + 1) (lweSecret coordinate))))
      (Fin.mOfFn lweDimension (fun coordinate ↦
        TGSW.encrypt 1 levels errorSampler
          (embedRingSecret q complementedRingSecret) gadget
          (embedConstantBit q (degree + 1)
            (globalComplementAction lweSecret true coordinate)))) ≤ _
  rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn]
  calc
    _ ≤ ∑ coordinate,
        tvDist
          (globalComplementTGSW offset gadget <$>
            TGSW.encrypt 1 levels errorSampler (embedRingSecret q ringSecret)
              gadget (embedConstantBit q (degree + 1) (lweSecret coordinate)))
          (TGSW.encrypt 1 levels errorSampler
            (embedRingSecret q complementedRingSecret) gadget
            (embedConstantBit q (degree + 1)
              (globalComplementAction lweSecret true coordinate))) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
        lweDimension _ _
    _ ≤ ∑ _coordinate : Fin lweDimension,
        rankOneComplementNoiseDistance (levels := levels) errorSampler offset := by
      apply Finset.sum_le_sum
      intro coordinate _
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
      exact globalComplementTGSW_encrypt_tvDist_le
        errorSampler secretValue offset
          (embedConstantBit q (degree + 1) (lweSecret coordinate)) gadget
    _ = (lweDimension : ℝ) *
        rankOneComplementNoiseDistance (levels := levels) errorSampler offset := by
      simp

/-! ## Joint rank-one BRK plus suffix-style KSK transport -/

/-- Public global-complement action on a rank-one BRK paired with a KSK whose target key is the
BRK plaintext key. -/
def globalComplementEvaluationKeyPair
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    (offset : RLWE.Rq q degree)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (view : Native.BootstrappingKey q degree 1 tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension sourceDimension keySwitchLevels) :
    Native.BootstrappingKey q degree 1 tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension sourceDimension keySwitchLevels :=
  (globalComplementBootstrappingKey offset tgswGadget view.1,
    globalComplementKeySwitchKey keySwitchGadget view.2)

/-- Complete fixed-secret evaluation-key law.  It simultaneously complements the BRK ring key,
the shared scalar target/plaintext key, and the KSK source key.  For narrow errors the BRK needs
the explicit shear law; the KSK needs only ordinary negation symmetry. -/
theorem globalComplementEvaluationKeyPair_generate_evalDist
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension)
    (hringNoise : RankOneComplementNoiseInvariant (levels := tgswLevels)
      ringErrorSampler
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))))
    (hkeySwitchNoise :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        keySwitchErrorSampler) :
    evalDist (globalComplementEvaluationKeyPair
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension ringErrorSampler tgswGadget lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget sourceSecret
              lweSecret
        return (bootstrappingKey, keySwitchKey))) =
      evalDist (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension ringErrorSampler tgswGadget
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
      (Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
        lweDimension ringErrorSampler tgswGadget lweSecret ringSecret)
      (Native.generateKeySwitchKey q lweDimension sourceDimension keySwitchLevels
        keySwitchErrorSampler keySwitchGadget sourceSecret lweSecret)
      (Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
        lweDimension ringErrorSampler tgswGadget
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
      (globalComplementBootstrappingKey_generate_evalDist ringErrorSampler
        tgswGadget lweSecret ringSecret hringNoise)
      (globalComplementKeySwitchKey_generate_evalDist keySwitchErrorSampler
        hkeySwitchNoise keySwitchGadget sourceSecret lweSecret)

set_option maxHeartbeats 2000000 in
/-- Quantitative joint evaluation-key law.  Exact KSK symmetry contributes zero loss; all loss is
the BRK coordinate count times the rank-one shear distance. -/
theorem globalComplementEvaluationKeyPair_generate_tvDist_le
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension)
    (hkeySwitchNoise :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        keySwitchErrorSampler) :
    tvDist (globalComplementEvaluationKeyPair
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension ringErrorSampler tgswGadget lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget sourceSecret
              lweSecret
        return (bootstrappingKey, keySwitchKey)))
      (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension ringErrorSampler tgswGadget
              (globalComplementAction lweSecret true)
              (maskedRingSecret ringSecret
                (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget
              (globalComplementAction sourceSecret true)
              (globalComplementAction lweSecret true)
        return (bootstrappingKey, keySwitchKey)) ≤
      (lweDimension : ℝ) *
        rankOneComplementNoiseDistance (levels := tgswLevels) ringErrorSampler
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) := by
  let offset :=
    embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))
  let sourceBRK :=
    Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
      lweDimension ringErrorSampler tgswGadget lweSecret ringSecret
  let targetBRK :=
    Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
      lweDimension ringErrorSampler tgswGadget
        (globalComplementAction lweSecret true)
        (maskedRingSecret ringSecret
          (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
  let sourceKSK :=
    Native.generateKeySwitchKey q lweDimension sourceDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget sourceSecret lweSecret
  let targetKSK :=
    Native.generateKeySwitchKey q lweDimension sourceDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget
        (globalComplementAction sourceSecret true)
        (globalComplementAction lweSecret true)
  let transformedBRK :=
    globalComplementBootstrappingKey offset tgswGadget <$> sourceBRK
  let transformedKSK :=
    globalComplementKeySwitchKey keySwitchGadget <$> sourceKSK
  have hbrk : tvDist transformedBRK targetBRK ≤
      (lweDimension : ℝ) *
        rankOneComplementNoiseDistance (levels := tgswLevels)
          ringErrorSampler offset := by
    exact globalComplementBootstrappingKey_generate_tvDist_le
      ringErrorSampler tgswGadget lweSecret ringSecret
  have hkskDist : tvDist transformedKSK targetKSK = 0 := by
    unfold tvDist
    rw [show evalDist transformedKSK = evalDist targetKSK by
      exact globalComplementKeySwitchKey_generate_evalDist
        keySwitchErrorSampler hkeySwitchNoise keySwitchGadget sourceSecret lweSecret]
    exact SPMF.tvDist_self _
  have hpair := FormalProof4FHE.TFHE.SamplerReplacement.tvDist_independentPair_le
    transformedBRK targetBRK transformedKSK targetKSK Prod.mk
  have hbound :
      tvDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          transformedBRK transformedKSK Prod.mk)
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          targetBRK targetKSK Prod.mk) ≤
        (lweDimension : ℝ) *
          rankOneComplementNoiseDistance (levels := tgswLevels)
            ringErrorSampler offset := by
    exact hpair.trans (by rw [hkskDist, add_zero]; exact hbrk)
  rw [show globalComplementEvaluationKeyPair offset tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ← sourceBRK
        let keySwitchKey ← sourceKSK
        return (bootstrappingKey, keySwitchKey)) =
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair
        transformedBRK transformedKSK Prod.mk by
      simp only [globalComplementEvaluationKeyPair, transformedBRK, transformedKSK,
        FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
        map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]]
  rw [show (do
      let bootstrappingKey ← targetBRK
      let keySwitchKey ← targetKSK
      return (bootstrappingKey, keySwitchKey)) =
      FormalProof4FHE.TFHE.SamplerReplacement.independentPair
        targetBRK targetKSK Prod.mk by
      unfold FormalProof4FHE.TFHE.SamplerReplacement.independentPair
      apply bind_congr
      intro bootstrappingKey
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro keySwitchKey
      rfl]
  exact hbound

/-- At the wide uniform ring-error endpoint, the joint theorem needs no BRK noise assumption. -/
theorem globalComplementEvaluationKeyPair_uniformRingError_evalDist
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension)
    (hkeySwitchNoise :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        keySwitchErrorSampler) :
    evalDist (globalComplementEvaluationKeyPair
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension ($ᵗ (RLWE.Rq q (degree + 1))) tgswGadget
              lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget sourceSecret
              lweSecret
        return (bootstrappingKey, keySwitchKey))) =
      evalDist (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension ($ᵗ (RLWE.Rq q (degree + 1))) tgswGadget
              (globalComplementAction lweSecret true)
              (maskedRingSecret ringSecret
                (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget
              (globalComplementAction sourceSecret true)
              (globalComplementAction lweSecret true)
        return (bootstrappingKey, keySwitchKey)) :=
  globalComplementEvaluationKeyPair_generate_evalDist
    ($ᵗ (RLWE.Rq q (degree + 1))) keySwitchErrorSampler tgswGadget
    keySwitchGadget lweSecret ringSecret sourceSecret
    (rankOneComplementNoiseInvariant_uniform
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))))
    hkeySwitchNoise

/-! ## The surviving two-element action is not a fresh-key randomizer -/

/-- Random masks that are constant across coefficients can reach only a secret and its global
complement.  Once there are at least two coefficients, their image distribution cannot be the
uniform binary-secret law, independently of the randomness distribution. -/
theorem constantMask_randomization_evalDist_ne_uniform
    {Randomness : Type} {degree : ℕ}
    (randomness : ProbComp Randomness)
    (secret : BinarySecret (degree + 2))
    (mask : Randomness → BinarySecret (degree + 2))
    (hconstant : ∀ randomValue coordinate, mask randomValue coordinate = mask randomValue 0) :
    evalDist ((fun randomValue ↦
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret (mask randomValue)) <$> randomness) ≠
      evalDist ($ᵗ BinarySecret (degree + 2)) := by
  let target :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
      secret (basisPolynomial (0 : Fin (degree + 2)))
  have htarget : ∀ randomValue,
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret (mask randomValue) ≠ target := by
    intro randomValue heq
    have hmask : mask randomValue = basisPolynomial (0 : Fin (degree + 2)) :=
      (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecretEquiv
        secret).injective heq
    have hzero := congrFun hmask (0 : Fin (degree + 2))
    have hone := congrFun hmask (1 : Fin (degree + 2))
    have hmaskZero : mask randomValue (0 : Fin (degree + 2)) = true := by
      simpa [basisPolynomial] using hzero
    have hmaskOne : mask randomValue (1 : Fin (degree + 2)) = false := by
      simpa [basisPolynomial] using hone
    rw [hconstant randomValue 1, hmaskZero] at hmaskOne
    contradiction
  intro heval
  have hpoint := evalDist_ext_iff.mp heval target
  have himage :
      Pr[= target |
        (fun randomValue ↦
          FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            secret (mask randomValue)) <$> randomness] = 0 := by
    rw [probOutput_map]
    exact probEvent_eq_zero fun randomValue _ ↦ htarget randomValue
  have huniform : Pr[= target | $ᵗ BinarySecret (degree + 2)] ≠ 0 := by
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  exact huniform (hpoint.symm.trans himage)

/-- At every native modulus `q > 2`, no randomized family of the public scalar-affine RLWE
transports classified above can produce an exactly fresh binary key with two or more
coefficients. -/
theorem scalarAffineXorTransport_randomization_evalDist_ne_uniform
    {Randomness : Type} {q degree : ℕ} (hq : 2 < q)
    (randomness : ProbComp Randomness)
    (secret : BinarySecret (degree + 2))
    (mask : Randomness → BinarySecret (degree + 2))
    (htransport : ∀ randomValue,
      ScalarAffineXorTransport q (degree + 2) (mask randomValue)) :
    evalDist ((fun randomValue ↦
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret (mask randomValue)) <$> randomness) ≠
      evalDist ($ᵗ BinarySecret (degree + 2)) := by
  letI : NeZero q := ⟨by omega⟩
  apply constantMask_randomization_evalDist_ne_uniform randomness secret mask
  intro randomValue coordinate
  exact scalarAffineXorTransport_imp_constant hq (mask randomValue)
    (htransport randomValue) coordinate

/-- Consequently, the paper-aligned CircLWE view-randomization interface cannot obtain its
uniform fresh-secret law from any randomized family of scalar-affine native RLWE XOR transports
at `q > 2`.  A valid compiler must use a genuinely richer key action or evaluator. -/
theorem no_uniform_viewRandomization_of_scalarAffineXorTransport
    {Mask View : Type} {q degree : ℕ} (hq : 2 < q)
    (compiler : LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (BinarySecret (degree + 2)) Mask View)
    (mask : Mask → BinarySecret (degree + 2))
    (hact : ∀ secret randomMask,
      compiler.act secret randomMask =
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret (mask randomMask))
    (htransport : ∀ randomMask,
      ScalarAffineXorTransport q (degree + 2) (mask randomMask))
    (hfresh : evalDist compiler.sampleFreshSecret =
      evalDist ($ᵗ BinarySecret (degree + 2))) : False := by
  let secret := allFalsePolynomial (degree + 2)
  have haction :
      (fun randomMask ↦
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
          secret (mask randomMask)) = compiler.act secret := by
    funext randomMask
    exact (hact secret randomMask).symm
  apply
    scalarAffineXorTransport_randomization_evalDist_ne_uniform hq
      compiler.sampleMask secret mask htransport
  rw [haction, compiler.secretLaw secret, hfresh]

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
