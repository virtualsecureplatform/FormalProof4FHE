/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareSecretRandomization
import FormalProof4FHE.TFHE.RingSquareUnitMaskObstruction

/-!
# Unit-Difference Guess and Check for Rank-One Circular RLWE

Let `(a,b=a*S+e)` be a rank-one zero-message RLWE row, let `V` be a public candidate
for the ring secret, and sample a fresh uniform ring mask `u`.  The public transform

`(a,b) |-> (a+u, b+u*V)`

has phase `e + u*(V-S)` under the original secret.  Consequently:

* for the correct candidate `V=S`, it is another honest RLWE row with exactly the same
  narrow error;
* when `V-S` is a unit, the two-dimensional map from `(a,u)` to the transformed row is a
  bijection, so the transformed row is exactly uniform, independently of the error.

This is the exact ring analogue of the elementary candidate test used in field-LWE
search-to-decision reductions.  The final section records its sharp limitation for TFHE's
production power-of-two negacyclic ring: pairwise unit-separated candidates have distinct
binary residues, so there can be at most two of them.  Thus this direct test supports at most
a two-candidate secret family.  It does not recover even the parity of an arbitrary ring secret
without an additional quotient-compatible candidate action, and it cannot recover all binary
coefficients.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.UnitGuessCheck

open FormalProof4FHE.TFHE
open FormalProof4FHE.FiniteProduct

noncomputable section

/-- Rank-one public challenge matrices for a batch of RLWE rows. -/
abbrev Challenge (R : Type) (samples : ℕ) := Matrix (Fin 1) (Fin samples) R

/-- Embed one ring candidate as a rank-one secret vector. -/
def candidateVector {R : Type} (candidate : R) : Fin 1 → R :=
  fun _ ↦ candidate

/-- Public candidate test on a complete batch.  It adds the fresh mask to the public
challenge and adds its product with the candidate to the body. -/
def candidateTransform
    {R : Type} [CommRing R] {samples : ℕ}
    (candidate : R) (randomizer : Challenge R samples)
    (ciphertext : TLWE.BatchCiphertext R 1 samples) :
    TLWE.BatchCiphertext R 1 samples :=
  (ciphertext.1 + randomizer,
    ciphertext.2 + vecMul (candidateVector candidate) randomizer)

/-- The residual left by the candidate transform under the original secret. -/
def candidateResidual
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R)
    (randomizer : Challenge R samples) (error : Fin samples → R) :
    Fin samples → R :=
  fun row ↦ error row + (candidate - secret 0) * randomizer 0 row

/-- Exact deterministic phase identity for the candidate test. -/
theorem candidateTransform_batchAssemble
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R)
    (challenge randomizer : Challenge R samples)
    (error : Fin samples → R) :
    candidateTransform candidate randomizer
        (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble secret (challenge + randomizer) 0
        (candidateResidual secret candidate randomizer error) := by
  apply Prod.ext
  · rfl
  · funext row
    simp [candidateTransform, candidateResidual, TLWE.batchAssemble,
      candidateVector, Matrix.vecMul, dotProduct]
    ring

/-- With the correct candidate, the public transform preserves the error literally. -/
theorem candidateTransform_batchAssemble_correct
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R)
    (challenge randomizer : Challenge R samples)
    (error : Fin samples → R) :
    candidateTransform (secret 0) randomizer
        (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble secret (challenge + randomizer) 0 error := by
  rw [candidateTransform_batchAssemble]
  congr 1
  funext row
  simp [candidateResidual]

/-- Deterministic tape map at a fixed error vector. -/
def candidateTapeMap
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R) (error : Fin samples → R)
    (tape : Challenge R samples × Challenge R samples) :
    TLWE.BatchCiphertext R 1 samples :=
  candidateTransform candidate tape.2
    (TLWE.batchAssemble secret tape.1 0 error)

/-- Recover the fresh randomizer from a transformed row when the candidate difference is a
unit. -/
def recoverRandomizer
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R) (error : Fin samples → R)
    (hunit : IsUnit (candidate - secret 0))
    (ciphertext : TLWE.BatchCiphertext R 1 samples) : Challenge R samples :=
  fun _ row ↦
    (↑(hunit.unit⁻¹) : R) *
      (ciphertext.2 row - secret 0 * ciphertext.1 0 row - error row)

/-- Explicit inverse of `candidateTapeMap` for a unit candidate difference. -/
def candidateTapeInverse
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R) (error : Fin samples → R)
    (hunit : IsUnit (candidate - secret 0))
    (ciphertext : TLWE.BatchCiphertext R 1 samples) :
    Challenge R samples × Challenge R samples :=
  let randomizer := recoverRandomizer secret candidate error hunit ciphertext
  (ciphertext.1 - randomizer, randomizer)

@[simp]
theorem candidateTapeInverse_candidateTapeMap
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R) (error : Fin samples → R)
    (hunit : IsUnit (candidate - secret 0))
    (tape : Challenge R samples × Challenge R samples) :
    candidateTapeInverse secret candidate error hunit
        (candidateTapeMap secret candidate error tape) = tape := by
  rcases tape with ⟨challenge, randomizer⟩
  have hinv :
      (↑(hunit.unit⁻¹) : R) * (candidate - secret 0) = 1 := by
    calc
      (↑(hunit.unit⁻¹) : R) * (candidate - secret 0) =
          (↑(hunit.unit⁻¹) : R) * (↑hunit.unit : R) := by
        exact congrArg (fun value : R ↦ (↑(hunit.unit⁻¹) : R) * value)
          hunit.unit_spec.symm
      _ = 1 := Units.inv_mul hunit.unit
  have hrecover :
      recoverRandomizer secret candidate error hunit
          (candidateTapeMap secret candidate error (challenge, randomizer)) =
        randomizer := by
    funext coordinate row
    fin_cases coordinate
    simp only [recoverRandomizer, candidateTapeMap, candidateTransform,
      TLWE.batchAssemble, candidateVector, Pi.add_apply, Matrix.add_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_one, Pi.zero_apply]
    calc
      (↑(hunit.unit⁻¹) : R) *
          ((secret 0 * challenge 0 row + 0 + error row +
              candidate * randomizer 0 row) -
            secret 0 * (challenge 0 row + randomizer 0 row) - error row) =
          ((↑(hunit.unit⁻¹) : R) * (candidate - secret 0)) *
            randomizer 0 row := by ring
      _ = randomizer 0 row := by rw [hinv, one_mul]
  apply Prod.ext
  · change
      (challenge + randomizer) -
          recoverRandomizer secret candidate error hunit
            (candidateTapeMap secret candidate error (challenge, randomizer)) =
        challenge
    rw [hrecover]
    simp
  · exact hrecover

@[simp]
theorem candidateTapeMap_candidateTapeInverse
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R) (error : Fin samples → R)
    (hunit : IsUnit (candidate - secret 0))
    (ciphertext : TLWE.BatchCiphertext R 1 samples) :
    candidateTapeMap secret candidate error
        (candidateTapeInverse secret candidate error hunit ciphertext) = ciphertext := by
  have hinv :
      (candidate - secret 0) * (↑(hunit.unit⁻¹) : R) = 1 := by
    calc
      (candidate - secret 0) * (↑(hunit.unit⁻¹) : R) =
          (↑hunit.unit : R) * (↑(hunit.unit⁻¹) : R) := by
        exact congrArg (fun value : R ↦ value * (↑(hunit.unit⁻¹) : R))
          hunit.unit_spec.symm
      _ = 1 := Units.mul_inv hunit.unit
  let randomizer := recoverRandomizer secret candidate error hunit ciphertext
  have hresidual : ∀ row,
      (candidate - secret 0) * randomizer 0 row =
        ciphertext.2 row - secret 0 * ciphertext.1 0 row - error row := by
    intro row
    simp only [randomizer, recoverRandomizer]
    rw [← mul_assoc, hinv, one_mul]
  apply Prod.ext
  · funext coordinate row
    simp [candidateTapeInverse, candidateTapeMap,
      candidateTransform]
  · funext row
    simp only [candidateTapeInverse, candidateTapeMap,
      candidateTransform, TLWE.batchAssemble, candidateVector, Pi.add_apply,
      Matrix.sub_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_one,
      Pi.zero_apply]
    calc
      secret 0 * (ciphertext.1 0 row - randomizer 0 row) + 0 + error row +
          candidate * randomizer 0 row =
        secret 0 * ciphertext.1 0 row + error row +
          (candidate - secret 0) * randomizer 0 row := by ring
      _ = ciphertext.2 row := by rw [hresidual]; ring

/-- For a unit candidate difference, the fixed-error candidate tape is a permutation onto
the complete batch-ciphertext carrier. -/
theorem candidateTapeMap_bijective
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (candidate : R) (error : Fin samples → R)
    (hunit : IsUnit (candidate - secret 0)) :
    Function.Bijective (candidateTapeMap secret candidate error) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨candidateTapeInverse secret candidate error hunit,
    candidateTapeInverse_candidateTapeMap secret candidate error hunit,
    candidateTapeMap_candidateTapeInverse secret candidate error hunit⟩

/-! ## Exact fixed-error distribution laws -/

/-- Sample the ordinary RLWE mask and the fresh candidate-test mask independently, while
holding the error vector fixed. -/
def fixedErrorCandidateSampler
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {samples : ℕ} (secret : Fin 1 → R) (candidate : R)
    (error : Fin samples → R) : ProbComp (TLWE.BatchCiphertext R 1 samples) := do
  let challenge ← $ᵗ Challenge R samples
  let randomizer ← $ᵗ Challenge R samples
  return candidateTapeMap secret candidate error (challenge, randomizer)

/-- A fresh honest zero-message batch at one fixed error vector. -/
def fixedErrorRealSampler
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {samples : ℕ} (secret : Fin 1 → R) (error : Fin samples → R) :
    ProbComp (TLWE.BatchCiphertext R 1 samples) := do
  let challenge ← $ᵗ Challenge R samples
  return TLWE.batchAssemble secret challenge 0 error

/-- A unit candidate difference makes the fixed-error output exactly uniform.  The error can
be arbitrarily large or structured: it is absorbed by the bijection rather than widened. -/
theorem fixedErrorCandidateSampler_unit_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {samples : ℕ} (secret : Fin 1 → R) (candidate : R)
    (error : Fin samples → R) (hunit : IsUnit (candidate - secret 0)) :
    evalDist (fixedErrorCandidateSampler secret candidate error) =
      evalDist ($ᵗ TLWE.BatchCiphertext R 1 samples) := by
  let tapeSampler : ProbComp (Challenge R samples × Challenge R samples) := do
    let challenge ← $ᵗ Challenge R samples
    let randomizer ← $ᵗ Challenge R samples
    return (challenge, randomizer)
  have htape : evalDist tapeSampler =
      evalDist ($ᵗ (Challenge R samples × Challenge R samples)) := by
    simpa only [tapeSampler] using
      (evalDist_independent_uniform_product
        (first := Challenge R samples) (second := Challenge R samples))
  have hmapped :
      evalDist (candidateTapeMap secret candidate error <$> tapeSampler) =
        evalDist (candidateTapeMap secret candidate error <$>
          ($ᵗ (Challenge R samples × Challenge R samples))) := by
    rw [evalDist_map, evalDist_map, htape]
  calc
    evalDist (fixedErrorCandidateSampler secret candidate error) =
        evalDist (candidateTapeMap secret candidate error <$> tapeSampler) := by
      simp [fixedErrorCandidateSampler, tapeSampler, map_eq_bind_pure_comp,
        monad_norm]
    _ = evalDist (candidateTapeMap secret candidate error <$>
        ($ᵗ (Challenge R samples × Challenge R samples))) := hmapped
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := Challenge R samples × Challenge R samples)
      (β := TLWE.BatchCiphertext R 1 samples)
      (candidateTapeMap secret candidate error)
      (candidateTapeMap_bijective secret candidate error hunit)

/-- With the correct candidate, the fixed-error output is exactly a fresh honest RLWE batch
with the same error vector. -/
theorem fixedErrorCandidateSampler_correct_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {samples : ℕ} (secret : Fin 1 → R) (error : Fin samples → R) :
    evalDist (fixedErrorCandidateSampler secret (secret 0) error) =
      evalDist (fixedErrorRealSampler secret error) := by
  apply evalDist_ext
  intro output
  simp only [fixedErrorCandidateSampler, fixedErrorRealSampler,
    candidateTapeMap]
  calc
    Pr[= output |
        ($ᵗ Challenge R samples) >>= fun challenge ↦
          ($ᵗ Challenge R samples) >>= fun randomizer ↦
            pure (candidateTransform (secret 0) randomizer
              (TLWE.batchAssemble secret challenge 0 error))] =
      Pr[= output |
        ($ᵗ Challenge R samples) >>= fun challenge ↦
          ($ᵗ Challenge R samples) >>= fun freshChallenge ↦
            pure (TLWE.batchAssemble secret freshChallenge 0 error)] := by
        apply congrArg (fun value : ENNReal ↦ value)
        apply probOutput_bind_congr
        intro challenge _hchallenge
        rw [show (($ᵗ Challenge R samples) >>= fun randomizer ↦
              pure (candidateTransform (secret 0) randomizer
                (TLWE.batchAssemble secret challenge 0 error))) =
            (($ᵗ Challenge R samples) >>= fun randomizer ↦
              pure (TLWE.batchAssemble secret (challenge + randomizer) 0 error)) by
          apply bind_congr
          intro randomizer
          rw [candidateTransform_batchAssemble_correct]]
        exact probOutput_bind_add_left_uniform
          (Challenge R samples) challenge
          (fun freshChallenge ↦
            pure (TLWE.batchAssemble secret freshChallenge 0 error)) output
    _ = Pr[= output | fixedErrorRealSampler secret error] := by
      rw [probOutput_bind_const]
      simp [fixedErrorRealSampler]

/-! ## Executable fresh-RLWE candidate test -/

/-- Publicly test a candidate against a fresh ordinary rank-one RLWE batch.  The transform
uses only the candidate, the public ciphertext, and fresh uniform masks. -/
def candidateTestSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (candidate : R) : ProbComp (TLWE.BatchCiphertext R 1 samples) := do
  let ciphertext ← TLWE.batchEncrypt 1 samples errorSampler secret 0
  let randomizer ← $ᵗ Challenge R samples
  return candidateTransform candidate randomizer ciphertext

/-- Reorder the independent random tapes so that the error vector is sampled first. -/
theorem candidateTestSampler_evalDist_errorFirst
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (candidate : R) :
    evalDist (candidateTestSampler samples errorSampler secret candidate) =
      evalDist (ProbComp.sampleIID samples errorSampler >>= fun error ↦
        fixedErrorCandidateSampler secret candidate error) := by
  simpa [candidateTestSampler, TLWE.batchEncrypt, fixedErrorCandidateSampler,
    candidateTapeMap, monad_norm] using
    (evalDist_bind_bind_swap
      ($ᵗ Challenge R samples)
      (ProbComp.sampleIID samples errorSampler)
      (fun challenge error ↦
        ($ᵗ Challenge R samples) >>= fun randomizer ↦
          pure (candidateTransform candidate randomizer
            (TLWE.batchAssemble secret challenge 0 error))))

/-- The same error-first normal form for an honest fresh zero-message batch. -/
theorem batchEncrypt_zero_evalDist_errorFirst
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R) :
    evalDist (TLWE.batchEncrypt 1 samples errorSampler secret 0) =
      evalDist (ProbComp.sampleIID samples errorSampler >>= fun error ↦
        fixedErrorRealSampler secret error) := by
  simpa [TLWE.batchEncrypt, fixedErrorRealSampler, monad_norm] using
    (evalDist_bind_bind_swap
      ($ᵗ Challenge R samples)
      (ProbComp.sampleIID samples errorSampler)
      (fun challenge error ↦
        pure (TLWE.batchAssemble secret challenge 0 error)))

/-- **Correct-candidate law.** The candidate test with `V=S` is exactly a fresh real RLWE
batch at the original error law.  In particular, there is no correctness or noise penalty. -/
theorem candidateTestSampler_correct_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R) :
    evalDist (candidateTestSampler samples errorSampler secret (secret 0)) =
      evalDist (TLWE.batchEncrypt 1 samples errorSampler secret 0) := by
  calc
    evalDist (candidateTestSampler samples errorSampler secret (secret 0)) =
        evalDist (ProbComp.sampleIID samples errorSampler >>= fun error ↦
          fixedErrorCandidateSampler secret (secret 0) error) :=
      candidateTestSampler_evalDist_errorFirst samples errorSampler secret (secret 0)
    _ = evalDist (ProbComp.sampleIID samples errorSampler >>= fun error ↦
          fixedErrorRealSampler secret error) := by
      refine evalDist_bind_congr' (ProbComp.sampleIID samples errorSampler) fun error ↦ ?_
      exact fixedErrorCandidateSampler_correct_evalDist secret error
    _ = evalDist (TLWE.batchEncrypt 1 samples errorSampler secret 0) :=
      (batchEncrypt_zero_evalDist_errorFirst samples errorSampler secret).symm

/-- **Wrong unit-difference law.** If `V-S` is a unit, the candidate-test output is exactly
uniform.  The only sampler condition is totality; the error distribution itself is unchanged
and need not be wide. -/
theorem candidateTestSampler_unit_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (errorSampler : ProbComp R)
    (herror : Pr[⊥ | errorSampler] = 0)
    (secret : Fin 1 → R) (candidate : R)
    (hunit : IsUnit (candidate - secret 0)) :
    evalDist (candidateTestSampler samples errorSampler secret candidate) =
      evalDist ($ᵗ TLWE.BatchCiphertext R 1 samples) := by
  have herrors :
      Pr[⊥ | ProbComp.sampleIID samples errorSampler] = 0 := by
    simpa only [ProbComp.sampleIID] using
      (probFailure_fin_mOfFn_eq_zero samples (fun _ ↦ errorSampler)
        (fun _ ↦ herror))
  calc
    evalDist (candidateTestSampler samples errorSampler secret candidate) =
        evalDist (ProbComp.sampleIID samples errorSampler >>= fun error ↦
          fixedErrorCandidateSampler secret candidate error) :=
      candidateTestSampler_evalDist_errorFirst samples errorSampler secret candidate
    _ = evalDist (ProbComp.sampleIID samples errorSampler >>= fun _error ↦
          ($ᵗ TLWE.BatchCiphertext R 1 samples)) := by
      refine evalDist_bind_congr' (ProbComp.sampleIID samples errorSampler) fun error ↦ ?_
      exact fixedErrorCandidateSampler_unit_evalDist secret candidate error hunit
    _ = evalDist ($ᵗ TLWE.BatchCiphertext R 1 samples) := by
      apply evalDist_ext
      intro ciphertext
      rw [probOutput_bind_const, herrors]
      simp

/-! ## Candidate testing inside the complete circular view -/

open FormalProof4FHE.TFHE.TGSW.RingSquare.SecretRandomization

/-- Apply the public candidate test only to the ordinary RLWE component of the complete
`(RGSW_S(-S), RLWE_S(0))` view. -/
def candidateCircularViewTransform
    {R : Type} [CommRing R] {levels samples : ℕ}
    (candidate : R) (randomizer : Challenge R samples)
    (view : CircularView R levels samples) : CircularView R levels samples :=
  (view.1, candidateTransform candidate randomizer view.2)

/-- Operational fixed-secret candidate experiment: sample a complete real circular view and
then apply the public candidate transform with fresh uniform masks. -/
def fixedSecretCandidateCircularViewSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) (candidate : R) :
    ProbComp (CircularView R levels samples) := do
  let view ← fixedSecretRealCircularViewSampler levels samples
    auxiliaryErrorSampler testErrorSampler secret gadget
  let randomizer ← $ᵗ Challenge R samples
  return candidateCircularViewTransform candidate randomizer view

/-- Separate the independent RGSW auxiliary sampler from the executable candidate-test
sampler on the ordinary RLWE rows. -/
theorem fixedSecretCandidateCircularViewSampler_normalForm
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) (candidate : R) :
    evalDist (fixedSecretCandidateCircularViewSampler levels samples
      auxiliaryErrorSampler testErrorSampler secret gadget candidate) =
      evalDist (TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0) >>=
        fun auxiliary ↦
          candidateTestSampler samples testErrorSampler secret candidate >>=
            fun testRows ↦ pure (auxiliary, testRows)) := by
  simp [fixedSecretCandidateCircularViewSampler,
    fixedSecretRealCircularViewSampler, candidateCircularViewTransform,
    candidateTestSampler, TLWE.batchEncrypt, monad_norm]

/-- The correct candidate leaves the complete circular view exactly in its real branch. -/
theorem fixedSecretCandidateCircularViewSampler_correct_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) :
    evalDist (fixedSecretCandidateCircularViewSampler levels samples
      auxiliaryErrorSampler testErrorSampler secret gadget (secret 0)) =
      evalDist (fixedSecretRealCircularViewSampler levels samples
        auxiliaryErrorSampler testErrorSampler secret gadget) := by
  rw [fixedSecretCandidateCircularViewSampler_normalForm]
  unfold fixedSecretRealCircularViewSampler
  refine evalDist_bind_congr'
    (TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0))
    fun auxiliary ↦ ?_
  rw [evalDist_bind, candidateTestSampler_correct_evalDist samples testErrorSampler secret,
    ← evalDist_bind]

/-- A wrong candidate with unit difference changes only the test-row component to exact
uniform, while retaining the genuine `RGSW_S(-S)` auxiliary object. -/
theorem fixedSecretCandidateCircularViewSampler_unit_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (htestError : Pr[⊥ | testErrorSampler] = 0)
    (secret : Fin 1 → R) (gadget : Fin levels → R) (candidate : R)
    (hunit : IsUnit (candidate - secret 0)) :
    evalDist (fixedSecretCandidateCircularViewSampler levels samples
      auxiliaryErrorSampler testErrorSampler secret gadget candidate) =
      evalDist (fixedSecretUniformCircularViewSampler levels samples
        auxiliaryErrorSampler secret gadget) := by
  rw [fixedSecretCandidateCircularViewSampler_normalForm]
  unfold fixedSecretUniformCircularViewSampler
  refine evalDist_bind_congr'
    (TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0))
    fun auxiliary ↦ ?_
  rw [evalDist_bind,
    candidateTestSampler_unit_evalDist samples testErrorSampler htestError secret candidate hunit,
    ← evalDist_bind]

/-! ## Uniform-secret candidate branches -/

/-- Run the candidate test at a fixed source secret and then apply the exact additive secret
randomization to the complete circular view.  The returned secret is included only to state the
strong joint-distribution law; a public decision oracle receives the view component alone. -/
def randomizedCandidateCircularViewSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) (candidate : R) :
    ProbComp (R × CircularView R levels samples) := do
  let shift ← $ᵗ R
  let view ← fixedSecretCandidateCircularViewSampler levels samples
    auxiliaryErrorSampler testErrorSampler secret gadget candidate
  return (secret 0 + shift, circularViewKeyShift shift gadget view)

/-- Fresh uniform-secret real branch for the restricted CircRLWE problem. -/
def uniformSecretRealCircularViewSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (gadget : Fin levels → R) : ProbComp (R × CircularView R levels samples) := do
  let secret ← $ᵗ R
  let view ← fixedSecretRealCircularViewSampler levels samples
    auxiliaryErrorSampler testErrorSampler (fun _ ↦ secret) gadget
  return (secret, view)

/-- Fresh uniform-secret branch with a genuine circular auxiliary and uniform test rows. -/
def uniformSecretUniformCircularViewSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler : ProbComp R)
    (gadget : Fin levels → R) : ProbComp (R × CircularView R levels samples) := do
  let secret ← $ᵗ R
  let view ← fixedSecretUniformCircularViewSampler levels samples
    auxiliaryErrorSampler (fun _ ↦ secret) gadget
  return (secret, view)

/-- **Correct candidate after secret randomization.** Testing `V=S` and applying the public
RGSW key shift produces exactly the fresh uniform-secret real CircRLWE branch, jointly with the
new hidden secret and at the original narrow error laws. -/
theorem randomizedCandidateCircularViewSampler_correct_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) :
    evalDist (randomizedCandidateCircularViewSampler levels samples
      auxiliaryErrorSampler testErrorSampler secret gadget (secret 0)) =
      evalDist (uniformSecretRealCircularViewSampler levels samples
        auxiliaryErrorSampler testErrorSampler gadget) := by
  let shiftedFinish := fun shift : R ↦
    fixedSecretRealCircularViewSampler levels samples auxiliaryErrorSampler
        testErrorSampler (fun _ ↦ secret 0 + shift) gadget >>= fun view ↦
      pure (secret 0 + shift, view)
  calc
    evalDist (randomizedCandidateCircularViewSampler levels samples
        auxiliaryErrorSampler testErrorSampler secret gadget (secret 0)) =
      evalDist (($ᵗ R) >>= shiftedFinish) := by
        unfold randomizedCandidateCircularViewSampler
        refine evalDist_bind_congr' ($ᵗ R) fun shift ↦ ?_
        calc
          evalDist (fixedSecretCandidateCircularViewSampler levels samples
              auxiliaryErrorSampler testErrorSampler secret gadget (secret 0) >>=
            fun view ↦
              pure (secret 0 + shift, circularViewKeyShift shift gadget view)) =
            evalDist (fixedSecretRealCircularViewSampler levels samples
                auxiliaryErrorSampler testErrorSampler secret gadget >>=
              fun view ↦
                pure (secret 0 + shift, circularViewKeyShift shift gadget view)) := by
              rw [evalDist_bind,
                fixedSecretCandidateCircularViewSampler_correct_evalDist
                  levels samples auxiliaryErrorSampler testErrorSampler secret gadget,
                ← evalDist_bind]
          _ = evalDist (shiftedFinish shift) := by
              simp only [shiftedFinish]
              rw [show (fixedSecretRealCircularViewSampler levels samples
                    auxiliaryErrorSampler testErrorSampler secret gadget >>=
                  fun view ↦
                    pure (secret 0 + shift,
                      circularViewKeyShift shift gadget view)) =
                ((circularViewKeyShift shift gadget <$>
                    fixedSecretRealCircularViewSampler levels samples
                      auxiliaryErrorSampler testErrorSampler secret gadget) >>=
                  fun view ↦ pure (secret 0 + shift, view)) by
                    simp [map_eq_bind_pure_comp, bind_assoc, monad_norm]]
              rw [evalDist_bind,
                circularViewKeyShift_real_evalDist levels samples
                  auxiliaryErrorSampler testErrorSampler secret shift gadget,
                ← evalDist_bind]
    _ = evalDist (((fun shift ↦ secret 0 + shift) <$> ($ᵗ R)) >>=
        fun freshSecret ↦
          fixedSecretRealCircularViewSampler levels samples auxiliaryErrorSampler
              testErrorSampler (fun _ ↦ freshSecret) gadget >>= fun view ↦
            pure (freshSecret, view)) := by
      simp [shiftedFinish, map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (($ᵗ R) >>= fun freshSecret ↦
          fixedSecretRealCircularViewSampler levels samples auxiliaryErrorSampler
              testErrorSampler (fun _ ↦ freshSecret) gadget >>= fun view ↦
            pure (freshSecret, view)) := by
      rw [evalDist_bind, add_uniform_evalDist (secret 0), ← evalDist_bind]
    _ = evalDist (uniformSecretRealCircularViewSampler levels samples
        auxiliaryErrorSampler testErrorSampler gadget) := by
      rfl

/-- **Wrong unit-difference candidate after secret randomization.** The same public procedure
produces exactly the fresh uniform-secret uniform-test branch.  Hence a decision distinguisher
for the uniform-secret restricted CircRLWE problem is an exact tester on a unit-separated
candidate family. -/
theorem randomizedCandidateCircularViewSampler_unit_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (htestError : Pr[⊥ | testErrorSampler] = 0)
    (secret : Fin 1 → R) (gadget : Fin levels → R) (candidate : R)
    (hunit : IsUnit (candidate - secret 0)) :
    evalDist (randomizedCandidateCircularViewSampler levels samples
      auxiliaryErrorSampler testErrorSampler secret gadget candidate) =
      evalDist (uniformSecretUniformCircularViewSampler levels samples
        auxiliaryErrorSampler gadget) := by
  let shiftedFinish := fun shift : R ↦
    fixedSecretUniformCircularViewSampler levels samples auxiliaryErrorSampler
        (fun _ ↦ secret 0 + shift) gadget >>= fun view ↦
      pure (secret 0 + shift, view)
  calc
    evalDist (randomizedCandidateCircularViewSampler levels samples
        auxiliaryErrorSampler testErrorSampler secret gadget candidate) =
      evalDist (($ᵗ R) >>= shiftedFinish) := by
        unfold randomizedCandidateCircularViewSampler
        refine evalDist_bind_congr' ($ᵗ R) fun shift ↦ ?_
        calc
          evalDist (fixedSecretCandidateCircularViewSampler levels samples
              auxiliaryErrorSampler testErrorSampler secret gadget candidate >>=
            fun view ↦
              pure (secret 0 + shift, circularViewKeyShift shift gadget view)) =
            evalDist (fixedSecretUniformCircularViewSampler levels samples
                auxiliaryErrorSampler secret gadget >>= fun view ↦
              pure (secret 0 + shift, circularViewKeyShift shift gadget view)) := by
              rw [evalDist_bind,
                fixedSecretCandidateCircularViewSampler_unit_evalDist
                  levels samples auxiliaryErrorSampler testErrorSampler htestError
                  secret gadget candidate hunit,
                ← evalDist_bind]
          _ = evalDist (shiftedFinish shift) := by
              simp only [shiftedFinish]
              rw [show (fixedSecretUniformCircularViewSampler levels samples
                    auxiliaryErrorSampler secret gadget >>= fun view ↦
                  pure (secret 0 + shift,
                    circularViewKeyShift shift gadget view)) =
                ((circularViewKeyShift shift gadget <$>
                    fixedSecretUniformCircularViewSampler levels samples
                      auxiliaryErrorSampler secret gadget) >>= fun view ↦
                  pure (secret 0 + shift, view)) by
                    simp [map_eq_bind_pure_comp, bind_assoc, monad_norm]]
              rw [evalDist_bind,
                circularViewKeyShift_uniform_evalDist levels samples
                  auxiliaryErrorSampler secret shift gadget,
                ← evalDist_bind]
    _ = evalDist (((fun shift ↦ secret 0 + shift) <$> ($ᵗ R)) >>=
        fun freshSecret ↦
          fixedSecretUniformCircularViewSampler levels samples auxiliaryErrorSampler
              (fun _ ↦ freshSecret) gadget >>= fun view ↦
            pure (freshSecret, view)) := by
      simp [shiftedFinish, map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (($ᵗ R) >>= fun freshSecret ↦
          fixedSecretUniformCircularViewSampler levels samples auxiliaryErrorSampler
              (fun _ ↦ freshSecret) gadget >>= fun view ↦
            pure (freshSecret, view)) := by
      rw [evalDist_bind, add_uniform_evalDist (secret 0), ← evalDist_bind]
    _ = evalDist (uniformSecretUniformCircularViewSampler levels samples
        auxiliaryErrorSampler gadget) := by
      rfl

/-! ## The one-residue-bit boundary in the production ring -/

/-- A candidate family is unit separated when every two distinct candidates differ by a
unit.  Exactly such families can be distinguished pairwise by the direct unit-difference
candidate test above. -/
def UnitSeparated
    {Index R : Type} [Monoid R] [Sub R] (candidate : Index → R) : Prop :=
  ∀ left right : Index, left ≠ right →
    IsUnit (candidate left - candidate right)

namespace Production

open FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.SingleSourceInverse.PowerOfTwo

/-- In the production power-of-two negacyclic ring, unit-separated candidates have distinct
images in the binary residue field. -/
theorem parity_injective_of_unitSeparated
    {Index : Type} (modulusExponent degreeExponent : ℕ)
    (modulusExponent_positive : 0 < modulusExponent)
    (candidate : Index → Ring modulusExponent degreeExponent)
    (hseparated : UnitSeparated candidate) :
    Function.Injective (fun index ↦
      parityHom modulusExponent degreeExponent modulusExponent_positive
        (candidate index)) := by
  intro left right hparity
  by_contra hne
  have hunit : IsUnit (candidate left - candidate right) :=
    hseparated left right hne
  have hone :=
    (isUnit_iff_parityHom_eq_one modulusExponent degreeExponent
      modulusExponent_positive (candidate left - candidate right)).mp hunit
  have hzero :
      parityHom modulusExponent degreeExponent modulusExponent_positive
          (candidate left - candidate right) = 0 := by
    change
      parityHom modulusExponent degreeExponent modulusExponent_positive
          (candidate left) =
        parityHom modulusExponent degreeExponent modulusExponent_positive
          (candidate right) at hparity
    rw [← FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofSub_eq_sub]
    calc
      parityHom modulusExponent degreeExponent modulusExponent_positive
          (@Sub.sub (Ring modulusExponent degreeExponent)
            (LatticeCrypto.vectorNegacyclicRing_instCommRing
              (ZMod (2 ^ modulusExponent)) (2 ^ degreeExponent)).toSub
            (candidate left) (candidate right)) =
        parityHom modulusExponent degreeExponent modulusExponent_positive
            (candidate left) -
          parityHom modulusExponent degreeExponent modulusExponent_positive
            (candidate right) :=
        map_sub (parityHom modulusExponent degreeExponent
          modulusExponent_positive) (candidate left) (candidate right)
      _ = 0 := sub_eq_zero.mpr hparity
  rw [hzero] at hone
  exact zero_ne_one hone

/-- **Sharp cardinal obstruction for the direct guess test.** A pairwise unit-separated
candidate family in TFHE's production ring has at most two members.  The test can therefore
handle at most a one-bit-sized candidate universe; it cannot enumerate the `2^N`
binary-polynomial secrets by pairwise unit differences.  Distinct residues are necessary here,
not a proof that choosing residue representatives recovers the parity of an arbitrary secret. -/
theorem card_le_two_of_unitSeparated
    {Index : Type} [Fintype Index]
    (modulusExponent degreeExponent : ℕ)
    (modulusExponent_positive : 0 < modulusExponent)
    (candidate : Index → Ring modulusExponent degreeExponent)
    (hseparated : UnitSeparated candidate) :
    Fintype.card Index ≤ 2 := by
  calc
    Fintype.card Index ≤ Fintype.card (ZMod 2) :=
      Fintype.card_le_of_injective
        (fun index ↦
          parityHom modulusExponent degreeExponent modulusExponent_positive
            (candidate index))
        (parity_injective_of_unitSeparated modulusExponent degreeExponent
          modulusExponent_positive candidate hseparated)
    _ = 2 := ZMod.card 2

end Production

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.UnitGuessCheck
