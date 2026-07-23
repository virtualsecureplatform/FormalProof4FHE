/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.LWE.AuxiliaryInputSearchToDecision
import FormalProof4FHE.TFHE.RingSquareActualNormalForm

/-!
# Exact Additive Secret Randomization for `RGSW_S(-S)`

After the public linear block of a rank-one `RGSW_S(-S)` ciphertext is stripped, its upper
rows have phase `g * S^2 + e` and its lower rows have phase `e`.  This special message relation
admits an exact public additive key shift which is stronger than the generic TGSW key-shift
shear.

For an upper row `(a,b)` at gadget value `g` and a public shift `r`, set

* `a' = a - 2 * g * r`;
* `b' = b + a * r - g * r^2`.

For a lower zero row, keep `a' = a` and set `b' = b + a * r`.  If the old secret is `S`, then
the transformed rows are fresh square/zero rows under `S+r` with *exactly the same errors*.
Both the challenge map and the full ciphertext map are permutations, so uniform challenges
and uniform ciphertexts are preserved exactly.

Sampling `r` uniformly therefore turns the hidden secret into a uniform ring element without
changing the narrow error law.  The reduction direction matters: this maps a challenge under a
chosen source-secret law to the uniform-secret square law.  By itself it does not transform a
uniform-secret challenge into a binary-secret challenge and hence is not a proof of the desired
binary-secret circular security.  It is, however, an exact self-randomization boundary suitable
for a search-to-decision argument.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.SecretRandomization

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.TGSW.RingSquare
open FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler

noncomputable section

/-! ## Deterministic square-preserving key shift -/

/-- Translate the public masks of the upper square rows as required by `S ↦ S + shift`.
Lower zero-row masks are unchanged. -/
def squareKeyShiftChallenge {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R :=
  fun coordinate row ↦
    let indexed := TGSW.rowIndex row
    if indexed.1 = 0 then
      challenge coordinate row - 2 * gadget indexed.2 * shift
    else
      challenge coordinate row

/-- Publicly shift a complete stripped square/zero batch from key `S` to key `S + shift`.
The body correction uses only the old public mask, the gadget, and `shift`. -/
def squareKeyShift {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (ciphertext : PreimageCompiler.Full.TargetBatch R levels) :
    PreimageCompiler.Full.TargetBatch R levels :=
  (squareKeyShiftChallenge shift gadget ciphertext.1,
    fun row ↦
      let indexed := TGSW.rowIndex row
      if indexed.1 = 0 then
        ciphertext.2 row + ciphertext.1 0 row * shift -
          gadget indexed.2 * shift * shift
      else
        ciphertext.2 row + ciphertext.1 0 row * shift)

@[simp]
theorem squareKeyShiftChallenge_neg
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :
    squareKeyShiftChallenge (-shift) gadget
        (squareKeyShiftChallenge shift gadget challenge) = challenge := by
  funext coordinate row
  by_cases hUpper : (TGSW.rowIndex row).1 = 0
  · simp [squareKeyShiftChallenge, hUpper]
  · simp [squareKeyShiftChallenge, hUpper]

/-- For a fixed shift, the mask translation is a permutation of the complete challenge
matrix. -/
theorem squareKeyShiftChallenge_bijective
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R) :
    Function.Bijective (squareKeyShiftChallenge shift gadget) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨squareKeyShiftChallenge (-shift) gadget,
    squareKeyShiftChallenge_neg shift gadget,
    by
      intro challenge
      simpa only [neg_neg] using
        squareKeyShiftChallenge_neg (-shift) gadget challenge⟩

@[simp]
theorem squareKeyShift_neg
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (ciphertext : PreimageCompiler.Full.TargetBatch R levels) :
    squareKeyShift (-shift) gadget (squareKeyShift shift gadget ciphertext) =
      ciphertext := by
  apply Prod.ext
  · exact squareKeyShiftChallenge_neg shift gadget ciphertext.1
  · funext row
    by_cases hUpper : (TGSW.rowIndex row).1 = 0
    · simp [squareKeyShift, squareKeyShiftChallenge, hUpper]
      ring
    · simp [squareKeyShift, squareKeyShiftChallenge, hUpper]

/-- The complete public square-key shift is a permutation of the stripped ciphertext
carrier. -/
theorem squareKeyShift_bijective
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R) :
    Function.Bijective (squareKeyShift shift gadget) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨squareKeyShift (-shift) gadget,
    squareKeyShift_neg shift gadget,
    by
      intro ciphertext
      simpa only [neg_neg] using squareKeyShift_neg (-shift) gadget ciphertext⟩

/-- Exact deterministic normal form: square/zero messages are transported from `S` to
`S + shift`, while every error coordinate is retained literally. -/
theorem squareKeyShift_batchAssemble
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (shift : R) (gadget : Fin levels → R)
    (challenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (error : Fin (TGSW.rowCount 1 levels) → R) :
    squareKeyShift shift gadget
        (TLWE.batchAssemble secret challenge
          (PreimageCompiler.Full.squareMessages secret gadget) error) =
      TLWE.batchAssemble (fun _ ↦ secret 0 + shift)
        (squareKeyShiftChallenge shift gadget challenge)
        (PreimageCompiler.Full.squareMessages (fun _ ↦ secret 0 + shift) gadget)
        error := by
  apply Prod.ext
  · rfl
  · funext row
    by_cases hUpper : (TGSW.rowIndex row).1 = 0
    · simp only [squareKeyShift, hUpper, if_pos, TLWE.batchAssemble,
        Pi.add_apply]
      simp [Matrix.vecMul, dotProduct, squareKeyShiftChallenge,
        PreimageCompiler.Full.squareMessages, hUpper]
      ring
    · simp only [squareKeyShift, hUpper, TLWE.batchAssemble,
        Pi.add_apply]
      simp [Matrix.vecMul, dotProduct, squareKeyShiftChallenge,
        PreimageCompiler.Full.squareMessages, hUpper]
      ring

/-! ## Exact distributional laws -/

/-- The upper-row mask translation preserves the uniform challenge law. -/
theorem squareKeyShiftChallenge_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {levels : ℕ} (shift : R) (gadget : Fin levels → R) :
    evalDist (squareKeyShiftChallenge shift gadget <$>
        ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)) =
      evalDist ($ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (β := Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
    (squareKeyShiftChallenge shift gadget)
    (squareKeyShiftChallenge_bijective shift gadget)

/-- The complete square-key shift also preserves a uniformly sampled stripped ciphertext. -/
theorem squareKeyShift_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {levels : ℕ} (shift : R) (gadget : Fin levels → R) :
    evalDist (squareKeyShift shift gadget <$>
        ($ᵗ PreimageCompiler.Full.TargetBatch R levels)) =
      evalDist ($ᵗ PreimageCompiler.Full.TargetBatch R levels) :=
  evalDist_map_bijective_uniform_cross
    (α := PreimageCompiler.Full.TargetBatch R levels)
    (β := PreimageCompiler.Full.TargetBatch R levels)
    (squareKeyShift shift gadget) (squareKeyShift_bijective shift gadget)

/-- For a fixed old secret and public shift, transforming fresh native square rows gives
exactly fresh native square rows under the shifted secret with the same error sampler. -/
theorem squareKeyShift_batchEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (shift : R) (gadget : Fin levels → R) :
    evalDist (squareKeyShift shift gadget <$>
        TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
          (PreimageCompiler.Full.squareMessages secret gadget)) =
      evalDist (TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
        (fun _ ↦ secret 0 + shift)
        (PreimageCompiler.Full.squareMessages (fun _ ↦ secret 0 + shift) gadget)) := by
  let samples := TGSW.rowCount 1 levels
  let challenges : ProbComp (Matrix (Fin 1) (Fin samples) R) :=
    $ᵗ Matrix (Fin 1) (Fin samples) R
  let errors : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let finish := fun (challenge : Matrix (Fin 1) (Fin samples) R)
      (error : Fin samples → R) ↦
    (pure (TLWE.batchAssemble (fun _ ↦ secret 0 + shift) challenge
      (PreimageCompiler.Full.squareMessages (fun _ ↦ secret 0 + shift) gadget)
      error) : ProbComp (PreimageCompiler.Full.TargetBatch R levels))
  rw [show TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
      (PreimageCompiler.Full.squareMessages secret gadget) =
      (challenges >>= fun challenge ↦
        errors >>= fun error ↦
          pure (TLWE.batchAssemble secret challenge
            (PreimageCompiler.Full.squareMessages secret gadget) error)) by
    simp [TLWE.batchEncrypt, challenges, errors, samples, monad_norm]]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (challenges >>= fun challenge ↦
        errors >>= fun error ↦
          finish (squareKeyShiftChallenge shift gadget challenge) error) := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' errors fun error ↦ ?_
      simpa only [samples, finish] using congrArg evalDist
        (congrArg pure
          (squareKeyShift_batchAssemble secret shift gadget challenge error))
    _ = evalDist ((squareKeyShiftChallenge shift gadget <$> challenges) >>=
        fun challenge ↦ errors >>= fun error ↦ finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
      rfl
    _ = evalDist (challenges >>= fun challenge ↦
        errors >>= fun error ↦ finish challenge error) := by
      rw [evalDist_bind,
        show evalDist (squareKeyShiftChallenge shift gadget <$> challenges) =
            evalDist challenges by
          exact squareKeyShiftChallenge_uniform_evalDist shift gadget,
        ← evalDist_bind]
    _ = _ := by
      simp [TLWE.batchEncrypt, challenges, errors, samples, finish, monad_norm]

/-! ## Uniformizing the hidden ring secret -/

/-- Add a uniformly sampled public ring shift to a fixed-secret native square challenge. -/
def randomizedFixedSecretSquareBatchSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) :
    ProbComp (PreimageCompiler.Full.TargetBatch R levels) := do
  let ciphertext ← TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
    (PreimageCompiler.Full.squareMessages secret gadget)
  let shift ← $ᵗ R
  return squareKeyShift shift gadget ciphertext

/-- Native stripped square rows under a uniformly sampled full-ring secret. -/
def uniformSecretSquareBatchSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    ProbComp (PreimageCompiler.Full.TargetBatch R levels) :=
  PreimageCompiler.Full.nativeSquareBatchSampler levels ($ᵗ R)
    (fun secret _ ↦ secret) errorSampler gadget

/-- Addition of a fixed ring element permutes the complete finite ring. -/
def addShiftEquiv {R : Type} [AddGroup R] (secret : R) : R ≃ R where
  toFun shift := secret + shift
  invFun output := -secret + output
  left_inv shift := by simp
  right_inv output := by simp

/-- A uniform additive shift makes any fixed hidden ring element exactly uniform. -/
theorem add_uniform_evalDist
    {R : Type} [AddGroup R] [Fintype R] [SampleableType R] (secret : R) :
    evalDist ((fun shift ↦ secret + shift) <$> ($ᵗ R)) = evalDist ($ᵗ R) :=
  evalDist_map_bijective_uniform_cross (α := R) (β := R)
    (fun shift ↦ secret + shift)
    (addShiftEquiv secret).bijective

/-- The randomized fixed-secret square sampler is exactly the native square sampler with a
uniform full-ring secret.  In particular, the narrow error law is unchanged. -/
theorem randomizedFixedSecretSquareBatchSampler_evalDist_eq_uniformSecret
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) :
    evalDist (randomizedFixedSecretSquareBatchSampler
        levels errorSampler secret gadget) =
      evalDist (uniformSecretSquareBatchSampler levels errorSampler gadget) := by
  let fixedSampler := TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
    (PreimageCompiler.Full.squareMessages secret gadget)
  let shiftedSampler := fun shift : R ↦
    TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
      (fun _ ↦ secret 0 + shift)
      (PreimageCompiler.Full.squareMessages (fun _ ↦ secret 0 + shift) gadget)
  let freshSampler := fun freshSecret : R ↦
    TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
      (fun _ ↦ freshSecret)
      (PreimageCompiler.Full.squareMessages (fun _ ↦ freshSecret) gadget)
  calc
    evalDist (randomizedFixedSecretSquareBatchSampler
        levels errorSampler secret gadget) =
      evalDist (($ᵗ R) >>= fun shift ↦
        squareKeyShift shift gadget <$> fixedSampler) := by
      simpa only [randomizedFixedSecretSquareBatchSampler, fixedSampler,
        Functor.map, bind_pure_comp] using
        (evalDist_bind_bind_swap fixedSampler ($ᵗ R)
          (fun ciphertext shift ↦ pure (squareKeyShift shift gadget ciphertext)))
    _ = evalDist (($ᵗ R) >>= shiftedSampler) := by
      refine evalDist_bind_congr' ($ᵗ R) fun shift ↦ ?_
      exact squareKeyShift_batchEncrypt_evalDist errorSampler secret shift gadget
    _ = evalDist (((fun shift ↦ secret 0 + shift) <$> ($ᵗ R)) >>=
        freshSampler) := by
      simp only [shiftedSampler, freshSampler, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ R) >>= freshSampler) := by
      rw [evalDist_bind, add_uniform_evalDist (secret 0), ← evalDist_bind]
    _ = evalDist (uniformSecretSquareBatchSampler levels errorSampler gadget) := by
      simp [uniformSecretSquareBatchSampler,
        PreimageCompiler.Full.nativeSquareBatchSampler, freshSampler]

/-- Randomize the output of an arbitrary secret sampler by a fresh full-ring shift. -/
def randomizedSquareBatchSampler
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    ProbComp (PreimageCompiler.Full.TargetBatch R levels) := do
  let secretValue ← secretSampler
  randomizedFixedSecretSquareBatchSampler levels errorSampler
    (embed secretValue) gadget

/-- For every never-failing source-secret sampler, public randomization erases its secret law
exactly and leaves the uniform-secret square distribution. -/
theorem randomizedSquareBatchSampler_evalDist_eq_uniformSecret
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (secretSampler : ProbComp Secret) (embed : Secret → Fin 1 → R)
    (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (hsecret : Pr[⊥ | secretSampler] = 0) :
    evalDist (randomizedSquareBatchSampler levels secretSampler embed errorSampler gadget) =
      evalDist (uniformSecretSquareBatchSampler levels errorSampler gadget) := by
  unfold randomizedSquareBatchSampler
  calc
    evalDist (secretSampler >>= fun secretValue ↦
        randomizedFixedSecretSquareBatchSampler levels errorSampler
          (embed secretValue) gadget) =
      evalDist (secretSampler >>= fun _secretValue ↦
        uniformSecretSquareBatchSampler levels errorSampler gadget) := by
      exact evalDist_bind_congr' secretSampler fun secretValue ↦
        randomizedFixedSecretSquareBatchSampler_evalDist_eq_uniformSecret
          levels errorSampler (embed secretValue) gadget
    _ = evalDist (uniformSecretSquareBatchSampler levels errorSampler gadget) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        secretSampler hsecret _

/-! ## Lift back to the genuine `RGSW_S(-S)` layout -/

/-- Public additive key shift on a genuine rank-one `RGSW_S(-S)` ciphertext: strip the
linear block, apply the exact square-key shift, and restore the linear block for the new
`-(S+shift)` message. -/
def rgswMinusSecretKeyShift
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (ciphertext : TGSW.Ciphertext R 1 levels) : TGSW.Ciphertext R 1 levels :=
  restoreLinearBlock gadget
    (squareKeyShift shift gadget (stripLinearBlock gadget ciphertext))

@[simp]
theorem rgswMinusSecretKeyShift_neg
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (ciphertext : TGSW.Ciphertext R 1 levels) :
    rgswMinusSecretKeyShift (-shift) gadget
        (rgswMinusSecretKeyShift shift gadget ciphertext) = ciphertext := by
  simp [rgswMinusSecretKeyShift]

/-- The public key shift is a permutation of the complete genuine RGSW ciphertext carrier. -/
theorem rgswMinusSecretKeyShift_bijective
    {R : Type} [CommRing R] {levels : ℕ}
    (shift : R) (gadget : Fin levels → R) :
    Function.Bijective (rgswMinusSecretKeyShift shift gadget) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨rgswMinusSecretKeyShift (-shift) gadget,
    rgswMinusSecretKeyShift_neg shift gadget,
    by
      intro ciphertext
      simpa only [neg_neg] using
        rgswMinusSecretKeyShift_neg (-shift) gadget ciphertext⟩

/-- Consequently the genuine-layout key shift preserves a uniformly sampled ciphertext. -/
theorem rgswMinusSecretKeyShift_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {levels : ℕ} (shift : R) (gadget : Fin levels → R) :
    evalDist (rgswMinusSecretKeyShift shift gadget <$>
        ($ᵗ TGSW.Ciphertext R 1 levels)) =
      evalDist ($ᵗ TGSW.Ciphertext R 1 levels) :=
  evalDist_map_bijective_uniform_cross
    (α := TGSW.Ciphertext R 1 levels) (β := TGSW.Ciphertext R 1 levels)
    (rgswMinusSecretKeyShift shift gadget)
    (rgswMinusSecretKeyShift_bijective shift gadget)

set_option maxHeartbeats 1000000 in
/-- Exact native theorem in the original layout: an honest `RGSW_S(-S)` ciphertext is
transported to an honest `RGSW_(S+r)(-(S+r))` ciphertext with the same narrow error sampler. -/
theorem rgswMinusSecretKeyShift_encrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (shift : R) (gadget : Fin levels → R) :
    evalDist (rgswMinusSecretKeyShift shift gadget <$>
        TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)) =
      evalDist (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ secret 0 + shift) gadget (-(secret 0 + shift))) := by
  let oldSquare := TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler secret
    (PreimageCompiler.Full.squareMessages secret gadget)
  let newSecret : Fin 1 → R := fun _ ↦ secret 0 + shift
  let newSquare := TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler newSecret
    (PreimageCompiler.Full.squareMessages newSecret gadget)
  have hold :=
    PreimageCompiler.ActualNormalForm.encryptSquareView_evalDist_eq_nativeSquareBatch
      levels errorSampler secret gadget
  have hnew :=
    PreimageCompiler.ActualNormalForm.encryptSquareView_evalDist_eq_nativeSquareBatch
      levels errorSampler newSecret gadget
  calc
    evalDist (rgswMinusSecretKeyShift shift gadget <$>
        TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)) =
      evalDist (restoreLinearBlock gadget <$>
        (squareKeyShift shift gadget <$> encryptSquareView
          levels errorSampler secret gadget)) := by
        apply congrArg evalDist
        simp only [encryptSquareView, Functor.map_map]
        rfl
    _ = evalDist (restoreLinearBlock gadget <$>
        (squareKeyShift shift gadget <$> oldSquare)) := by
      exact evalDist_map_eq_of_evalDist_eq
        (evalDist_map_eq_of_evalDist_eq hold (squareKeyShift shift gadget))
        (restoreLinearBlock gadget)
    _ = evalDist (restoreLinearBlock gadget <$> newSquare) := by
      exact evalDist_map_eq_of_evalDist_eq
        (squareKeyShift_batchEncrypt_evalDist errorSampler secret shift gadget)
        (restoreLinearBlock gadget)
    _ = evalDist (restoreLinearBlock gadget <$>
        encryptSquareView levels errorSampler newSecret gadget) := by
      exact evalDist_map_eq_of_evalDist_eq hnew.symm (restoreLinearBlock gadget)
    _ = evalDist (TGSW.encrypt 1 levels errorSampler newSecret
        gadget (-newSecret 0)) := by
      simp [encryptSquareView, Functor.map_map]
    _ = evalDist (TGSW.encrypt 1 levels errorSampler
        (fun _ ↦ secret 0 + shift) gadget (-(secret 0 + shift))) := by
      rfl

/-- Add a uniform public ring shift directly to an honest fixed-secret
`RGSW_S(-S)` ciphertext. -/
def randomizedFixedSecretRGSWMinusSecretSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) : ProbComp (TGSW.Ciphertext R 1 levels) := do
  let ciphertext ← TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)
  let shift ← $ᵗ R
  return rgswMinusSecretKeyShift shift gadget ciphertext

/-- Honest genuine-layout `RGSW_S(-S)` under a uniformly sampled full-ring secret. -/
def uniformSecretRGSWMinusSecretSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    ProbComp (TGSW.Ciphertext R 1 levels) := do
  let secret ← $ᵗ R
  TGSW.encrypt 1 levels errorSampler (fun _ ↦ secret) gadget (-secret)

/-- Exact genuine-RGSW randomization law.  A uniform public additive shift erases any fixed
source secret while preserving the native `-S` message relation and every narrow row error. -/
theorem randomizedFixedSecretRGSWMinusSecretSampler_evalDist_eq_uniformSecret
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R) :
    evalDist (randomizedFixedSecretRGSWMinusSecretSampler
        levels errorSampler secret gadget) =
      evalDist (uniformSecretRGSWMinusSecretSampler levels errorSampler gadget) := by
  let fixedSampler :=
    TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0)
  let shiftedSampler := fun shift : R ↦
    TGSW.encrypt 1 levels errorSampler (fun _ ↦ secret 0 + shift)
      gadget (-(secret 0 + shift))
  let freshSampler := fun freshSecret : R ↦
    TGSW.encrypt 1 levels errorSampler (fun _ ↦ freshSecret)
      gadget (-freshSecret)
  calc
    evalDist (randomizedFixedSecretRGSWMinusSecretSampler
        levels errorSampler secret gadget) =
      evalDist (($ᵗ R) >>= fun shift ↦
        rgswMinusSecretKeyShift shift gadget <$> fixedSampler) := by
      simpa only [randomizedFixedSecretRGSWMinusSecretSampler, fixedSampler,
        Functor.map, bind_pure_comp] using
        (evalDist_bind_bind_swap fixedSampler ($ᵗ R)
          (fun ciphertext shift ↦
            pure (rgswMinusSecretKeyShift shift gadget ciphertext)))
    _ = evalDist (($ᵗ R) >>= shiftedSampler) := by
      refine evalDist_bind_congr' ($ᵗ R) fun shift ↦ ?_
      exact rgswMinusSecretKeyShift_encrypt_evalDist
        errorSampler secret shift gadget
    _ = evalDist (((fun shift ↦ secret 0 + shift) <$> ($ᵗ R)) >>=
        freshSampler) := by
      simp only [shiftedSampler, freshSampler, map_eq_bind_pure_comp,
        Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (($ᵗ R) >>= freshSampler) := by
      rw [evalDist_bind, add_uniform_evalDist (secret 0), ← evalDist_bind]
    _ = evalDist (uniformSecretRGSWMinusSecretSampler
        levels errorSampler gadget) := by
      rfl

/-! ## The exact reduction direction -/

/-- Pull a distinguisher back through a fresh public additive secret shift. -/
def randomizedRGSWMinusSecretDistinguisher
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {levels : ℕ} (gadget : Fin levels → R)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) :
    PreimageCompiler.Full.Distinguisher R levels :=
  fun ciphertext ↦ do
    let shift ← $ᵗ R
    distinguisher (rgswMinusSecretKeyShift shift gadget ciphertext)

/-- Running the pulled-back distinguisher on a fixed-secret genuine challenge is exactly
running the original distinguisher on the uniform-secret genuine challenge. -/
theorem fixedSecretGame_randomizedDistinguisher_evalDist_eq_uniformSecretGame
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) :
    evalDist
        (TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0) >>=
          randomizedRGSWMinusSecretDistinguisher gadget distinguisher) =
      evalDist
        (uniformSecretRGSWMinusSecretSampler levels errorSampler gadget >>=
          distinguisher) := by
  have hRandomized :=
    randomizedFixedSecretRGSWMinusSecretSampler_evalDist_eq_uniformSecret
      levels errorSampler secret gadget
  calc
    evalDist
        (TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0) >>=
          randomizedRGSWMinusSecretDistinguisher gadget distinguisher) =
      evalDist
        (randomizedFixedSecretRGSWMinusSecretSampler
          levels errorSampler secret gadget >>= distinguisher) := by
      simp [randomizedRGSWMinusSecretDistinguisher,
        randomizedFixedSecretRGSWMinusSecretSampler, bind_assoc]
    _ = evalDist
        (uniformSecretRGSWMinusSecretSampler levels errorSampler gadget >>=
          distinguisher) := by
      rw [evalDist_bind, hRandomized, ← evalDist_bind]

/-- Pulling a distinguisher back through the same random shift preserves the uniform
ciphertext game exactly. -/
theorem uniformGame_randomizedDistinguisher_evalDist_eq
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (gadget : Fin levels → R)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) :
    evalDist (PreimageCompiler.Full.uniformGame
        (randomizedRGSWMinusSecretDistinguisher gadget distinguisher)) =
      evalDist (PreimageCompiler.Full.uniformGame distinguisher) := by
  let uniformCiphertext : ProbComp (TGSW.Ciphertext R 1 levels) :=
    $ᵗ TGSW.Ciphertext R 1 levels
  let finish := fun ciphertext ↦ distinguisher ciphertext
  calc
    evalDist (PreimageCompiler.Full.uniformGame
        (randomizedRGSWMinusSecretDistinguisher gadget distinguisher)) =
      evalDist (($ᵗ R) >>= fun shift ↦
        uniformCiphertext >>= fun ciphertext ↦
          finish (rgswMinusSecretKeyShift shift gadget ciphertext)) := by
      simpa only [PreimageCompiler.Full.uniformGame,
        randomizedRGSWMinusSecretDistinguisher, uniformCiphertext, finish,
        bind_assoc] using
        (evalDist_bind_bind_swap uniformCiphertext ($ᵗ R)
          (fun ciphertext shift ↦
            distinguisher (rgswMinusSecretKeyShift shift gadget ciphertext)))
    _ = evalDist (($ᵗ R) >>= fun _shift ↦ uniformCiphertext >>= finish) := by
      refine evalDist_bind_congr' ($ᵗ R) fun shift ↦ ?_
      have hmap := rgswMinusSecretKeyShift_uniform_evalDist shift gadget
      have hbind :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          hmap finish
      simpa only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc,
        pure_bind] using hbind
    _ = evalDist (uniformCiphertext >>= finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ R) (by simp) _
    _ = evalDist (PreimageCompiler.Full.uniformGame distinguisher) := by
      rfl

/-- Real-versus-uniform advantage for a fixed genuine `RGSW_S(-S)` source secret. -/
noncomputable def fixedSecretRGSWMinusSecretAdvantage
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) : ℝ :=
  (TGSW.encrypt 1 levels errorSampler secret gadget (-secret 0) >>=
      distinguisher).boolDistAdvantage
    (PreimageCompiler.Full.uniformGame distinguisher)

/-- Real-versus-uniform advantage for the uniform-full-ring-secret genuine distribution. -/
noncomputable def uniformSecretRGSWMinusSecretAdvantage
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) : ℝ :=
  (uniformSecretRGSWMinusSecretSampler levels errorSampler gadget >>=
      distinguisher).boolDistAdvantage
    (PreimageCompiler.Full.uniformGame distinguisher)

/-- **Direction-sensitive self-reduction.** Every distinguisher for uniform-secret
`RGSW_S(-S)` induces, with exactly the same advantage, a randomized distinguisher for the
fixed-secret distribution.  The converse reduction is not asserted. -/
theorem fixedSecretAdvantage_randomizedDistinguisher_eq_uniformSecretAdvantage
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels : ℕ} (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (gadget : Fin levels → R)
    (distinguisher : PreimageCompiler.Full.Distinguisher R levels) :
    fixedSecretRGSWMinusSecretAdvantage errorSampler secret gadget
        (randomizedRGSWMinusSecretDistinguisher gadget distinguisher) =
      uniformSecretRGSWMinusSecretAdvantage errorSampler gadget distinguisher := by
  unfold fixedSecretRGSWMinusSecretAdvantage
    uniformSecretRGSWMinusSecretAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (fixedSecretGame_randomizedDistinguisher_evalDist_eq_uniformSecretGame
        errorSampler secret gadget distinguisher),
    probOutput_congr rfl
      (uniformGame_randomizedDistinguisher_evalDist_eq gadget distinguisher)]

/-! ## Zero-loss PKC-style view-randomization certificate -/

/-- The special `RGSW_S(-S)` relation supplies the secret-law and shifted-view fields of the
generic auxiliary-input search-to-decision interface with zero loss.  Unlike the generic
quadratic CircLWE construction, this compiler performs no homomorphic evaluation and no noise
flooding. -/
def exactRGSWMinusSecretViewRandomization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      R R (TGSW.Ciphertext R 1 levels) :=
  LWE.AuxiliaryInput.SearchToDecision.ViewRandomization.ofExact
    ($ᵗ R)
    (fun secret shift ↦ secret + shift)
    ($ᵗ R)
    (fun secret ↦
      TGSW.encrypt 1 levels errorSampler (fun _ ↦ secret) gadget (-secret))
    (fun shift ↦ pure ∘ rgswMinusSecretKeyShift shift gadget)
    (fun secret ↦ add_uniform_evalDist secret)
    (fun secret shift ↦ by
      simpa only [← map_eq_bind_pure_comp] using
        (rgswMinusSecretKeyShift_encrypt_evalDist
          errorSampler (fun _ : Fin 1 ↦ secret) shift gadget))

@[simp]
theorem exactRGSWMinusSecretViewRandomization_error
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (gadget : Fin levels → R) :
    (exactRGSWMinusSecretViewRandomization levels errorSampler gadget).error = 0 :=
  rfl

/-- Formal analogue of the secret-randomization part of PKC 2024, Lemma 3, specialized to
the native rank-one `RGSW_S(-S)` circular object: the randomized fixed-secret joint
`(newSecret, ciphertext)` law is exactly the fresh uniform-secret law at the original narrow
noise. -/
theorem exactRGSWMinusSecretViewRandomization_randomizedView_tvDist_eq_zero
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels : ℕ) (errorSampler : ProbComp R) (gadget : Fin levels → R)
    (secret : R) :
    tvDist
        ((exactRGSWMinusSecretViewRandomization levels errorSampler gadget).randomizedView
          secret)
        (exactRGSWMinusSecretViewRandomization levels errorSampler gadget).freshWideView =
      0 := by
  apply le_antisymm
  · simpa using
      (LWE.AuxiliaryInput.SearchToDecision.ViewRandomization.randomizedView_tvDist_freshWideView_le
        (exactRGSWMinusSecretViewRandomization levels errorSampler gadget) secret)
  · exact tvDist_nonneg _ _

/-! ## Complete circular-auxiliary plus ordinary-RLWE view -/

/-- Public key transport for a batch of ordinary rank-one zero-message RLWE rows. -/
def zeroBatchKeyShift
    {R : Type} [CommRing R] {samples : ℕ}
    (shift : R) (ciphertext : TLWE.BatchCiphertext R 1 samples) :
    TLWE.BatchCiphertext R 1 samples :=
  (ciphertext.1,
    fun row ↦ ciphertext.2 row + ciphertext.1 0 row * shift)

@[simp]
theorem zeroBatchKeyShift_neg
    {R : Type} [CommRing R] {samples : ℕ}
    (shift : R) (ciphertext : TLWE.BatchCiphertext R 1 samples) :
    zeroBatchKeyShift (-shift) (zeroBatchKeyShift shift ciphertext) = ciphertext := by
  apply Prod.ext
  · rfl
  · funext row
    simp [zeroBatchKeyShift]

theorem zeroBatchKeyShift_bijective
    {R : Type} [CommRing R] {samples : ℕ} (shift : R) :
    Function.Bijective
      (zeroBatchKeyShift shift : TLWE.BatchCiphertext R 1 samples → _) := by
  apply Function.bijective_iff_has_inverse.mpr
  exact ⟨zeroBatchKeyShift (-shift), zeroBatchKeyShift_neg shift,
    by
      intro ciphertext
      simpa only [neg_neg] using zeroBatchKeyShift_neg (-shift) ciphertext⟩

/-- Ordinary zero-message rows move from key `S` to key `S+r` while keeping every error
coordinate unchanged. -/
theorem zeroBatchKeyShift_batchAssemble
    {R : Type} [CommRing R] {samples : ℕ}
    (secret : Fin 1 → R) (shift : R)
    (challenge : Matrix (Fin 1) (Fin samples) R)
    (error : Fin samples → R) :
    zeroBatchKeyShift shift
        (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble (fun _ ↦ secret 0 + shift) challenge 0 error := by
  apply Prod.ext
  · rfl
  · funext row
    simp [zeroBatchKeyShift, TLWE.batchAssemble, Matrix.vecMul, dotProduct]
    ring

/-- Fixed-shift transport of a fresh ordinary zero-message batch is exact and does not change
the error sampler. -/
theorem zeroBatchKeyShift_batchEncrypt_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (samples : ℕ) (errorSampler : ProbComp R) (secret : Fin 1 → R)
    (shift : R) :
    evalDist (zeroBatchKeyShift shift <$>
        TLWE.batchEncrypt 1 samples errorSampler secret 0) =
      evalDist (TLWE.batchEncrypt 1 samples errorSampler
        (fun _ ↦ secret 0 + shift) 0) := by
  unfold TLWE.batchEncrypt
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine evalDist_bind_congr'
    ($ᵗ Matrix (Fin 1) (Fin samples) R) fun challenge ↦ ?_
  refine evalDist_bind_congr'
    (ProbComp.sampleIID samples errorSampler) fun error ↦ ?_
  exact congrArg evalDist
    (congrArg pure (zeroBatchKeyShift_batchAssemble secret shift challenge error))

/-- The ordinary-batch key transport also preserves an exactly uniform transcript. -/
theorem zeroBatchKeyShift_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    {samples : ℕ} (shift : R) :
    evalDist (zeroBatchKeyShift shift <$>
        ($ᵗ TLWE.BatchCiphertext R 1 samples)) =
      evalDist ($ᵗ TLWE.BatchCiphertext R 1 samples) :=
  evalDist_map_bijective_uniform_cross
    (α := TLWE.BatchCiphertext R 1 samples)
    (β := TLWE.BatchCiphertext R 1 samples)
    (zeroBatchKeyShift shift) (zeroBatchKeyShift_bijective shift)

/-- Complete public view in the restricted ring-square CircRLWE experiment: the native
`RGSW_S(-S)` auxiliary object and a batch of ordinary rank-one test rows. -/
abbrev CircularView (R : Type) (levels samples : ℕ) :=
  TGSW.Ciphertext R 1 levels × TLWE.BatchCiphertext R 1 samples

/-- Real fixed-secret view: circular auxiliary RGSW plus ordinary zero-message RLWE rows under
the same ring secret. -/
def fixedSecretRealCircularViewSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) :
    ProbComp (CircularView R levels samples) := do
  let auxiliary ← TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0)
  let testRows ← TLWE.batchEncrypt 1 samples testErrorSampler secret 0
  return (auxiliary, testRows)

/-- Uniform-test fixed-secret view: retain the real circular auxiliary object but replace the
ordinary test rows by a fully uniform transcript. -/
def fixedSecretUniformCircularViewSampler
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (gadget : Fin levels → R) :
    ProbComp (CircularView R levels samples) := do
  let auxiliary ← TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0)
  let testRows ← $ᵗ TLWE.BatchCiphertext R 1 samples
  return (auxiliary, testRows)

/-- Shift both components of the complete restricted CircRLWE view. -/
def circularViewKeyShift
    {R : Type} [CommRing R] {levels samples : ℕ}
    (shift : R) (gadget : Fin levels → R)
    (view : CircularView R levels samples) : CircularView R levels samples :=
  (rgswMinusSecretKeyShift shift gadget view.1,
    zeroBatchKeyShift shift view.2)

/-- The complete real circular view transports exactly from `S` to `S+r`, at the original
auxiliary and test error laws. -/
theorem circularViewKeyShift_real_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (shift : R) (gadget : Fin levels → R) :
    evalDist (circularViewKeyShift shift gadget <$>
        fixedSecretRealCircularViewSampler levels samples auxiliaryErrorSampler
          testErrorSampler secret gadget) =
      evalDist (fixedSecretRealCircularViewSampler levels samples auxiliaryErrorSampler
        testErrorSampler (fun _ ↦ secret 0 + shift) gadget) := by
  let oldAuxiliary :=
    TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0)
  let newAuxiliary :=
    TGSW.encrypt 1 levels auxiliaryErrorSampler (fun _ ↦ secret 0 + shift)
      gadget (-(secret 0 + shift))
  let oldTests := TLWE.batchEncrypt 1 samples testErrorSampler secret 0
  let newTests := TLWE.batchEncrypt 1 samples testErrorSampler
    (fun _ ↦ secret 0 + shift) 0
  let finish := fun auxiliary testRows ↦
    (pure (auxiliary, testRows) : ProbComp (CircularView R levels samples))
  calc
    evalDist (circularViewKeyShift shift gadget <$>
        fixedSecretRealCircularViewSampler levels samples auxiliaryErrorSampler
          testErrorSampler secret gadget) =
      evalDist ((rgswMinusSecretKeyShift shift gadget <$> oldAuxiliary) >>=
        fun auxiliary ↦
          (zeroBatchKeyShift shift <$> oldTests) >>= fun testRows ↦
            finish auxiliary testRows) := by
      simp [fixedSecretRealCircularViewSampler, circularViewKeyShift,
        oldAuxiliary, oldTests, finish, map_eq_bind_pure_comp, bind_assoc,
        monad_norm]
    _ = evalDist (newAuxiliary >>= fun auxiliary ↦
        (zeroBatchKeyShift shift <$> oldTests) >>= fun testRows ↦
          finish auxiliary testRows) := by
      rw [evalDist_bind,
        rgswMinusSecretKeyShift_encrypt_evalDist
          auxiliaryErrorSampler secret shift gadget,
        ← evalDist_bind]
    _ = evalDist (newAuxiliary >>= fun auxiliary ↦
        newTests >>= fun testRows ↦ finish auxiliary testRows) := by
      refine evalDist_bind_congr' newAuxiliary fun auxiliary ↦ ?_
      rw [evalDist_bind,
        zeroBatchKeyShift_batchEncrypt_evalDist samples testErrorSampler secret shift,
        ← evalDist_bind]
    _ = evalDist (fixedSecretRealCircularViewSampler levels samples
        auxiliaryErrorSampler testErrorSampler (fun _ ↦ secret 0 + shift) gadget) := by
      simp [fixedSecretRealCircularViewSampler, newAuxiliary, newTests, finish,
        monad_norm]

/-- The same exact shift transports the uniform-test branch: the circular auxiliary follows
the shifted secret and the uniform test transcript remains uniform. -/
theorem circularViewKeyShift_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler : ProbComp R)
    (secret : Fin 1 → R) (shift : R) (gadget : Fin levels → R) :
    evalDist (circularViewKeyShift shift gadget <$>
        fixedSecretUniformCircularViewSampler levels samples auxiliaryErrorSampler
          secret gadget) =
      evalDist (fixedSecretUniformCircularViewSampler levels samples auxiliaryErrorSampler
        (fun _ ↦ secret 0 + shift) gadget) := by
  let oldAuxiliary :=
    TGSW.encrypt 1 levels auxiliaryErrorSampler secret gadget (-secret 0)
  let newAuxiliary :=
    TGSW.encrypt 1 levels auxiliaryErrorSampler (fun _ ↦ secret 0 + shift)
      gadget (-(secret 0 + shift))
  let uniformTests : ProbComp (TLWE.BatchCiphertext R 1 samples) :=
    $ᵗ TLWE.BatchCiphertext R 1 samples
  let finish := fun auxiliary testRows ↦
    (pure (auxiliary, testRows) : ProbComp (CircularView R levels samples))
  calc
    evalDist (circularViewKeyShift shift gadget <$>
        fixedSecretUniformCircularViewSampler levels samples auxiliaryErrorSampler
          secret gadget) =
      evalDist ((rgswMinusSecretKeyShift shift gadget <$> oldAuxiliary) >>=
        fun auxiliary ↦
          (zeroBatchKeyShift shift <$> uniformTests) >>= fun testRows ↦
            finish auxiliary testRows) := by
      simp [fixedSecretUniformCircularViewSampler, circularViewKeyShift,
        oldAuxiliary, uniformTests, finish, map_eq_bind_pure_comp, bind_assoc,
        monad_norm]
    _ = evalDist (newAuxiliary >>= fun auxiliary ↦
        (zeroBatchKeyShift shift <$> uniformTests) >>= fun testRows ↦
          finish auxiliary testRows) := by
      rw [evalDist_bind,
        rgswMinusSecretKeyShift_encrypt_evalDist
          auxiliaryErrorSampler secret shift gadget,
        ← evalDist_bind]
    _ = evalDist (newAuxiliary >>= fun auxiliary ↦
        uniformTests >>= fun testRows ↦ finish auxiliary testRows) := by
      refine evalDist_bind_congr' newAuxiliary fun auxiliary ↦ ?_
      rw [evalDist_bind,
        show evalDist (zeroBatchKeyShift shift <$> uniformTests) =
            evalDist uniformTests by
          exact zeroBatchKeyShift_uniform_evalDist shift,
        ← evalDist_bind]
    _ = evalDist (fixedSecretUniformCircularViewSampler levels samples
        auxiliaryErrorSampler (fun _ ↦ secret 0 + shift) gadget) := by
      simp [fixedSecretUniformCircularViewSampler, newAuxiliary, uniformTests,
        finish, monad_norm]

/-- Zero-loss PKC-style randomizer for the complete real restricted CircRLWE view. -/
def exactRealCircularViewRandomization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      R R (CircularView R levels samples) :=
  LWE.AuxiliaryInput.SearchToDecision.ViewRandomization.ofExact
    ($ᵗ R) (fun secret shift ↦ secret + shift) ($ᵗ R)
    (fun secret ↦ fixedSecretRealCircularViewSampler levels samples
      auxiliaryErrorSampler testErrorSampler (fun _ ↦ secret) gadget)
    (fun shift ↦ pure ∘ circularViewKeyShift shift gadget)
    (fun secret ↦ add_uniform_evalDist secret)
    (fun secret shift ↦ by
      simpa only [← map_eq_bind_pure_comp] using
        (circularViewKeyShift_real_evalDist levels samples auxiliaryErrorSampler
          testErrorSampler (fun _ : Fin 1 ↦ secret) shift gadget))

/-- Zero-loss PKC-style randomizer for the corresponding uniform-test branch. -/
def exactUniformCircularViewRandomization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      R R (CircularView R levels samples) :=
  LWE.AuxiliaryInput.SearchToDecision.ViewRandomization.ofExact
    ($ᵗ R) (fun secret shift ↦ secret + shift) ($ᵗ R)
    (fun secret ↦ fixedSecretUniformCircularViewSampler levels samples
      auxiliaryErrorSampler (fun _ ↦ secret) gadget)
    (fun shift ↦ pure ∘ circularViewKeyShift shift gadget)
    (fun secret ↦ add_uniform_evalDist secret)
    (fun secret shift ↦ by
      simpa only [← map_eq_bind_pure_comp] using
        (circularViewKeyShift_uniform_evalDist levels samples auxiliaryErrorSampler
          (fun _ : Fin 1 ↦ secret) shift gadget))

@[simp]
theorem exactRealCircularViewRandomization_error
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler testErrorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    (exactRealCircularViewRandomization levels samples auxiliaryErrorSampler
      testErrorSampler gadget).error = 0 := rfl

@[simp]
theorem exactUniformCircularViewRandomization_error
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels samples : ℕ) (auxiliaryErrorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    (exactUniformCircularViewRandomization levels samples auxiliaryErrorSampler
      gadget).error = 0 := rfl

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.SecretRandomization
