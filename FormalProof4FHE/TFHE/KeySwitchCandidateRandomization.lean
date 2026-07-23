/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.TFHE.Native

/-!
# Candidate Randomization of a Native TFHE Key-Switch Key

This file formalizes the exact algebra behind the key-switch-first coordinate test used by a
binary-secret search-to-decision reduction.  Given a proposed value `candidate` for one scalar
secret coordinate, sample a fresh vector `u`, add `u` to that row of every public TLWE challenge,
and add `candidate * u` to the corresponding bodies.

* If the candidate is correct, this is merely a fresh presentation of the same TLWE batch.
* If the candidate is wrong, the difference between the candidate and the binary secret is
  `+1` or `-1`.  Hence the map from `(challenge, u)` to the transformed transcript is a
  permutation, so a uniform input pair produces an exactly uniform TLWE batch.

The result is valid over every finite commutative ring; it does not require division, a field, or
a Gaussian error law.  The error and message vectors are arbitrary and fixed in the core
bijection.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.KeySwitchCandidateRandomization

/-- Add a vector to one distinguished row of a batch challenge. -/
def shiftChallengeRow {R : Type} [AddMonoid R] {dimension samples : ℕ}
    (coordinate : Fin dimension) (shift : Fin samples → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  fun row sample => challenge row sample + if row = coordinate then shift sample else 0

@[simp]
theorem shiftChallengeRow_zero {R : Type} [AddMonoid R] {dimension samples : ℕ}
    (coordinate : Fin dimension)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    shiftChallengeRow coordinate 0 challenge = challenge := by
  funext row sample
  by_cases hrow : row = coordinate <;> simp [shiftChallengeRow, hrow]

@[simp]
theorem shiftChallengeRow_neg_shiftChallengeRow {R : Type} [AddGroup R]
    {dimension samples : ℕ} (coordinate : Fin dimension)
    (shift : Fin samples → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    shiftChallengeRow coordinate (-shift)
        (shiftChallengeRow coordinate shift challenge) = challenge := by
  funext row sample
  by_cases hrow : row = coordinate <;> simp [shiftChallengeRow, hrow]

@[simp]
theorem shiftChallengeRow_shiftChallengeRow_neg {R : Type} [AddGroup R]
    {dimension samples : ℕ} (coordinate : Fin dimension)
    (shift : Fin samples → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    shiftChallengeRow coordinate shift
        (shiftChallengeRow coordinate (-shift) challenge) = challenge := by
  funext row sample
  by_cases hrow : row = coordinate <;> simp [shiftChallengeRow, hrow]

/-- Translation of one fixed challenge row is a permutation. -/
theorem shiftChallengeRow_bijective {R : Type} [AddGroup R]
    {dimension samples : ℕ} (coordinate : Fin dimension)
    (shift : Fin samples → R) :
    Function.Bijective
      (shiftChallengeRow coordinate shift :
        Matrix (Fin dimension) (Fin samples) R →
          Matrix (Fin dimension) (Fin samples) R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨shiftChallengeRow coordinate (-shift),
      shiftChallengeRow_neg_shiftChallengeRow coordinate shift,
      shiftChallengeRow_shiftChallengeRow_neg coordinate shift⟩

/-- A fixed row translation preserves the uniform challenge distribution. -/
theorem shiftChallengeRow_uniform_evalDist {R : Type} [AddGroup R]
    [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (coordinate : Fin dimension) (shift : Fin samples → R) :
    evalDist (shiftChallengeRow coordinate shift <$>
        ($ᵗ Matrix (Fin dimension) (Fin samples) R)) =
      evalDist ($ᵗ Matrix (Fin dimension) (Fin samples) R) :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin samples) R)
    (β := Matrix (Fin dimension) (Fin samples) R)
    (shiftChallengeRow coordinate shift)
    (shiftChallengeRow_bijective coordinate shift)

/-- Shifting one challenge row changes the batch inner product by exactly that secret
coordinate times the shift. -/
theorem vecMul_shiftChallengeRow {R : Type} [Semiring R] {dimension samples : ℕ}
    (secret : Fin dimension → R) (coordinate : Fin dimension)
    (shift : Fin samples → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    vecMul secret (shiftChallengeRow coordinate shift challenge) =
      vecMul secret challenge + fun sample => secret coordinate * shift sample := by
  funext sample
  simp only [Matrix.vecMul, dotProduct, shiftChallengeRow, Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

/-- Apply the coordinate-candidate transform to an arbitrary TLWE batch. -/
def randomizeBatch {R : Type} [Semiring R] {dimension samples : ℕ}
    (coordinate : Fin dimension) (candidate : Bool) (shift : Fin samples → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    TLWE.BatchCiphertext R dimension samples :=
  (shiftChallengeRow coordinate shift ciphertext.1,
    fun sample => ciphertext.2 sample + embedBit candidate * shift sample)

/-- With the correct candidate, coordinate randomization preserves the deterministic TLWE
assembly while replacing its challenge by the shifted challenge. -/
theorem randomizeBatch_batchAssemble_correct {R : Type} [CommSemiring R]
    {dimension samples : ℕ} (secret : BinarySecret dimension)
    (coordinate : Fin dimension) (shift : Fin samples → R)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (message error : Fin samples → R) :
    randomizeBatch coordinate (secret coordinate) shift
        (TLWE.batchAssemble (embedBinarySecret secret) challenge message error) =
      TLWE.batchAssemble (embedBinarySecret secret)
        (shiftChallengeRow coordinate shift challenge) message error := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [randomizeBatch, TLWE.batchAssemble, Pi.add_apply]
    rw [show vecMul (embedBinarySecret secret)
        (shiftChallengeRow coordinate shift challenge) sample =
          vecMul (embedBinarySecret secret) challenge sample +
            embedBit (secret coordinate) * shift sample by
      exact congrFun
        (vecMul_shiftChallengeRow (embedBinarySecret secret) coordinate shift challenge)
        sample]
    ac_rfl

/-- Candidate minus hidden bit, embedded in the coefficient ring. -/
def candidateDifference {R : Type} [Ring R] (hidden candidate : Bool) : R :=
  embedBit candidate - embedBit hidden

/-- For unequal bits the embedded candidate difference is `+1` or `-1`, hence its square is
one over every ring. -/
@[simp]
theorem candidateDifference_sq_of_ne {R : Type} [Ring R]
    (hidden candidate : Bool) (hne : candidate ≠ hidden) :
    candidateDifference (R := R) hidden candidate *
        candidateDifference hidden candidate = 1 := by
  cases hidden <;> cases candidate <;>
    simp_all [candidateDifference, embedBit]

/-- The deterministic map whose domain contains a uniform challenge and the fresh shift. -/
def assembleCandidate {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret : BinarySecret dimension) (coordinate : Fin dimension) (candidate : Bool)
    (message error : Fin samples → R)
    (input : Matrix (Fin dimension) (Fin samples) R × (Fin samples → R)) :
    TLWE.BatchCiphertext R dimension samples :=
  randomizeBatch coordinate candidate input.2
    (TLWE.batchAssemble (embedBinarySecret secret) input.1 message error)

/-- Recover the fresh shift from a transformed transcript when the candidate is wrong. -/
def recoverShift {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret : BinarySecret dimension) (coordinate : Fin dimension) (candidate : Bool)
    (message error : Fin samples → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) : Fin samples → R :=
  fun sample =>
    candidateDifference (R := R) (secret coordinate) candidate *
      (ciphertext.2 sample -
        (vecMul (embedBinarySecret secret) ciphertext.1 sample +
          message sample + error sample))

/-- Explicit inverse to `assembleCandidate` in the wrong-candidate case. -/
def unassembleCandidate {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret : BinarySecret dimension) (coordinate : Fin dimension) (candidate : Bool)
    (message error : Fin samples → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    Matrix (Fin dimension) (Fin samples) R × (Fin samples → R) :=
  let shift := recoverShift secret coordinate candidate message error ciphertext
  (shiftChallengeRow coordinate (-shift) ciphertext.1, shift)

theorem recoverShift_assembleCandidate {R : Type} [CommRing R]
    {dimension samples : ℕ} (secret : BinarySecret dimension)
    (coordinate : Fin dimension) (candidate : Bool) (hcandidate : candidate ≠ secret coordinate)
    (message error : Fin samples → R)
    (input : Matrix (Fin dimension) (Fin samples) R × (Fin samples → R)) :
    recoverShift secret coordinate candidate message error
        (assembleCandidate secret coordinate candidate message error input) = input.2 := by
  funext sample
  simp only [recoverShift, assembleCandidate, randomizeBatch, TLWE.batchAssemble,
    Pi.add_apply]
  rw [show vecMul (embedBinarySecret secret)
      (shiftChallengeRow coordinate input.2 input.1) sample =
        vecMul (embedBinarySecret secret) input.1 sample +
          embedBit (secret coordinate) * input.2 sample by
    exact congrFun
      (vecMul_shiftChallengeRow (embedBinarySecret secret) coordinate input.2 input.1)
      sample]
  cases hc : candidate <;> cases hs : secret coordinate <;>
    simp_all [candidateDifference, embedBit]

@[simp]
theorem unassembleCandidate_assembleCandidate {R : Type} [CommRing R]
    {dimension samples : ℕ} (secret : BinarySecret dimension)
    (coordinate : Fin dimension) (candidate : Bool) (hcandidate : candidate ≠ secret coordinate)
    (message error : Fin samples → R)
    (input : Matrix (Fin dimension) (Fin samples) R × (Fin samples → R)) :
    unassembleCandidate secret coordinate candidate message error
        (assembleCandidate secret coordinate candidate message error input) = input := by
  apply Prod.ext
  · change shiftChallengeRow coordinate
        (-recoverShift secret coordinate candidate message error
          (assembleCandidate secret coordinate candidate message error input))
        (shiftChallengeRow coordinate input.2 input.1) = input.1
    rw [recoverShift_assembleCandidate secret coordinate candidate hcandidate]
    exact shiftChallengeRow_neg_shiftChallengeRow coordinate input.2 input.1
  · exact recoverShift_assembleCandidate secret coordinate candidate hcandidate
      message error input

@[simp]
theorem assembleCandidate_unassembleCandidate {R : Type} [CommRing R]
    {dimension samples : ℕ} (secret : BinarySecret dimension)
    (coordinate : Fin dimension) (candidate : Bool) (hcandidate : candidate ≠ secret coordinate)
    (message error : Fin samples → R)
    (ciphertext : TLWE.BatchCiphertext R dimension samples) :
    assembleCandidate secret coordinate candidate message error
        (unassembleCandidate secret coordinate candidate message error ciphertext) = ciphertext := by
  apply Prod.ext
  · change shiftChallengeRow coordinate
        (recoverShift secret coordinate candidate message error ciphertext)
        (shiftChallengeRow coordinate
          (-recoverShift secret coordinate candidate message error ciphertext)
          ciphertext.1) = ciphertext.1
    exact shiftChallengeRow_shiftChallengeRow_neg coordinate
      (recoverShift secret coordinate candidate message error ciphertext) ciphertext.1
  · funext sample
    let shift := recoverShift secret coordinate candidate message error ciphertext
    simp only [assembleCandidate, unassembleCandidate, randomizeBatch,
      TLWE.batchAssemble, Pi.add_apply]
    rw [show vecMul (embedBinarySecret secret)
        (shiftChallengeRow coordinate (-shift) ciphertext.1) sample =
          vecMul (embedBinarySecret secret) ciphertext.1 sample -
            embedBit (secret coordinate) * shift sample by
      simpa [embedBinarySecret, sub_eq_add_neg] using congrFun
        (vecMul_shiftChallengeRow (embedBinarySecret secret) coordinate (-shift)
          ciphertext.1) sample]
    change
      vecMul (embedBinarySecret secret) ciphertext.1 sample -
            embedBit (secret coordinate) * shift sample + message sample + error sample +
          embedBit candidate * shift sample = ciphertext.2 sample
    unfold shift
    simp only [recoverShift]
    cases hc : candidate <;> cases hs : secret coordinate
    all_goals simp_all [candidateDifference, embedBit]
    all_goals ring

/-- For a wrong binary candidate, the challenge-and-shift map is a permutation of the complete
TLWE batch space. -/
theorem assembleCandidate_bijective {R : Type} [CommRing R]
    {dimension samples : ℕ} (secret : BinarySecret dimension)
    (coordinate : Fin dimension) (candidate : Bool) (hcandidate : candidate ≠ secret coordinate)
    (message error : Fin samples → R) :
    Function.Bijective
      (assembleCandidate (R := R) secret coordinate candidate message error) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unassembleCandidate secret coordinate candidate message error,
      unassembleCandidate_assembleCandidate secret coordinate candidate hcandidate message error,
      assembleCandidate_unassembleCandidate secret coordinate candidate hcandidate message error⟩

/-! ## Exact fixed-message distribution laws -/

/-- For a correct candidate and fixed message/error vectors, averaging over both the original
uniform challenge and the fresh shift gives the original real TLWE distribution exactly. -/
theorem randomizeAssembled_correct_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (secret : BinarySecret dimension) (coordinate : Fin dimension)
    (message error : Fin samples → R) :
    evalDist (do
      let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
      let shift ← $ᵗ (Fin samples → R)
      return randomizeBatch coordinate (secret coordinate) shift
        (TLWE.batchAssemble (embedBinarySecret secret) challenge message error)) =
    evalDist (do
      let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
      return TLWE.batchAssemble (embedBinarySecret secret) challenge message error) := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let shifts : ProbComp (Fin samples → R) := $ᵗ (Fin samples → R)
  let finish := fun challenge =>
    (pure (TLWE.batchAssemble (embedBinarySecret secret) challenge message error) :
      ProbComp (TLWE.BatchCiphertext R dimension samples))
  calc
    _ = evalDist (shifts >>= fun shift =>
        challenges >>= fun challenge =>
        pure (randomizeBatch coordinate (secret coordinate) shift
          (TLWE.batchAssemble (embedBinarySecret secret) challenge message error))) := by
      exact evalDist_bind_bind_swap challenges shifts _
    _ = evalDist (shifts >>= fun _ => challenges >>= finish) := by
      refine evalDist_bind_congr' shifts fun shift => ?_
      calc
        _ = evalDist (challenges >>= fun challenge =>
            pure (TLWE.batchAssemble (embedBinarySecret secret)
              (shiftChallengeRow coordinate shift challenge) message error)) := by
          refine evalDist_bind_congr' challenges fun challenge => ?_
          simpa only using congrArg evalDist (congrArg pure
            (randomizeBatch_batchAssemble_correct secret coordinate shift
              challenge message error))
        _ = evalDist ((shiftChallengeRow coordinate shift <$> challenges) >>= finish) := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          simp only [Function.comp_apply, pure_bind, finish]
        _ = evalDist (challenges >>= finish) := by
          rw [evalDist_bind, shiftChallengeRow_uniform_evalDist coordinate shift,
            ← evalDist_bind]
    _ = evalDist (challenges >>= finish) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        shifts (by simp [shifts]) _
    _ = _ := by simp [challenges, finish]

/-- For a wrong candidate and fixed message/error vectors, the transformed TLWE batch is exactly
uniform.  This is the core information-theoretic KSK-first candidate law. -/
theorem randomizeAssembled_wrong_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R] {dimension samples : ℕ}
    (secret : BinarySecret dimension) (coordinate : Fin dimension) (candidate : Bool)
    (hcandidate : candidate ≠ secret coordinate) (message error : Fin samples → R) :
    evalDist (do
      let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
      let shift ← $ᵗ (Fin samples → R)
      return randomizeBatch coordinate candidate shift
        (TLWE.batchAssemble (embedBinarySecret secret) challenge message error)) =
      evalDist ($ᵗ TLWE.BatchCiphertext R dimension samples) := by
  let pairs : ProbComp
      (Matrix (Fin dimension) (Fin samples) R × (Fin samples → R)) := do
    let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
    let shift ← $ᵗ (Fin samples → R)
    return (challenge, shift)
  have hpairs :
      evalDist pairs = evalDist ($ᵗ
        (Matrix (Fin dimension) (Fin samples) R × (Fin samples → R))) := by
    simpa only [pairs] using
      (FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
        (first := Matrix (Fin dimension) (Fin samples) R)
        (second := Fin samples → R))
  rw [show (do
      let challenge ← $ᵗ Matrix (Fin dimension) (Fin samples) R
      let shift ← $ᵗ (Fin samples → R)
      return randomizeBatch coordinate candidate shift
        (TLWE.batchAssemble (embedBinarySecret secret) challenge message error)) =
      (pairs >>= fun input =>
        pure (assembleCandidate secret coordinate candidate message error input)) by
    simp [pairs, assembleCandidate, monad_norm]]
  calc
    _ = evalDist (($ᵗ
          (Matrix (Fin dimension) (Fin samples) R × (Fin samples → R))) >>= fun input =>
        pure (assembleCandidate secret coordinate candidate message error input)) := by
      rw [evalDist_bind, hpairs, ← evalDist_bind]
    _ = _ := by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (evalDist_map_bijective_uniform_cross
          (α := Matrix (Fin dimension) (Fin samples) R × (Fin samples → R))
          (β := TLWE.BatchCiphertext R dimension samples)
          (assembleCandidate secret coordinate candidate message error)
          (assembleCandidate_bijective secret coordinate candidate hcandidate message error))

/-! ## Native batch-encryption laws -/

/-- Sample the native TLWE batch and then apply fresh coordinate-candidate randomization. -/
def randomizeEncryption {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ} (errorSampler : ProbComp R)
    (secret : BinarySecret dimension) (coordinate : Fin dimension) (candidate : Bool)
    (message : Fin samples → R) : ProbComp (TLWE.BatchCiphertext R dimension samples) := do
  let ciphertext ← TLWE.batchEncrypt dimension samples errorSampler
    (embedBinarySecret secret) message
  let shift ← $ᵗ (Fin samples → R)
  return randomizeBatch coordinate candidate shift ciphertext

/-- A correct candidate leaves the native fixed-message batch-encryption distribution exactly
unchanged. -/
theorem randomizeEncryption_correct_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ} (errorSampler : ProbComp R)
    (secret : BinarySecret dimension) (coordinate : Fin dimension)
    (message : Fin samples → R) :
    evalDist (randomizeEncryption errorSampler secret coordinate
      (secret coordinate) message) =
      evalDist (TLWE.batchEncrypt dimension samples errorSampler
        (embedBinarySecret secret) message) := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let errors : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let shifts : ProbComp (Fin samples → R) := $ᵗ (Fin samples → R)
  rw [show randomizeEncryption errorSampler secret coordinate
      (secret coordinate) message =
      (challenges >>= fun challenge =>
        errors >>= fun error =>
        shifts >>= fun shift =>
        pure (randomizeBatch coordinate (secret coordinate) shift
          (TLWE.batchAssemble (embedBinarySecret secret) challenge message error))) by
    simp [randomizeEncryption, TLWE.batchEncrypt, challenges, errors, shifts, monad_norm]]
  calc
    _ = evalDist (errors >>= fun error =>
        challenges >>= fun challenge =>
        shifts >>= fun shift =>
        pure (randomizeBatch coordinate (secret coordinate) shift
          (TLWE.batchAssemble (embedBinarySecret secret) challenge message error))) :=
      evalDist_bind_bind_swap challenges errors _
    _ = evalDist (errors >>= fun error =>
        challenges >>= fun challenge =>
        pure (TLWE.batchAssemble (embedBinarySecret secret) challenge message error)) := by
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [challenges, shifts] using
        (randomizeAssembled_correct_evalDist secret coordinate message error)
    _ = evalDist (challenges >>= fun challenge =>
        errors >>= fun error =>
        pure (TLWE.batchAssemble (embedBinarySecret secret) challenge message error)) :=
      (evalDist_bind_bind_swap challenges errors _).symm
    _ = _ := by simp [TLWE.batchEncrypt, challenges, errors, monad_norm]

/-- A wrong candidate makes the native fixed-message batch-encryption transcript exactly uniform.
The only sampler-side premise is that the scalar error sampler never fails; its distribution may
otherwise be arbitrary (including centered binomial or discrete Gaussian). -/
theorem randomizeEncryption_wrong_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ} (errorSampler : ProbComp R)
    (hError : Pr[⊥ | errorSampler] = 0)
    (secret : BinarySecret dimension) (coordinate : Fin dimension) (candidate : Bool)
    (hcandidate : candidate ≠ secret coordinate)
    (message : Fin samples → R) :
    evalDist (randomizeEncryption errorSampler secret coordinate candidate message) =
      evalDist ($ᵗ TLWE.BatchCiphertext R dimension samples) := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let errors : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let shifts : ProbComp (Fin samples → R) := $ᵗ (Fin samples → R)
  rw [show randomizeEncryption errorSampler secret coordinate candidate message =
      (challenges >>= fun challenge =>
        errors >>= fun error =>
        shifts >>= fun shift =>
        pure (randomizeBatch coordinate candidate shift
          (TLWE.batchAssemble (embedBinarySecret secret) challenge message error))) by
    simp [randomizeEncryption, TLWE.batchEncrypt, challenges, errors, shifts, monad_norm]]
  calc
    _ = evalDist (errors >>= fun error =>
        challenges >>= fun challenge =>
        shifts >>= fun shift =>
        pure (randomizeBatch coordinate candidate shift
          (TLWE.batchAssemble (embedBinarySecret secret) challenge message error))) :=
      evalDist_bind_bind_swap challenges errors _
    _ = evalDist (errors >>= fun _ =>
        ($ᵗ TLWE.BatchCiphertext R dimension samples)) := by
      refine evalDist_bind_congr' errors fun error => ?_
      simpa only [challenges, shifts] using
        (randomizeAssembled_wrong_evalDist secret coordinate candidate hcandidate
          message error)
    _ = _ :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        errors
        (FormalProof4FHE.SharedRandomness.probFailure_sampleIID_eq_zero
          samples errorSampler hError) _

/-! ## Native key-switch-key specialization -/

/-- Coordinate-candidate randomization of the complete native TFHE key-switch table. -/
def randomizeKeySwitchKey
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension)
    (coordinate : Fin targetDimension) (candidate : Bool) :
    ProbComp (KeySwitchKey q targetDimension sourceDimension keySwitchLevels) :=
  randomizeEncryption errorSampler targetSecret coordinate candidate
    (keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret)

/-- Supplying the true scalar-key bit leaves the native real KSK law unchanged exactly. -/
theorem randomizeKeySwitchKey_correct_evalDist
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension)
    (coordinate : Fin targetDimension) :
    evalDist (randomizeKeySwitchKey q targetDimension sourceDimension keySwitchLevels
      errorSampler gadget sourceSecret targetSecret coordinate (targetSecret coordinate)) =
      evalDist (generateKeySwitchKey q targetDimension sourceDimension keySwitchLevels
        errorSampler gadget sourceSecret targetSecret) := by
  simpa only [randomizeKeySwitchKey, generateKeySwitchKey] using
    (randomizeEncryption_correct_evalDist errorSampler targetSecret coordinate
      (keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret))

/-- Supplying the wrong scalar-key bit makes the complete native KSK exactly uniform, while
retaining arbitrary fixed source-key gadget messages. -/
theorem randomizeKeySwitchKey_wrong_evalDist
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) (hError : Pr[⊥ | errorSampler] = 0)
    (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension)
    (coordinate : Fin targetDimension) (candidate : Bool)
    (hcandidate : candidate ≠ targetSecret coordinate) :
    evalDist (randomizeKeySwitchKey q targetDimension sourceDimension keySwitchLevels
      errorSampler gadget sourceSecret targetSecret coordinate candidate) =
      evalDist ($ᵗ KeySwitchKey q targetDimension sourceDimension keySwitchLevels) := by
  simpa only [randomizeKeySwitchKey] using
    (randomizeEncryption_wrong_evalDist errorSampler hError targetSecret coordinate
      candidate hcandidate
      (keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret))

end FormalProof4FHE.TFHE.Native.KeySwitchCandidateRandomization
