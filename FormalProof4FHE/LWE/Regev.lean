/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime

/-!
# Regev Encryption and the Decisional-LWE Game Hop

This module gives a current VCVio formulation of Regev encryption over `ZMod q`. Its main theorem
separates the one-time IND-CPA proof into an exact decisional-LWE key-replacement hop and a
statistical masking term. The latter is the precise leftover-hash boundary that remains to be
bounded from concrete parameters.
-/

open AsymmEncAlg Matrix OracleComp

namespace FormalProof4FHE.Regev

/-- A Regev public key `(A, sᵀ A + e)` containing `m` LWE samples. -/
abbrev PublicKey (q n m : ℕ) :=
  Matrix (Fin n) (Fin m) (ZMod q) × (Fin m → ZMod q)

/-- The Regev secret vector. -/
abbrev SecretKey (q n : ℕ) := Fin n → ZMod q

/-- A Regev ciphertext `(A r, ⟨b,r⟩ + encode(message))`. -/
abbrev Ciphertext (q n : ℕ) := (Fin n → ZMod q) × ZMod q

/-- Sample a vector whose coefficients are uniform bits embedded as zero or one in `ZMod q`. -/
def sampleBinaryVector (q m : ℕ) [NeZero q] : ProbComp (Fin m → ZMod q) := do
  let bits ← $ᵗ (Fin m → Bool)
  return fun i ↦ if bits i then 1 else 0

/-- The Regev encryption algorithm with abstract message encoding and decoding functions.

Security uses only `encode`; keeping `decode` explicit makes the algorithm a genuine encryption
scheme while allowing correctness and concrete rounding parameters to be developed independently. -/
def scheme (q n m : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (encode : Bool → ZMod q) (decode : ZMod q → Option Bool) :
    AsymmEncAlg ProbComp Bool (PublicKey q n m) (SecretKey q n) (Ciphertext q n) where
  keygen := do
    let A ← $ᵗ Matrix (Fin n) (Fin m) (ZMod q)
    let secret ← $ᵗ (Fin n → ZMod q)
    let error ← ProbComp.sampleIID m errorSampler
    return ((A, vecMul secret A + error), secret)
  encrypt := fun pk message ↦ do
    let randomness ← sampleBinaryVector q m
    return (pk.1.mulVec randomness, dotProduct pk.2 randomness + encode message)
  decrypt := fun secret ciphertext ↦
    return decode (ciphertext.2 - dotProduct secret ciphertext.1)

/-- The batch decisional-LWE problem used by Regev key generation. -/
abbrev lweProblem (q n m : ℕ) [NeZero q] (errorSampler : ProbComp (ZMod q)) :=
  FormalProof4FHE.LWE.zmodBatchProblem n m q errorSampler

section Games

variable {q n m : ℕ} [NeZero q]
  (errorSampler : ProbComp (ZMod q))
  (encode : Bool → ZMod q) (decode : ZMod q → Option Bool)

/-- The signed advantage of a Boolean winning game. -/
noncomputable def signedAdvantage (game : ProbComp Bool) : ℝ :=
  (Pr[= true | game]).toReal - 1 / 2

/-- One-time IND-CPA with an explicit public-key sampler, written with the key sampled before the
hidden bit. This order aligns the real and uniform branches definitionally with the LWE games. -/
def keyFirstGame
    (publicKeySampler : ProbComp (PublicKey q n m))
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool := do
  let publicKey ← publicKeySampler
  let bit ← $ᵗ Bool
  let (message₀, message₁, state) ← adversary.chooseMessages publicKey
  let ciphertext ←
    (scheme q n m errorSampler encode decode).encrypt publicKey
      (if bit then message₀ else message₁)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- The same explicit-key game in the conventional order, with the hidden bit sampled first. -/
def bitFirstGame
    (publicKeySampler : ProbComp (PublicKey q n m))
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let publicKey ← publicKeySampler
  let (message₀, message₁, state) ← adversary.chooseMessages publicKey
  let ciphertext ←
    (scheme q n m errorSampler encode decode).encrypt publicKey
      (if bit then message₀ else message₁)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- Sampling the public key and the hidden bit commutes because the two samplers are independent. -/
theorem bitFirstGame_probOutput_eq_keyFirstGame
    (publicKeySampler : ProbComp (PublicKey q n m))
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode))
    (result : Bool) :
    Pr[= result | bitFirstGame errorSampler encode decode publicKeySampler adversary] =
      Pr[= result | keyFirstGame errorSampler encode decode publicKeySampler adversary] := by
  simpa [bitFirstGame, keyFirstGame] using
    (probOutput_bind_bind_swap ($ᵗ Bool) publicKeySampler
      (fun bit publicKey ↦ do
        let (message₀, message₁, state) ← adversary.chooseMessages publicKey
        let ciphertext ←
          (scheme q n m errorSampler encode decode).encrypt publicKey
            (if bit then message₀ else message₁)
        let guess ← adversary.distinguish state ciphertext
        return (bit == guess)) result)

/-- The honest Regev game, whose public key is a batch of real LWE samples. -/
def realGame
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool :=
  keyFirstGame errorSampler encode decode
    (LearningWithErrors.distr (lweProblem q n m errorSampler)) adversary

/-- The first hybrid, replacing `sᵀ A + e` in the public key by a uniform vector. -/
def uniformKeyGame
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool :=
  keyFirstGame errorSampler encode decode
    (LearningWithErrors.uniformDistr (lweProblem q n m errorSampler)) adversary

/-- The terminal information-theoretic game: the public key and challenge ciphertext are uniform,
and the fair hidden bit is sampled only after the adversary's guess. -/
def idealGame
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool := do
  let publicKey ← LearningWithErrors.uniformDistr (lweProblem q n m errorSampler)
  let (_, _, state) ← adversary.chooseMessages publicKey
  let ciphertext ← $ᵗ Ciphertext q n
  let guess ← adversary.distinguish state ciphertext
  let bit ← $ᵗ Bool
  return (bit == guess)

/-- The downstream leftover-hash term: the distinguishing gap between encrypting under a uniform
public key and replacing the entire ciphertext by an independent uniform value. -/
noncomputable def maskingAdvantage
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ℝ :=
  (uniformKeyGame errorSampler encode decode adversary).boolDistAdvantage
    (idealGame errorSampler encode decode adversary)

/-- The concrete LWE distinguisher obtained from a Regev IND-CPA adversary. Given a candidate
public key, it runs the challenge phase and returns whether that adversary won. -/
def lweReduction
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    LearningWithErrors.Adversary (lweProblem q n m errorSampler) := fun publicKey ↦ do
  let bit ← $ᵗ Bool
  let (message₀, message₁, state) ← adversary.chooseMessages publicKey
  let ciphertext ←
    (scheme q n m errorSampler encode decode).encrypt publicKey
      (if bit then message₀ else message₁)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- VCVio's standard one-time IND-CPA game for `scheme` is the bit-first game with a real LWE
public-key sampler. The secret-key component produced by key generation is unused. -/
theorem oneTimeGame_probOutput_eq_bitFirstReal
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode))
    (result : Bool) :
    Pr[= result | IND_CPA_OneTime_Game_ProbComp
      (encAlg := scheme q n m errorSampler encode decode) adversary] =
    Pr[= result | bitFirstGame errorSampler encode decode
      (LearningWithErrors.distr (lweProblem q n m errorSampler)) adversary] := by
  simp [IND_CPA_OneTime_Game_ProbComp, bitFirstGame, scheme,
    LearningWithErrors.distr, lweProblem, FormalProof4FHE.LWE.zmodBatchProblem,
    FormalProof4FHE.LWE.batchProblem, monad_norm]

/-- The standard VCVio one-time IND-CPA signed advantage equals the key-first real-game
formulation used by the reduction. -/
theorem oneTime_signedAdvantage_eq_real
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    IND_CPA_OneTime_signedAdvantageReal
        (scheme q n m errorSampler encode decode) adversary =
      signedAdvantage (realGame errorSampler encode decode adversary) := by
  unfold IND_CPA_OneTime_signedAdvantageReal signedAdvantage
  rw [oneTimeGame_probOutput_eq_bitFirstReal errorSampler encode decode adversary true,
    bitFirstGame_probOutput_eq_keyFirstGame errorSampler encode decode
      (LearningWithErrors.distr (lweProblem q n m errorSampler)) adversary true]
  rfl

/-- The real/uniform Regev public-key gap is exactly the advantage of `lweReduction`. -/
theorem real_uniform_gap_eq_lweAdvantage
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    (realGame errorSampler encode decode adversary).boolDistAdvantage
        (uniformKeyGame errorSampler encode decode adversary) =
      LearningWithErrors.advantage (lweProblem q n m errorSampler)
        (lweReduction errorSampler encode decode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  rfl

/-- Replacing an honest Regev public key by uniform changes the absolute signed advantage by at
most the decisional-LWE advantage. -/
theorem abs_signedAdvantage_real_le
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    |signedAdvantage (realGame errorSampler encode decode adversary)| ≤
      |signedAdvantage (uniformKeyGame errorSampler encode decode adversary)| +
        LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) := by
  rw [← real_uniform_gap_eq_lweAdvantage errorSampler encode decode adversary]
  unfold signedAdvantage ProbComp.boolDistAdvantage
  simpa [add_comm] using
    (abs_sub_le
      (Pr[= true | realGame errorSampler encode decode adversary]).toReal
      (Pr[= true | uniformKeyGame errorSampler encode decode adversary]).toReal
      (1 / 2 : ℝ))

/-- The terminal ideal game succeeds with probability exactly one half. -/
theorem idealGame_probOutput_true
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    Pr[= true | idealGame errorSampler encode decode adversary] = 1 / 2 := by
  let preGame : ProbComp Bool := do
    let publicKey ← LearningWithErrors.uniformDistr (lweProblem q n m errorSampler)
    let (_, _, state) ← adversary.chooseMessages publicKey
    let ciphertext ← $ᵗ Ciphertext q n
    adversary.distinguish state ciphertext
  rw [show idealGame errorSampler encode decode adversary = (do
      let guess ← preGame
      let bit ← $ᵗ Bool
      pure (bit == guess)) by
    simp [idealGame, preGame, monad_norm]]
  calc
    _ = Pr[= true | preGame >>= fun _ ↦ ($ᵗ Bool)] := by
      refine probOutput_bind_congr' preGame true fun guess ↦ ?_
      cases guess <;> simp
    _ = 1 / 2 := by simp

/-- In the uniform-key hybrid, absolute signed advantage is exactly the statistical masking term. -/
theorem abs_signedAdvantage_uniformKey_eq_maskingAdvantage
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    |signedAdvantage (uniformKeyGame errorSampler encode decode adversary)| =
      maskingAdvantage errorSampler encode decode adversary := by
  unfold signedAdvantage maskingAdvantage ProbComp.boolDistAdvantage
  rw [idealGame_probOutput_true errorSampler encode decode adversary, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]

/-- Regev's key-first one-time IND-CPA advantage is bounded by decisional LWE plus the explicit
leftover-hash masking term. -/
theorem abs_signedAdvantage_real_le_lwe_add_masking
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    |signedAdvantage (realGame errorSampler encode decode adversary)| ≤
      LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) +
        maskingAdvantage errorSampler encode decode adversary := by
  calc
    _ ≤ |signedAdvantage (uniformKeyGame errorSampler encode decode adversary)| +
          LearningWithErrors.advantage (lweProblem q n m errorSampler)
            (lweReduction errorSampler encode decode adversary) :=
      abs_signedAdvantage_real_le errorSampler encode decode adversary
    _ = _ := by
      rw [abs_signedAdvantage_uniformKey_eq_maskingAdvantage errorSampler encode decode adversary,
        add_comm]

/-- Standard one-time IND-CPA security for Regev: the absolute signed advantage in VCVio's
conventional game is bounded by decisional LWE plus the statistical masking term. -/
theorem oneTime_abs_signedAdvantage_le_lwe_add_masking
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    |IND_CPA_OneTime_signedAdvantageReal
        (scheme q n m errorSampler encode decode) adversary| ≤
      LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) +
        maskingAdvantage errorSampler encode decode adversary := by
  rw [oneTime_signedAdvantage_eq_real errorSampler encode decode adversary]
  exact abs_signedAdvantage_real_le_lwe_add_masking errorSampler encode decode adversary

/-- Bias-advantage form of the Regev reduction. VCVio's Boolean bias is twice the absolute signed
advantage, so both the computational and statistical terms acquire the conventional factor two. -/
theorem oneTime_boolBiasAdvantage_le_two_mul_lwe_add_masking
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    (IND_CPA_OneTime_Game_ProbComp
        (encAlg := scheme q n m errorSampler encode decode) adversary).boolBiasAdvantage ≤
      2 * (LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) +
        maskingAdvantage errorSampler encode decode adversary) := by
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half]
  exact mul_le_mul_of_nonneg_left
    (oneTime_abs_signedAdvantage_le_lwe_add_masking errorSampler encode decode adversary)
    (by norm_num)

end Games

end FormalProof4FHE.Regev
