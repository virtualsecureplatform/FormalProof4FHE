/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import FormalProof4FHE.Probability.LeftoverHash
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime

/-!
# Regev Encryption and the Decisional-LWE Game Hop

This module gives a current VCVio formulation of Regev encryption over `ZMod q`. Its main theorem
combines an exact decisional-LWE key-replacement hop with a finite leftover-hash proof for Regev's
binary subset sums, yielding the concrete one-time bound
`LWEAdv + sqrt (q^(n+1) / 2^m) / 2`.
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

/-- Reindex a Regev public key by columns, viewing every column and its corresponding `b` entry
as one element of the ciphertext group. -/
def publicKeyColumnEquiv (q n m : ℕ) :
    PublicKey q n m ≃ (Fin m → Ciphertext q n) where
  toFun publicKey := fun column ↦
    (fun row ↦ publicKey.1 row column, publicKey.2 column)
  invFun table :=
    (fun row column ↦ (table column).1 row, fun column ↦ (table column).2)
  left_inv publicKey := by
    apply Prod.ext
    · ext row column
      rfl
    · funext column
      rfl
  right_inv table := by
    funext column
    apply Prod.ext
    · funext row
      rfl
    · rfl

/-- The binary subset-sum hash family underlying Regev encryption. -/
def subsetHash (q n m : ℕ) [NeZero q]
    (publicKey : PublicKey q n m) (bits : Fin m → Bool) : Ciphertext q n :=
  FormalProof4FHE.LeftoverHash.binarySubsetSum
    (publicKeyColumnEquiv q n m publicKey) bits

/-- The subset-sum presentation is exactly Regev's matrix/vector encryption core. -/
theorem subsetHash_eq_matrixHash (q n m : ℕ) [NeZero q]
    (publicKey : PublicKey q n m) (bits : Fin m → Bool) :
    subsetHash q n m publicKey bits =
      (publicKey.1.mulVec (fun i ↦ if bits i then 1 else 0),
        dotProduct publicKey.2 (fun i ↦ if bits i then 1 else 0)) := by
  apply Prod.ext
  · funext row
    simp [subsetHash, FormalProof4FHE.LeftoverHash.binarySubsetSum,
      publicKeyColumnEquiv, Matrix.mulVec, dotProduct, Prod.fst_sum]
    apply Finset.sum_congr rfl
    intro column _
    cases bits column <;> simp
  · simp [subsetHash, FormalProof4FHE.LeftoverHash.binarySubsetSum,
      publicKeyColumnEquiv, dotProduct, Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro column _
    cases bits column <;> simp

/-- Regev's binary subset-sum family is two-universal.  Distinct bit vectors differ at a
coordinate whose public-key column is an independent uniform element of the ciphertext group. -/
theorem subsetHash_isTwoUniversal (q n m : ℕ) [NeZero q] :
    FormalProof4FHE.LeftoverHash.IsTwoUniversal
      (PublicKey q n m) (Fin m → Bool) (Ciphertext q n) (subsetHash q n m) := by
  intro x y hxy
  have htable :=
    FormalProof4FHE.LeftoverHash.binarySubsetSum_isTwoUniversal
      (D := Fin m) (G := Ciphertext q n) x y hxy
  have hcollisionCard :
      (Finset.univ.filter fun publicKey : PublicKey q n m =>
          subsetHash q n m publicKey x = subsetHash q n m publicKey y).card =
        (Finset.univ.filter fun table : Fin m → Ciphertext q n =>
          FormalProof4FHE.LeftoverHash.binarySubsetSum table x =
            FormalProof4FHE.LeftoverHash.binarySubsetSum table y).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr
      ((publicKeyColumnEquiv q n m).subtypeEquiv fun _ ↦ Iff.rfl)
  rw [hcollisionCard]
  calc
    (Finset.univ.filter fun table : Fin m → Ciphertext q n =>
        FormalProof4FHE.LeftoverHash.binarySubsetSum table x =
          FormalProof4FHE.LeftoverHash.binarySubsetSum table y).card *
          Fintype.card (Ciphertext q n)
        ≤ Fintype.card (Fin m → Ciphertext q n) := htable
    _ = Fintype.card (PublicKey q n m) :=
      (Fintype.card_congr (publicKeyColumnEquiv q n m)).symm

/-- Concrete leftover-hash bound for Regev's raw public-key/subset-sum distribution. -/
theorem subsetHash_leftover (q n m : ℕ) [NeZero q] :
    tvDist
        (FormalProof4FHE.LeftoverHash.hashed (subsetHash q n m))
        (FormalProof4FHE.LeftoverHash.ideal
          (Seed := PublicKey q n m) (Output := Ciphertext q n)) ≤
      Real.sqrt
          (Fintype.card (Ciphertext q n) /
            Fintype.card (Fin m → Bool)) / 2 :=
  FormalProof4FHE.LeftoverHash.leftover_hash_lemma
    (subsetHash q n m) (subsetHash_isTwoUniversal q n m)

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

/-- The matching public-key distribution of the uniform LWE hybrid is the uniform distribution
on the public-key product type. -/
theorem probOutput_uniformDistr_eq_uniformPublicKey
    (q n m : ℕ) [NeZero q] (errorSampler : ProbComp (ZMod q))
    (publicKey : PublicKey q n m) :
    Pr[= publicKey | LearningWithErrors.uniformDistr (lweProblem q n m errorSampler)] =
      Pr[= publicKey | ($ᵗ PublicKey q n m)] := by
  simp [LearningWithErrors.uniformDistr, lweProblem,
    FormalProof4FHE.LWE.zmodBatchProblem, FormalProof4FHE.LWE.batchProblem,
    probOutput_bind_eq_sum_fintype]
  rw [ENNReal.mul_inv] <;> simp

/-- Uniform sampling on the public-key/ciphertext product agrees with independent component
sampling. -/
theorem evalDist_uniformPublicKeyCiphertext_eq_components
    (q n m : ℕ) [NeZero q] :
    𝒟[$ᵗ (PublicKey q n m × Ciphertext q n)] =
      𝒟[do
        let publicKey ← $ᵗ PublicKey q n m
        let ciphertext ← $ᵗ Ciphertext q n
        return (publicKey, ciphertext)] := by
  apply evalDist_ext
  intro pair
  simp [probOutput_bind_eq_sum_fintype]
  rw [ENNReal.mul_inv
    (Or.inr (ENNReal.mul_ne_top (by simp) (by simp)))
    (Or.inl (ENNReal.mul_ne_top (by simp) (by simp)))]

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

/-- Post-processing applied to the raw leftover-hash source.  The source supplies a public key and
an unshifted subset sum; this computation chooses the IND-CPA messages and adds their encoding. -/
def maskingPostprocess
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode))
    (sample : PublicKey q n m × Ciphertext q n) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let (message₀, message₁, state) ← adversary.chooseMessages sample.1
  let message := if bit then message₀ else message₁
  let ciphertext := (sample.2.1, sample.2.2 + encode message)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- Uniform-key encryption in leftover-hash sampling order. -/
def lhlRealGame
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool := do
  let sample ← FormalProof4FHE.LeftoverHash.hashed (subsetHash q n m)
  maskingPostprocess errorSampler encode decode adversary sample

/-- The corresponding ideal source, post-processed identically. -/
def lhlIdealGame
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) : ProbComp Bool := do
  let sample ← FormalProof4FHE.LeftoverHash.ideal
    (Seed := PublicKey q n m) (Output := Ciphertext q n)
  maskingPostprocess errorSampler encode decode adversary sample

/-- Add an offset to the scalar component of a Regev ciphertext. -/
def shiftCiphertext (offset : ZMod q) (ciphertext : Ciphertext q n) : Ciphertext q n :=
  (ciphertext.1, ciphertext.2 + offset)

omit [NeZero q] in
/-- Ciphertext shifting is a permutation. -/
theorem shiftCiphertext_bijective (offset : ZMod q) :
    Function.Bijective (shiftCiphertext (n := n) offset) := by
  constructor
  · intro left right h
    apply Prod.ext
    · simpa [shiftCiphertext] using congrArg Prod.fst h
    · apply add_right_cancel (b := offset)
      simpa [shiftCiphertext] using congrArg Prod.snd h
  · intro ciphertext
    refine ⟨(ciphertext.1, ciphertext.2 - offset), ?_⟩
    simp [shiftCiphertext]

/-- A fair bit agrees with any independent Boolean computation with probability one half. -/
theorem fairBit_eq_independentGuess (guessGame : ProbComp Bool) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let guess ← guessGame
      return (bit == guess)] = 1 / 2 := by
  calc
    _ = Pr[= true | do
        let guess ← guessGame
        let bit ← $ᵗ Bool
        return (bit == guess)] :=
      probOutput_bind_bind_swap ($ᵗ Bool) guessGame
        (fun bit guess ↦ pure (bit == guess)) true
    _ = Pr[= true | guessGame >>= fun _ ↦ ($ᵗ Bool)] := by
      refine probOutput_bind_congr' guessGame true fun guess ↦ ?_
      cases guess <;> simp
    _ = 1 / 2 := by simp

/-- For every fixed uniform public key, the ideal leftover-hash source makes the hidden bit
information-theoretically independent of the adversary's view. -/
theorem lhlIdeal_publicKey_probOutput_true
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode))
    (publicKey : PublicKey q n m) :
    Pr[= true | do
      let ciphertextCore ← $ᵗ Ciphertext q n
      maskingPostprocess errorSampler encode decode adversary
        (publicKey, ciphertextCore)] = 1 / 2 := by
  let preGame : ProbComp (Bool × (Bool × Bool × adversary.State)) := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages publicKey
    return (bit, messages)
  let shiftedCont := fun (pre : Bool × (Bool × Bool × adversary.State))
      (ciphertextCore : Ciphertext q n) ↦ do
    let message := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := shiftCiphertext (n := n) (encode message) ciphertextCore
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let unshiftedCont := fun (pre : Bool × (Bool × Bool × adversary.State))
      (ciphertextCore : Ciphertext q n) ↦ do
    let guess ← adversary.distinguish pre.2.2.2 ciphertextCore
    return (pre.1 == guess)
  calc
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ Ciphertext q n) >>= fun ciphertextCore ↦ shiftedCont pre ciphertextCore] := by
      simpa [preGame, shiftedCont, maskingPostprocess, shiftCiphertext, monad_norm] using
        (probOutput_bind_bind_swap ($ᵗ Ciphertext q n) preGame
          (fun ciphertextCore pre ↦ shiftedCont pre ciphertextCore) true)
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ Ciphertext q n) >>= fun ciphertextCore ↦ unshiftedCont pre ciphertextCore] := by
      refine probOutput_bind_congr' preGame true fun pre ↦ ?_
      let message := if pre.1 then pre.2.1 else pre.2.2.1
      simpa [shiftedCont, unshiftedCont, message] using
        (probOutput_bind_bijective_uniform_cross
          (Ciphertext q n)
          (shiftCiphertext (n := n) (encode message))
          (shiftCiphertext_bijective (n := n) (encode message))
          (fun ciphertextCore ↦ do
            let guess ← adversary.distinguish pre.2.2.2 ciphertextCore
            return (pre.1 == guess)) true)
    _ = Pr[= true | adversary.chooseMessages publicKey >>= fun messages ↦
          ($ᵗ Bool) >>= fun bit ↦
          ($ᵗ Ciphertext q n) >>= fun ciphertextCore ↦
            unshiftedCont (bit, messages) ciphertextCore] := by
      simpa [preGame, unshiftedCont, monad_norm] using
        (probOutput_bind_bind_swap ($ᵗ Bool) (adversary.chooseMessages publicKey)
          (fun bit messages ↦ do
            let ciphertextCore ← $ᵗ Ciphertext q n
            unshiftedCont (bit, messages) ciphertextCore) true)
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' messages, Pr[= messages | adversary.chooseMessages publicKey] * (1 / 2) := by
          refine tsum_congr fun messages : Bool × Bool × adversary.State ↦ ?_
          congr 1
          simpa [unshiftedCont, monad_norm] using
            (fairBit_eq_independentGuess
              (do
                let ciphertextCore ← $ᵗ Ciphertext q n
                adversary.distinguish messages.2.2 ciphertextCore))
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- The terminal leftover-hash game succeeds with probability exactly one half. -/
theorem lhlIdealGame_probOutput_true
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    Pr[= true | lhlIdealGame errorSampler encode decode adversary] = 1 / 2 := by
  have hgame :
      𝒟[lhlIdealGame errorSampler encode decode adversary] =
        𝒟[do
          let publicKey ← $ᵗ PublicKey q n m
          let ciphertextCore ← $ᵗ Ciphertext q n
          maskingPostprocess errorSampler encode decode adversary
            (publicKey, ciphertextCore)] := by
    unfold lhlIdealGame FormalProof4FHE.LeftoverHash.ideal
    rw [evalDist_bind, evalDist_uniformPublicKeyCiphertext_eq_components q n m,
      ← evalDist_bind]
    simp [monad_norm]
  rw [OracleComp.probOutput_congr rfl hgame, probOutput_bind_eq_tsum]
  simp_rw [lhlIdeal_publicKey_probOutput_true errorSampler encode decode adversary]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- Reordering the independent challenge randomness does not change the uniform-key game. -/
theorem uniformKeyGame_probOutput_eq_lhlRealGame
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode))
    (result : Bool) :
    Pr[= result | uniformKeyGame errorSampler encode decode adversary] =
      Pr[= result | lhlRealGame errorSampler encode decode adversary] := by
  rw [show lhlRealGame errorSampler encode decode adversary = (do
      let publicKey ← $ᵗ PublicKey q n m
      let bits ← $ᵗ (Fin m → Bool)
      maskingPostprocess errorSampler encode decode adversary
        (publicKey, subsetHash q n m publicKey bits)) by
    simp [lhlRealGame, FormalProof4FHE.LeftoverHash.hashed, monad_norm]]
  unfold uniformKeyGame keyFirstGame
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun publicKey : PublicKey q n m ↦ ?_
  rw [probOutput_uniformDistr_eq_uniformPublicKey q n m errorSampler publicKey]
  congr 1
  let preGame : ProbComp (Bool × (Bool × Bool × adversary.State)) := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages publicKey
    return (bit, messages)
  simpa [preGame, maskingPostprocess, FormalProof4FHE.LeftoverHash.hashed,
    scheme, sampleBinaryVector, subsetHash_eq_matrixHash, monad_norm] using
      (probOutput_bind_bind_swap preGame ($ᵗ (Fin m → Bool))
        (fun pre bits ↦ do
          let bit := pre.1
          let messages := pre.2
          let ciphertextCore := subsetHash q n m publicKey bits
          let message := if bit then messages.1 else messages.2.1
          let ciphertext :=
            (ciphertextCore.1, ciphertextCore.2 + encode message)
          let guess ← adversary.distinguish messages.2.2 ciphertext
          return (bit == guess)) result)

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

/-- The adversary-specific masking gap is exactly the Boolean gap obtained by post-processing the
two raw leftover-hash sources. -/
theorem maskingAdvantage_eq_lhlGames
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    maskingAdvantage errorSampler encode decode adversary =
      (lhlRealGame errorSampler encode decode adversary).boolDistAdvantage
        (lhlIdealGame errorSampler encode decode adversary) := by
  unfold maskingAdvantage ProbComp.boolDistAdvantage
  rw [uniformKeyGame_probOutput_eq_lhlRealGame errorSampler encode decode adversary true,
    idealGame_probOutput_true errorSampler encode decode adversary,
    lhlIdealGame_probOutput_true errorSampler encode decode adversary]

/-- Identical post-processing cannot increase the distance between the raw hash source and
uniform. -/
theorem lhlGames_tvDist_le_raw
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    tvDist
        (lhlRealGame errorSampler encode decode adversary)
        (lhlIdealGame errorSampler encode decode adversary) ≤
      tvDist
        (FormalProof4FHE.LeftoverHash.hashed (subsetHash q n m))
        (FormalProof4FHE.LeftoverHash.ideal
          (Seed := PublicKey q n m) (Output := Ciphertext q n)) := by
  simpa [lhlRealGame, lhlIdealGame, monad_norm] using
    (tvDist_bind_right_le
      (maskingPostprocess errorSampler encode decode adversary)
      (FormalProof4FHE.LeftoverHash.hashed (subsetHash q n m))
      (FormalProof4FHE.LeftoverHash.ideal
        (Seed := PublicKey q n m) (Output := Ciphertext q n)))

/-- The concrete statistical masking bound for Regev encryption. -/
theorem maskingAdvantage_le_leftover
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    maskingAdvantage errorSampler encode decode adversary ≤
      Real.sqrt
          (Fintype.card (Ciphertext q n) /
            Fintype.card (Fin m → Bool)) / 2 := by
  rw [maskingAdvantage_eq_lhlGames errorSampler encode decode adversary]
  unfold ProbComp.boolDistAdvantage
  calc
    _ ≤ tvDist
          (lhlRealGame errorSampler encode decode adversary)
          (lhlIdealGame errorSampler encode decode adversary) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist
          (FormalProof4FHE.LeftoverHash.hashed (subsetHash q n m))
          (FormalProof4FHE.LeftoverHash.ideal
            (Seed := PublicKey q n m) (Output := Ciphertext q n)) :=
      lhlGames_tvDist_le_raw errorSampler encode decode adversary
    _ ≤ _ := subsetHash_leftover q n m

/-- Arithmetic form of the masking bound: the ciphertext range has size `q^(n+1)` and the
binary randomness space has size `2^m`. -/
theorem maskingAdvantage_le_explicit
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    maskingAdvantage errorSampler encode decode adversary ≤
      Real.sqrt (((q : ℝ) ^ (n + 1)) / ((2 : ℝ) ^ m)) / 2 := by
  simpa [Ciphertext, Fintype.card_prod, Fintype.card_fun, Nat.cast_mul,
    Nat.cast_pow, pow_succ', mul_comm] using
      (maskingAdvantage_le_leftover errorSampler encode decode adversary)

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

/-- Fully concrete one-time Regev security theorem: decisional LWE plus the finite leftover-hash
bound `sqrt(q^(n+1) / 2^m) / 2`. -/
theorem oneTime_abs_signedAdvantage_le_lwe_add_leftover
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    |IND_CPA_OneTime_signedAdvantageReal
        (scheme q n m errorSampler encode decode) adversary| ≤
      LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) +
        Real.sqrt (((q : ℝ) ^ (n + 1)) / ((2 : ℝ) ^ m)) / 2 := by
  calc
    _ ≤ LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) +
        maskingAdvantage errorSampler encode decode adversary :=
      oneTime_abs_signedAdvantage_le_lwe_add_masking errorSampler encode decode adversary
    _ ≤ _ := add_le_add
      (le_refl (LearningWithErrors.advantage (lweProblem q n m errorSampler)
        (lweReduction errorSampler encode decode adversary)))
      (maskingAdvantage_le_explicit errorSampler encode decode adversary)

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

/-- Bias-advantage form with the concrete leftover-hash term. -/
theorem oneTime_boolBiasAdvantage_le_two_mul_lwe_add_leftover
    (adversary : IND_CPA_Adv (scheme q n m errorSampler encode decode)) :
    (IND_CPA_OneTime_Game_ProbComp
        (encAlg := scheme q n m errorSampler encode decode) adversary).boolBiasAdvantage ≤
      2 * (LearningWithErrors.advantage (lweProblem q n m errorSampler)
          (lweReduction errorSampler encode decode adversary) +
        Real.sqrt (((q : ℝ) ^ (n + 1)) / ((2 : ℝ) ^ m)) / 2) := by
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half]
  exact mul_le_mul_of_nonneg_left
    (oneTime_abs_signedAdvantage_le_lwe_add_leftover errorSampler encode decode adversary)
    (by norm_num)

end Games

end FormalProof4FHE.Regev
