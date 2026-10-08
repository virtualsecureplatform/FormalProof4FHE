/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveQuadraticParameters
import FormalProof4FHE.LWE.Regev
import FormalProof4FHE.TFHE.BootstrappingCorrectness

/-!
# Public encryption with the recursive same-key context

The retained public-key batch encrypts public bits by binary subset sums.
A Regev ciphertext is embedded as T=0,c=-u,b=v in the recursive format;
decryption under the same secret is v-sᵀu. The recursive hint context is
retained by key generation and the IND-CPA experiment. This supplies public
encryption, not a closed homomorphic multiplication or a reusable refresh.
-/

open Matrix OracleComp AsymmEncAlg
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.RecursivePublicKey

abbrev PublicKey (q n p : ℕ) := Regev.PublicKey q n p
abbrev Context (q n k : ℕ) := Fin k → RecursiveQuadratic.Ciphertext (ZMod q) n
abbrev HintRaw (q n k : ℕ) := Matrix (Fin n) (Fin k × Option (Fin n)) (ZMod q) ×
  ((Fin k × Option (Fin n)) → ZMod q)

noncomputable local instance (q n k : ℕ) [NeZero q] :
    SampleableType ((Fin k × Option (Fin n)) → ZMod q) := instSampleableTypePiFintype
noncomputable local instance (q n k : ℕ) [NeZero q] :
    SampleableType (Matrix (Fin n) (Fin k × Option (Fin n)) (ZMod q)) := instSampleableTypeFinFunc
noncomputable local instance (q n p k : ℕ) [NeZero q] :
    SampleableType (RecursiveQuadratic.Column n p k → ZMod q) := instSampleableTypePiFintype
noncomputable local instance (q n p k : ℕ) [NeZero q] :
    SampleableType (Matrix (Fin n) (RecursiveQuadratic.Column n p k) (ZMod q)) := instSampleableTypeFinFunc

def embedLinear {q n : ℕ} (ciphertext : Regev.Ciphertext q n) :
    RecursiveQuadratic.Ciphertext (ZMod q) n := (0, -ciphertext.1, ciphertext.2)

theorem decrypt_embedLinear {q n : ℕ} (secret : Fin n → ZMod q)
    (ciphertext : Regev.Ciphertext q n) :
    RecursiveQuadratic.decrypt secret (embedLinear ciphertext) =
      ciphertext.2 - dotProduct secret ciphertext.1 := by
  simp only [RecursiveQuadratic.decrypt, embedLinear, neg_dotProduct, vecMul_zero,
    zero_dotProduct, sub_zero]
  rw [dotProduct_comm]
  ring

def rawEncrypt {q n p : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (publicKey : PublicKey q n p) (bit : Bool) : ProbComp (Regev.Ciphertext q n) := do
  let randomness ← Regev.sampleBinaryVector q p
  pure (publicKey.1.mulVec randomness, dotProduct publicKey.2 randomness + encode bit)

def encrypt {q n p : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (publicKey : PublicKey q n p) (bit : Bool) :
    ProbComp (RecursiveQuadratic.Ciphertext (ZMod q) n) :=
  embedLinear <$> rawEncrypt encode publicKey bit

theorem rawEncrypt_eq_regev {q n p : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (decode : ZMod q → Option Bool) (errors : ProbComp (ZMod q))
    (publicKey : PublicKey q n p) (bit : Bool) :
    rawEncrypt encode publicKey bit = (Regev.scheme q n p errors encode decode).encrypt publicKey bit := rfl

def encryptWithCoins {q n p : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (publicKey : PublicKey q n p) (bits : Fin p → Bool) (bit : Bool) :
    RecursiveQuadratic.Ciphertext (ZMod q) n :=
  embedLinear (Regev.shiftCiphertext (encode bit) (Regev.subsetHash q n p publicKey bits))

theorem encrypt_eq_uniformCoins {q n p : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (publicKey : PublicKey q n p) (bit : Bool) :
    encrypt encode publicKey bit =
      (fun bits ↦ encryptWithCoins encode publicKey bits bit) <$> ($ᵗ (Fin p → Bool)) := by
  simp [encrypt, rawEncrypt, Regev.sampleBinaryVector, encryptWithCoins,
    Regev.shiftCiphertext, Regev.subsetHash_eq_matrixHash, monad_norm]

theorem decrypt_fresh_publicEncryption {q n p : ℕ} [NeZero q]
    (encode : Bool → ZMod q) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (Fin p) (ZMod q)) (errors : Fin p → ZMod q)
    (bits : Fin p → Bool) (bit : Bool) :
    RecursiveQuadratic.decrypt secret
      (encryptWithCoins encode (challenge, vecMul secret challenge + errors) bits bit) =
        encode bit + dotProduct errors (fun index ↦ if bits index then 1 else 0) := by
  rw [encryptWithCoins, decrypt_embedLinear, Regev.subsetHash_eq_matrixHash]
  simp only [Regev.shiftCiphertext, add_dotProduct, dotProduct_mulVec]
  ring

theorem publicEncryption_error_bound {q n p : ℕ} [NeZero q]
    (encode : Bool → ZMod q) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (Fin p) (ZMod q)) (errors : Fin p → ZMod q)
    (bits : Fin p → Bool) (bit : Bool) (bound : ℕ)
    (herrors : ∀ index, (LatticeCrypto.centeredRepr (errors index)).natAbs ≤ bound) :
    (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt secret
        (encryptWithCoins encode (challenge, vecMul secret challenge + errors) bits bit) -
          encode bit)).natAbs ≤ p * bound := by
  rw [decrypt_fresh_publicEncryption, add_sub_cancel_left]
  unfold dotProduct
  calc
    _ ≤ ∑ index, (LatticeCrypto.centeredRepr
        (errors index * if bits index then 1 else 0)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
    _ ≤ ∑ _index : Fin p, bound := by
      apply Finset.sum_le_sum
      intro index _
      cases bits index <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, mul_one]
      · simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
      · exact herrors index
    _ = _ := by simp

def bitEncode {q : ℕ} [NeZero q] (oneCode : ZMod q) (bit : Bool) : ZMod q :=
  if bit then oneCode else 0

def decode {q n : ℕ} [NeZero q] (oneCode : ZMod q)
    (secret : Fin n → ZMod q) (ciphertext : RecursiveQuadratic.Ciphertext (ZMod q) n) : Bool :=
  TFHE.BootstrappingCorrectness.decodeNearest 0 oneCode (RecursiveQuadratic.decrypt secret ciphertext)

theorem decode_publicEncryption {q n p : ℕ} [NeZero q]
    (oneCode : ZMod q) (secret : Fin n → ZMod q)
    (challenge : Matrix (Fin n) (Fin p) (ZMod q)) (errors : Fin p → ZMod q)
    (bits : Fin p → Bool) (bit : Bool) (bound : ℕ)
    (herrors : ∀ index, (LatticeCrypto.centeredRepr (errors index)).natAbs ≤ bound)
    (hmargin : 2 * (p * bound) < TFHE.BootstrappingCorrectness.centeredDistance 0 oneCode) :
    decode oneCode secret
      (encryptWithCoins (bitEncode oneCode) (challenge, vecMul secret challenge + errors) bits bit) = bit := by
  have hnoise := publicEncryption_error_bound (bitEncode oneCode) secret challenge errors bits bit bound herrors
  cases bit with
  | false =>
    exact TFHE.BootstrappingCorrectness.decodeNearest_eq_false_of_distance_le _ _ _ _ hmargin
      (by simpa only [TFHE.BootstrappingCorrectness.centeredDistance, bitEncode, Bool.false_eq_true,
        ↓reduceIte] using hnoise)
  | true =>
    exact TFHE.BootstrappingCorrectness.decodeNearest_eq_true_of_distance_le _ _ _ _ hmargin
      (by simpa only [TFHE.BootstrappingCorrectness.centeredDistance, bitEncode, ↓reduceIte] using hnoise)

/-- Split every raw tape coordinate into public-key rows and recursive-hint rows. -/
def splitRaw {q n p k : ℕ} :
    RecursiveQuadratic.Raw (ZMod q) n p k ≃ PublicKey q n p × HintRaw q n k where
  toFun raw :=
    ((fun row column ↦ raw.1 row (.inl column), fun column ↦ raw.2 (.inl column)),
      (fun row column ↦ raw.1 row (.inr column), fun column ↦ raw.2 (.inr column)))
  invFun pair :=
    (fun row column ↦ Sum.elim (pair.1.1 row) (pair.2.1 row) column,
      Sum.elim pair.1.2 pair.2.2)
  left_inv raw := by
    apply Prod.ext
    · funext row column
      cases column <;> rfl
    · funext column
      cases column <;> rfl
  right_inv pair := by rfl

def hintContext {q n k : ℕ} (raw : HintRaw q n k) : Context q n k :=
  fun index ↦ (fun row column ↦ raw.1 row (index, some column),
    (fun row ↦ raw.2 (index, some row)), raw.2 (index, none))

theorem project_splitRaw {q n p k : ℕ} (raw : RecursiveQuadratic.Raw (ZMod q) n p k) :
    RecursiveQuadratic.project raw = ((splitRaw raw).1, hintContext (splitRaw raw).2) := rfl

noncomputable def idealContext (q n k : ℕ) [NeZero q] : ProbComp (Context q n k) :=
  hintContext <$> ($ᵗ HintRaw q n k)

/-- Independence is asserted only after the justified whole-view replacement. -/
theorem idealView_evalDist (q n p k : ℕ) [NeZero q] :
    𝒟[RecursiveQuadratic.idealView (R := ZMod q) (n := n) (p := p) (k := k)] =
    𝒟[do
      let publicKey ← $ᵗ PublicKey q n p
      let context ← idealContext q n k
      pure (publicKey, context)] := by
  let finish := fun pair : PublicKey q n p × HintRaw q n k ↦ (pair.1, hintContext pair.2)
  have hsplit := evalDist_map_bijective_uniform_cross
    (α := RecursiveQuadratic.Raw (ZMod q) n p k) (β := PublicKey q n p × HintRaw q n k)
    splitRaw splitRaw.bijective
  have hm := evalDist_map_eq_of_evalDist_eq hsplit finish
  have hpair := FiniteProduct.evalDist_independent_uniform_product
    (first := PublicKey q n p) (second := HintRaw q n k)
  have hp := evalDist_map_eq_of_evalDist_eq hpair finish
  simpa only [RecursiveQuadratic.idealView, idealContext, finish, Functor.map_map,
    Function.comp_def, ← project_splitRaw, monad_norm] using hm.trans hp.symm

/-- Honest key generation retains the one underlying secret, for decryption only. -/
noncomputable def keygen {q n p k samples : ℕ} [NeZero q]
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    ProbComp (RecursiveQuadratic.View (ZMod q) n p k × (Fin n → ZMod q)) := do
  let secret ← secretSampler
  let challenge ← $ᵗ Matrix (Fin n) (RecursiveQuadratic.Column n p k) (ZMod q)
  let errors ← ProbComp.sampleIID samples errorSampler
  pure (RecursiveQuadratic.fresh polynomial secret challenge (fun column ↦ errors (columns column)), secret)

theorem keygen_public_evalDist {q n p k samples : ℕ} [NeZero q]
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    𝒟[Prod.fst <$> keygen columns polynomial secretSampler errorSampler] =
      𝒟[RecursiveQuadratic.freshView columns polynomial secretSampler id errorSampler] := by
  simp [keygen, RecursiveQuadratic.freshView, map_bind]

noncomputable def scheme {q n p k samples : ℕ} [NeZero q] (oneCode : ZMod q)
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q)) :
    AsymmEncAlg ProbComp Bool (RecursiveQuadratic.View (ZMod q) n p k)
      (Fin n → ZMod q) (RecursiveQuadratic.Ciphertext (ZMod q) n) where
  keygen := keygen columns polynomial secretSampler errorSampler
  encrypt := fun view bit ↦ encrypt (bitEncode oneCode) view.1 bit
  decrypt := fun secret ciphertext ↦ pure (some (decode oneCode secret ciphertext))

structure Adversary (q n p k : ℕ) where
  State : Type
  chooseMessages : RecursiveQuadratic.View (ZMod q) n p k → ProbComp (Bool × Bool × State)
  distinguish : State → RecursiveQuadratic.Ciphertext (ZMod q) n → ProbComp Bool

def gameGivenView {q n p k : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (adversary : Adversary q n p k) (view : RecursiveQuadratic.View (ZMod q) n p k) :
    ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages view
  let ciphertext ← encrypt encode view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

def game {q n p k : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (viewSampler : ProbComp (RecursiveQuadratic.View (ZMod q) n p k))
    (adversary : Adversary q n p k) : ProbComp Bool := viewSampler >>= gameGivenView encode adversary

/-- Only the ideal context is sampled independently inside this masking adapter. -/
def regevAdversary {q n p k : ℕ} [NeZero q] (encode : Bool → ZMod q)
    (contextSampler : ProbComp (Context q n k)) (adversary : Adversary q n p k) :
    IND_CPA_Adv (Regev.scheme q n p (pure 0) encode (fun _ ↦ none)) where
  State := adversary.State
  chooseMessages := fun publicKey ↦ do
    let context ← contextSampler
    adversary.chooseMessages (publicKey, context)
  distinguish := fun state ciphertext ↦ adversary.distinguish state (embedLinear ciphertext)

theorem uniform_context_game_evalDist {q n p k : ℕ} [NeZero q]
    (encode : Bool → ZMod q) (contextSampler : ProbComp (Context q n k))
    (adversary : Adversary q n p k) :
    𝒟[game encode (do
      let publicKey ← $ᵗ PublicKey q n p
      let context ← contextSampler
      pure (publicKey, context)) adversary] =
    𝒟[Regev.uniformKeyGame (pure 0) encode (fun _ ↦ none)
      (regevAdversary encode contextSampler adversary)] := by
  have hpk : 𝒟[LearningWithErrors.uniformDistr (Regev.lweProblem q n p (pure 0))] =
      𝒟[$ᵗ PublicKey q n p] :=
    evalDist_ext (Regev.probOutput_uniformDistr_eq_uniformPublicKey q n p (pure 0))
  let next := fun (publicKey : PublicKey q n p) (context : Context q n k) (bit : Bool) ↦ do
    let messages ← adversary.chooseMessages (publicKey, context)
    let ciphertext ← rawEncrypt encode publicKey (if bit then messages.1 else messages.2.1)
    let guess ← adversary.distinguish messages.2.2 (embedLinear ciphertext)
    pure (bit == guess)
  have hleft : game encode (do
      let publicKey ← $ᵗ PublicKey q n p
      let context ← contextSampler
      pure (publicKey, context)) adversary =
      (($ᵗ PublicKey q n p) >>= fun publicKey ↦ contextSampler >>= fun context ↦
        ($ᵗ Bool) >>= next publicKey context) := by
    simp [game, gameGivenView, encrypt, next, monad_norm]
  have hright : 𝒟[Regev.uniformKeyGame (pure 0) encode (fun _ ↦ none)
      (regevAdversary encode contextSampler adversary)] =
      𝒟[($ᵗ PublicKey q n p) >>= fun publicKey ↦ ($ᵗ Bool) >>= fun bit ↦
        contextSampler >>= fun context ↦ next publicKey context bit] := by
    unfold Regev.uniformKeyGame Regev.keyFirstGame
    rw [evalDist_bind, hpk, ← evalDist_bind]
    simp [regevAdversary, Regev.scheme, rawEncrypt, next, monad_norm]
  rw [hleft, hright]
  refine evalDist_bind_congr' ($ᵗ PublicKey q n p) fun publicKey ↦ ?_
  exact evalDist_bind_bind_swap contextSampler ($ᵗ Bool) (next publicKey)

theorem ideal_game_abs_advantage_le {q n p k : ℕ} [NeZero q]
    (encode : Bool → ZMod q) (adversary : Adversary q n p k) :
    |Pr[= true | game encode
      (RecursiveQuadratic.idealView (R := ZMod q) (n := n) (p := p) (k := k)) adversary].toReal - 1 / 2| ≤
        Real.sqrt ((q : ℝ) ^ (n + 1) / (2 : ℝ) ^ p) / 2 := by
  have hview := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (idealView_evalDist q n p k) (gameGivenView encode adversary)
  have hgame := hview.trans (uniform_context_game_evalDist encode (idealContext q n k) adversary)
  have hmask := Regev.maskingAdvantage_le_explicit (pure 0) encode (fun _ ↦ none)
    (regevAdversary encode (idealContext q n k) adversary)
  rw [← Regev.abs_signedAdvantage_uniformKey_eq_maskingAdvantage] at hmask
  unfold Regev.signedAdvantage at hmask
  simpa only [game, probOutput_congr rfl hgame] using hmask

/-- The published hint context is included in the ordinary-LWE reduction observer. -/
theorem sampled_game_abs_advantage_le {p k samples : ℕ} (parameter : ℕ)
    (columns : RecursiveQuadratic.Column (RecursiveQuadraticParameters.binaryDimension parameter * 1)
      p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (RecursiveQuadraticParameters.modulus parameter))
      (RecursiveQuadraticParameters.binaryDimension parameter * 1) k)
    (encode : Bool → ZMod (RecursiveQuadraticParameters.modulus parameter))
    (adversary : Adversary (RecursiveQuadraticParameters.modulus parameter)
      (RecursiveQuadraticParameters.binaryDimension parameter * 1) p k) :
    |Pr[= true | game encode
      (RecursiveQuadratic.freshView columns polynomial
        ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter))
        (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)))
        (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
          (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)))
        adversary].toReal - 1 / 2| ≤
      RecursiveQuadraticParameters.ordinaryReductionLoss parameter columns polynomial
        (gameGivenView encode adversary) +
      RecursiveQuadraticParameters.implementationLoss samples parameter +
      Real.sqrt ((RecursiveQuadraticParameters.modulus parameter : ℝ) ^
        (RecursiveQuadraticParameters.binaryDimension parameter * 1 + 1) / (2 : ℝ) ^ p) / 2 := by
  have hview := RecursiveQuadraticParameters.sampled_advantage_le_narrowLWE parameter columns polynomial
    (gameGivenView encode adversary)
  have hmask := ideal_game_abs_advantage_le encode adversary
  unfold ProbComp.boolDistAdvantage at hview
  have htriangle := abs_sub_le
    (Pr[= true | game encode
      (RecursiveQuadratic.freshView columns polynomial
        ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (RecursiveQuadraticParameters.binaryDimension parameter))
        (FormalProof4FHE.BlockBinary.expand (ZMod (RecursiveQuadraticParameters.modulus parameter)))
        (UniformInterval.sample (RecursiveQuadraticParameters.modulus parameter)
          (RecursiveQuadraticParameters.radius parameter) (RecursiveQuadraticParameters.retries parameter)))
        adversary]).toReal
    (Pr[= true | game encode
      (RecursiveQuadratic.idealView (R := ZMod (RecursiveQuadraticParameters.modulus parameter))
        (n := RecursiveQuadraticParameters.binaryDimension parameter * 1) (p := p) (k := k)) adversary]).toReal
    (1 / 2 : ℝ)
  exact htriangle.trans (add_le_add hview hmask)

/-- Adapter to the standard VCVio experiment; the adversary receives the full view. -/
def fromINDCPA {q n p k samples : ℕ} [NeZero q] (oneCode : ZMod q)
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme oneCode columns polynomial secretSampler errorSampler)) :
    Adversary q n p k where
  State := adversary.State
  chooseMessages := adversary.chooseMessages
  distinguish := adversary.distinguish

theorem oneTime_game_evalDist {q n p k samples : ℕ} [NeZero q] (oneCode : ZMod q)
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp (Fin n → ZMod q)) (errorSampler : ProbComp (ZMod q))
    (adversary : IND_CPA_Adv (scheme oneCode columns polynomial secretSampler errorSampler)) :
    𝒟[IND_CPA_OneTime_Game_ProbComp adversary] =
      𝒟[game (bitEncode oneCode)
        (RecursiveQuadratic.freshView columns polynomial secretSampler id errorSampler)
        (fromINDCPA oneCode columns polynomial secretSampler errorSampler adversary)] := by
  let observe := gameGivenView (bitEncode oneCode)
    (fromINDCPA oneCode columns polynomial secretSampler errorSampler adversary)
  have hswap := evalDist_bind_bind_swap ($ᵗ Bool)
    (keygen columns polynomial secretSampler errorSampler)
    (fun bit pair ↦ do
      let messages ← adversary.chooseMessages pair.1
      let ciphertext ← encrypt (bitEncode oneCode) pair.1.1
        (if bit then messages.1 else messages.2.1)
      let guess ← adversary.distinguish messages.2.2 ciphertext
      pure (bit == guess))
  have hforget := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (keygen_public_evalDist columns polynomial secretSampler errorSampler) observe
  simpa [IND_CPA_OneTime_Game_ProbComp, scheme, game, observe, gameGivenView,
    fromINDCPA, monad_norm] using hswap.trans (by
      simpa [bind_map_left, observe, gameGivenView, fromINDCPA, monad_norm] using hforget)

/-- Sampling a representation of one secret does not add a key to the scheme. -/
theorem freshView_mapped_secret {q n p k samples : ℕ} [NeZero q] {Key : Type}
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp Key) (expand : Key → Fin n → ZMod q)
    (errorSampler : ProbComp (ZMod q)) :
    RecursiveQuadratic.freshView columns polynomial (expand <$> secretSampler) id errorSampler =
      RecursiveQuadratic.freshView columns polynomial secretSampler expand errorSampler := by
  simp [RecursiveQuadratic.freshView, monad_norm]

end FormalProof4FHE.LWE.RecursivePublicKey
