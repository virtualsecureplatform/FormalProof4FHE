/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWSampling
import FormalProof4FHE.LWE.Regev
import FormalProof4FHE.Probability.SeededProductTV
import FormalProof4FHE.Probability.DiscreteGaussianTail

/-!
# GSW encryption masking with the complete bootstrap context retained

Ciphertext columns reuse one public key and use independent binary selectors.
The uniform-public-key branch is statistically hiding even when an arbitrary
bootstrap context is retained and messages are chosen after seeing both public
tables. The final bound retains the real joint-view key-replacement advantage.
It does not assume that advantage is small, or reduce it to ordinary LWE.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWMasking

open GSWGadget GSWAccumulator GSWPublicKey

abbrev Column (Q dimension : ℕ) := Fin (dimension + 1) → ZMod Q
abbrev Table (Q dimension samples : ℕ) := Fin samples → Column Q dimension
abbrev Coins (samples columns : ℕ) := Fin columns → Fin samples → Bool
abbrev Core (Q dimension columns : ℕ) := Fin columns → Column Q dimension

/-- Public-key columns as the retained leftover-hash seed. -/
def tableOfPublicKey {Q dimension samples : ℕ} (key : PublicKey Q dimension samples) :
    Table Q dimension samples := fun column row ↦ publicKeyView key row column

def storeTable {Q dimension samples : ℕ} (table : Table Q dimension samples) :
    PublicKey Q dimension samples := storePublicKey fun row column ↦ table column row

@[simp] theorem tableOfPublicKey_storeTable {Q dimension samples : ℕ}
    (table : Table Q dimension samples) : tableOfPublicKey (storeTable table) = table := by
  ext column row
  simp [tableOfPublicKey, storeTable]

@[simp] theorem storeTable_tableOfPublicKey {Q dimension samples : ℕ}
    (key : PublicKey Q dimension samples) : storeTable (tableOfPublicKey key) = key := by
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro column hcolumn
  simp [storeTable, tableOfPublicKey, storePublicKey, publicKeyView, Vector.get]

def subsetHash {Q dimension samples : ℕ} [NeZero Q]
    (table : Table Q dimension samples) (bits : Fin samples → Bool) : Column Q dimension :=
  LeftoverHash.binarySubsetSum table bits

theorem subsetHash_isTwoUniversal {Q dimension samples : ℕ} [NeZero Q] :
    LeftoverHash.IsTwoUniversal (Table Q dimension samples) (Fin samples → Bool)
      (Column Q dimension) (subsetHash (Q := Q) (dimension := dimension) (samples := samples)) :=
  LeftoverHash.binarySubsetSum_isTwoUniversal

/-- Functional selectors are materialized in the layout used by public encryption. -/
def storeCoins {samples columns : ℕ} (coins : Coins samples columns) : SelectorCoins samples columns :=
  Vector.ofFn fun sample ↦ Vector.ofFn fun column ↦ coins column sample

def hashCore {Q dimension samples columns : ℕ} [NeZero Q]
    (table : Table Q dimension samples) (coins : Coins samples columns) : Core Q dimension columns :=
  fun column ↦ subsetHash table (coins column)

/-- Exact algebraic bridge, including all matrix columns and the bit-gadget offset. -/
theorem encryptMatrix_eq_hashCore {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (table : Table Q dimension samples)
    (coins : Coins samples ((dimension + 1) * params.levels)) (bit : Bool) :
    encryptMatrix params (storeTable table) (storeCoins coins) bit =
      Matrix.of (fun row column ↦ hashCore table coins column row) +
        (bitMessage bit : ZMod Q) • gadget params (dimension + 1) := by
  ext row column
  simp only [encryptMatrix, storeTable, publicKeyView_storePublicKey, Matrix.add_apply]
  congr 1
  simp only [Matrix.mul_apply, selectors, storeCoins, Vector.get_ofFn, hashCore, subsetHash,
    LeftoverHash.binarySubsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro sample _
  cases coins column sample <;> simp [GSWGadget.bitMessage]

def ciphertextFromCore {Q dimension : ℕ} [NeZero Q] (params : Parameters Q)
    (core : Core Q dimension ((dimension + 1) * params.levels)) (bit : Bool) :
    StoredCiphertext params (dimension + 1) :=
  storeCiphertext params (Matrix.of (fun row column ↦ core column row) +
    (bitMessage bit : ZMod Q) • gadget params (dimension + 1))

/-- This is exactly the operational public encryption on the corresponding selector tape. -/
theorem encryptStored_eq_ciphertextFromCore {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (table : Table Q dimension samples)
    (coins : Coins samples ((dimension + 1) * params.levels)) (bit : Bool) :
    encryptStored params (storeTable table) (storeCoins coins) bit =
      ciphertextFromCore params (hashCore table coins) bit := by
  simp only [encryptStored, encryptMatrix_eq_hashCore, ciphertextFromCore]

def encrypt {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (table : Table Q dimension samples) (bit : Bool) : ProbComp (StoredCiphertext params (dimension + 1)) :=
  (fun coins ↦ encryptStored params (storeTable table) (storeCoins coins) bit) <$>
    ($ᵗ Coins samples ((dimension + 1) * params.levels))

/-- Reindexing the actual single-input selection tape uses no secret-dependent transformation. -/
def singleInputCoinsEquiv (samples columns : ℕ) :
    (Fin 1 → Fin samples → Fin columns → Bool) ≃ Coins samples columns where
  toFun coins := fun column sample ↦ coins 0 sample column
  invFun coins := fun _ sample column ↦ coins column sample
  left_inv coins := by
    ext index sample column
    have hi : index = 0 := Fin.eq_zero index
    subst index
    rfl
  right_inv coins := by rfl

/-- The masking sampler is the actual `encryptInputs` sampler projected to its single input. -/
theorem evalDist_encrypt_eq_encryptInputs_one {Q dimension samples : ℕ} [NeZero Q]
    (params : Parameters Q) (table : Table Q dimension samples) (bit : Bool) :
    𝒟[encrypt params table bit] =
      𝒟[(fun ciphertexts ↦ ciphertexts.get 0) <$>
        GSWSampling.encryptInputs params (storeTable table) (Vector.replicate 1 bit)] := by
  let coinsEquiv := singleInputCoinsEquiv samples ((dimension + 1) * params.levels)
  have huniform := evalDist_map_bijective_uniform_cross
    (Fin 1 → Fin samples → Fin ((dimension + 1) * params.levels) → Bool)
    coinsEquiv coinsEquiv.bijective
  unfold encrypt
  rw [evalDist_map]
  rw [← huniform]
  simp [GSWSampling.encryptInputs, GSWSampling.sampleInputCoins,
    encryptInputsStored, storeCoins, coinsEquiv, singleInputCoinsEquiv, monad_norm]

/-- One leftover-hash error per column, under the one public seed. -/
theorem hashCore_joint_masking {Q dimension samples columns : ℕ} [NeZero Q] :
    tvDist
        (do
          let table ← $ᵗ Table Q dimension samples
          let coins ← $ᵗ Coins samples columns
          pure (table, hashCore table coins))
        (SeededProductTV.joint ($ᵗ Table Q dimension samples) fun _ ↦ ($ᵗ Core Q dimension columns)) ≤
      columns * (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  unfold hashCore
  have h := SeededProductTV.leftover_hash_columns
    (subsetHash (Q := Q) (dimension := dimension) (samples := samples))
    subsetHash_isTwoUniversal columns
  rw [tvDist, SeededProductTV.evalDist_hashedColumns_eq_uniform_tape,
    SeededProductTV.evalDist_idealColumns_eq_uniform_tape] at h
  simpa only [tvDist, Core, Column, Coins, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat] using h

/-- A public adversary sees both the stored public key and the complete bootstrap context. -/
structure Adversary {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q) (Context : Type) where
  State : Type
  chooseMessages : PublicKey Q dimension samples × Context → ProbComp (Bool × Bool × State)
  distinguish : State → StoredCiphertext params (dimension + 1) → ProbComp Bool

variable {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q) {Context : Type}

/-- The ordinary IND-CPA winning game, with its whole public-key/context sampler explicit. -/
def game (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) : ProbComp Bool := do
  let view ← keySampler
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (storeTable view.1, view.2)
  let ciphertext ← encrypt params view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

/-- Replace only the public-key table; retain the exact marginal law of the real context. -/
def uniformView (keySampler : ProbComp (Table Q dimension samples × Context)) :
    ProbComp (Table Q dimension samples × Context) := do
  let oldView ← keySampler
  let table ← $ᵗ Table Q dimension samples
  pure (table, oldView.2)

/-- Reordered IND-CPA continuation for a retained context and raw hash core. -/
def maskingPostprocess (adversary : Adversary (dimension := dimension) (samples := samples) params Context) (context : Context)
    (sample : Table Q dimension samples × Core Q dimension ((dimension + 1) * params.levels)) :
    ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (storeTable sample.1, context)
  let message := if bit then messages.1 else messages.2.1
  let guess ← adversary.distinguish messages.2.2 (ciphertextFromCore params sample.2 message)
  pure (bit == guess)

/-- The gadget offset is an additive translation of the full column tape. -/
def gadgetOffset (bit : Bool) : Core Q dimension ((dimension + 1) * params.levels) :=
  fun column row ↦ ((bitMessage bit : ZMod Q) • gadget params (dimension + 1)) row column

theorem ciphertextFromCore_eq_shift (core : Core Q dimension ((dimension + 1) * params.levels))
    (bit : Bool) :
    ciphertextFromCore params core bit =
      ciphertextFromCore params (core + gadgetOffset params bit) false := by
  unfold ciphertextFromCore
  congr 1
  ext row column
  cases bit <;> simp [gadgetOffset, GSWGadget.bitMessage]

/-- The ideal full-matrix core hides the bit for every fixed public view. -/
theorem ideal_fixed_view_probOutput_true (adversary : Adversary (dimension := dimension) (samples := samples) params Context)
    (table : Table Q dimension samples) (context : Context) :
    Pr[= true | do
      let core ← $ᵗ Core Q dimension ((dimension + 1) * params.levels)
      maskingPostprocess params adversary context (table, core)] = 1 / 2 := by
  let preGame : ProbComp (Bool × (Bool × Bool × adversary.State)) := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages (storeTable table, context)
    pure (bit, messages)
  let shifted := fun (pre : Bool × (Bool × Bool × adversary.State))
      (core : Core Q dimension ((dimension + 1) * params.levels)) ↦ do
    let message := if pre.1 then pre.2.1 else pre.2.2.1
    let guess ← adversary.distinguish pre.2.2.2 (ciphertextFromCore params core message)
    pure (pre.1 == guess)
  let unshifted := fun (pre : Bool × (Bool × Bool × adversary.State))
      (core : Core Q dimension ((dimension + 1) * params.levels)) ↦ do
    let guess ← adversary.distinguish pre.2.2.2 (ciphertextFromCore params core false)
    pure (pre.1 == guess)
  calc
    _ = Pr[= true | preGame >>= fun pre ↦
        ($ᵗ Core Q dimension ((dimension + 1) * params.levels)) >>= shifted pre] := by
      simpa [preGame, shifted, maskingPostprocess, monad_norm] using
        (probOutput_bind_bind_swap
          ($ᵗ Core Q dimension ((dimension + 1) * params.levels)) preGame
          (fun core pre ↦ shifted pre core) true)
    _ = Pr[= true | preGame >>= fun pre ↦
        ($ᵗ Core Q dimension ((dimension + 1) * params.levels)) >>= unshifted pre] := by
      refine probOutput_bind_congr' preGame true fun pre ↦ ?_
      let message := if pre.1 then pre.2.1 else pre.2.2.1
      have h := evalDist_bind_bijective_add_right_uniform
        (α := Core Q dimension ((dimension + 1) * params.levels))
        id Function.bijective_id (gadgetOffset params message) (unshifted pre)
      calc
        _ = Pr[= true | do
            let core ← $ᵗ Core Q dimension ((dimension + 1) * params.levels)
            unshifted pre (core + gadgetOffset params message)] := by
          refine probOutput_bind_congr'
            ($ᵗ Core Q dimension ((dimension + 1) * params.levels)) true fun core ↦ ?_
          simp only [shifted, unshifted]
          rw [ciphertextFromCore_eq_shift params core message]
        _ = _ := OracleComp.probOutput_congr rfl h
    _ = Pr[= true | adversary.chooseMessages (storeTable table, context) >>= fun messages ↦
        ($ᵗ Bool) >>= fun bit ↦
        ($ᵗ Core Q dimension ((dimension + 1) * params.levels)) >>= fun core ↦
          unshifted (bit, messages) core] := by
      simpa [preGame, unshifted, monad_norm] using
        (probOutput_bind_bind_swap ($ᵗ Bool)
          (adversary.chooseMessages (storeTable table, context))
          (fun bit messages ↦ do
            let core ← $ᵗ Core Q dimension ((dimension + 1) * params.levels)
            unshifted (bit, messages) core) true)
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' messages, Pr[= messages | adversary.chooseMessages (storeTable table, context)] * (1 / 2) := by
          refine tsum_congr fun messages : Bool × Bool × adversary.State ↦ ?_
          congr 1
          simpa [unshifted, monad_norm] using Regev.fairBit_eq_independentGuess
            (do
              let core ← $ᵗ Core Q dimension ((dimension + 1) * params.levels)
              adversary.distinguish messages.2.2 (ciphertextFromCore params core false))
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

def hashGame (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) : ProbComp Bool := do
  let oldView ← keySampler
  let table ← $ᵗ Table Q dimension samples
  let coins ← $ᵗ Coins samples ((dimension + 1) * params.levels)
  maskingPostprocess params adversary oldView.2 (table, hashCore table coins)

def idealGame (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) : ProbComp Bool := do
  let oldView ← keySampler
  let sample ← SeededProductTV.joint ($ᵗ Table Q dimension samples)
    fun _ ↦ ($ᵗ Core Q dimension ((dimension + 1) * params.levels))
  maskingPostprocess params adversary oldView.2 sample

/-- The real bootstrap context is drawn once, before the independent public-key hybrid. -/
theorem uniform_game_probOutput_eq_hashGame
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) (result : Bool) :
    Pr[= result | game params (uniformView keySampler) adversary] =
      Pr[= result | hashGame params keySampler adversary] := by
  unfold game uniformView hashGame
  simp only [bind_assoc, pure_bind]
  refine probOutput_bind_congr' keySampler result fun oldView ↦ ?_
  refine probOutput_bind_congr' ($ᵗ Table Q dimension samples) result fun table ↦ ?_
  let preGame : ProbComp (Bool × (Bool × Bool × adversary.State)) := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages (storeTable table, oldView.2)
    pure (bit, messages)
  simpa [preGame, encrypt, maskingPostprocess, encryptStored_eq_ciphertextFromCore,
    monad_norm] using
    (probOutput_bind_bind_swap preGame
      ($ᵗ Coins samples ((dimension + 1) * params.levels))
      (fun pre coins ↦ do
        let guess ← adversary.distinguish pre.2.2.2
          (ciphertextFromCore params (hashCore table coins)
            (if pre.1 then pre.2.1 else pre.2.2.1))
        pure (pre.1 == guess)) result)

theorem idealGame_probOutput_true (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    Pr[= true | idealGame params keySampler adversary] = 1 / 2 := by
  simp only [idealGame, SeededProductTV.joint, bind_assoc, pure_bind]
  rw [probOutput_bind_eq_tsum]
  have hcontext (oldView : Table Q dimension samples × Context) :
      Pr[= true | do
        let table ← $ᵗ Table Q dimension samples
        let core ← $ᵗ Core Q dimension ((dimension + 1) * params.levels)
        maskingPostprocess params adversary oldView.2 (table, core)] = 1 / 2 := by
    rw [probOutput_bind_eq_tsum]
    simp_rw [ideal_fixed_view_probOutput_true]
    rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
  simp_rw [hcontext]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- A retained context of any size adds no statistical masking loss. -/
theorem hashGame_tvDist_idealGame_le
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    tvDist (hashGame params keySampler adversary) (idealGame params keySampler adversary) ≤
      ((dimension + 1) * params.levels) *
          (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  unfold hashGame idealGame
  apply tvDist_bind_left_le_const'
  intro oldView
  have h := tvDist_bind_right_le (maskingPostprocess params adversary oldView.2)
    (do
      let table ← $ᵗ Table Q dimension samples
      let coins ← $ᵗ Coins samples ((dimension + 1) * params.levels)
      pure (table, hashCore table coins))
    (SeededProductTV.joint ($ᵗ Table Q dimension samples)
      fun _ ↦ ($ᵗ Core Q dimension ((dimension + 1) * params.levels)))
  simpa only [bind_assoc, pure_bind, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    using h.trans hashCore_joint_masking

/-- IND-CPA in the uniform-public-key branch, after adaptive choice of messages. -/
theorem uniform_game_abs_advantage_le
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    |Pr[= true | game params (uniformView keySampler) adversary].toReal - 1 / 2| ≤
      ((dimension + 1) * params.levels) *
        (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  rw [uniform_game_probOutput_eq_hashGame]
  have h := (abs_probOutput_toReal_sub_le_tvDist (hashGame params keySampler adversary)
    (idealGame params keySampler adversary)).trans (hashGame_tvDist_idealGame_le params keySampler adversary)
  simpa only [idealGame_probOutput_true, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat] using h

/-- Exact remaining computational obligation, with the real bootstrapping tape retained.
This is a game advantage, not an assumption or a proved ordinary-LWE reduction. -/
noncomputable def keyReplacementAdvantage
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) : ℝ :=
  |Pr[= true | game params keySampler adversary].toReal -
    Pr[= true | game params (uniformView keySampler) adversary].toReal|

/-- The public GSW security bound exposes the joint-view hop rather than hiding it in a KDM premise. -/
theorem game_abs_advantage_le_keyReplacement_add_masking
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    |Pr[= true | game params keySampler adversary].toReal - 1 / 2| ≤
      keyReplacementAdvantage params keySampler adversary +
        ((dimension + 1) * params.levels) *
          (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) :=
  (abs_sub_le (Pr[= true | game params keySampler adversary].toReal)
    (Pr[= true | game params (uniformView keySampler) adversary].toReal) (1 / 2)).trans
      (add_le_add_right (uniform_game_abs_advantage_le params keySampler adversary)
        (keyReplacementAdvantage params keySampler adversary))

/-- The concrete operational one-key public view contains all controls and no client secret. -/
def operationalView (errorSampler : ProbComp (ZMod Q)) :
    ProbComp (Table Q dimension samples × Vector (StoredCiphertext params (dimension + 1)) dimension) :=
  (fun keys ↦ (tableOfPublicKey keys.publicKey, keys.controls)) <$>
    GSWSampling.generateKeys params dimension samples errorSampler

/-- The actual generator and public-encryption code, with the secret excluded from the adversary view. -/
def operationalGame (errorSampler : ProbComp (ZMod Q))
    (adversary : Adversary (dimension := dimension) (samples := samples) params
      (Vector (StoredCiphertext params (dimension + 1)) dimension)) : ProbComp Bool := do
  let keys ← GSWSampling.generateKeys params dimension samples errorSampler
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (keys.publicKey, keys.controls)
  let ciphertexts ← GSWSampling.encryptInputs params keys.publicKey
    (Vector.replicate 1 (if bit then messages.1 else messages.2.1))
  let guess ← adversary.distinguish messages.2.2 (ciphertexts.get 0)
  pure (bit == guess)

/-- The public-view security experiment is exactly the operational single-challenge experiment. -/
theorem evalDist_operationalGame_eq_game (errorSampler : ProbComp (ZMod Q))
    (adversary : Adversary (dimension := dimension) (samples := samples) params
      (Vector (StoredCiphertext params (dimension + 1)) dimension)) :
    𝒟[operationalGame params errorSampler adversary] =
      𝒟[game params (operationalView params errorSampler) adversary] := by
  apply evalDist_ext
  intro result
  simp only [operationalGame, game, operationalView, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind]
  refine probOutput_bind_congr' (GSWSampling.generateKeys params dimension samples errorSampler)
    result fun keys ↦ ?_
  simp only [storeTable_tableOfPublicKey]
  refine probOutput_bind_congr' ($ᵗ Bool) result fun bit ↦ ?_
  refine probOutput_bind_congr' (adversary.chooseMessages (keys.publicKey, keys.controls))
    result fun messages ↦ ?_
  have h := evalDist_encrypt_eq_encryptInputs_one params (tableOfPublicKey keys.publicKey)
    (if bit then messages.1 else messages.2.1)
  simp only [storeTable_tableOfPublicKey] at h
  let cont : StoredCiphertext params (dimension + 1) → ProbComp Bool := fun ciphertext ↦ do
    let guess ← adversary.distinguish messages.2.2 ciphertext
    pure (bit == guess)
  have hprocessed :
      𝒟[encrypt params (tableOfPublicKey keys.publicKey)
        (if bit then messages.1 else messages.2.1) >>= cont] =
      𝒟[((fun ciphertexts ↦ ciphertexts.get 0) <$>
        GSWSampling.encryptInputs params keys.publicKey
          (Vector.replicate 1 (if bit then messages.1 else messages.2.1))) >>= cont] := by
    simp only [evalDist_bind]
    rw [h]
  simpa [cont, monad_norm] using (OracleComp.probOutput_congr rfl hprocessed).symm

/-- Specialization to the actual one-secret key generator. No hardness premise is discharged here. -/
theorem operational_game_abs_advantage_le (errorSampler : ProbComp (ZMod Q))
    (adversary : Adversary (dimension := dimension) (samples := samples) params (Vector (StoredCiphertext params (dimension + 1)) dimension)) :
    |Pr[= true | game params (operationalView params errorSampler) adversary].toReal - 1 / 2| ≤
      keyReplacementAdvantage params (operationalView params errorSampler) adversary +
        ((dimension + 1) * params.levels) *
          (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) :=
  game_abs_advantage_le_keyReplacement_add_masking params _ adversary

/-- Concrete masking loss for the correctness family, with its existing selector count. -/
noncomputable def familyMaskingBound (n : ℕ) : ℝ :=
  (16 * (n + 1) : ℕ) *
    (Real.sqrt ((GSWBootstrapParameters.coefficientModulus n : ℝ) ^ (n + 1) /
      (2 : ℝ) ^ sampleCount n) / 2)

/-- The public-key output space fits below the selector space by an exponential margin. -/
theorem family_cardinality_margin (n : ℕ) :
    GSWBootstrapParameters.coefficientModulus n ^ (n + 1) * 2 ^ (2 * n) ≤
      2 ^ sampleCount n := by
  have hn : 1 ≤ n + 1 := by omega
  have hsmall : n + 1 ≤ 2 ^ (n + 1) := (Nat.lt_two_pow_self (n := n + 1)).le
  have hbase : 64 * (n + 1) ≤ 2 ^ (7 * (n + 1)) := by
    calc
      _ ≤ 64 * 2 ^ (n + 1) := Nat.mul_le_mul_left _ hsmall
      _ = 2 ^ (6 + (n + 1)) := by rw [pow_add 2 6 (n + 1)]; norm_num
      _ ≤ _ := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega)
  have hmodulus : GSWBootstrapParameters.coefficientModulus n ^ (n + 1) ≤
      2 ^ (112 * (n + 1) ^ 2) := by
    rw [GSWBootstrapParameters.coefficientModulus_eq, ← pow_mul]
    calc
      _ ≤ (2 ^ (7 * (n + 1))) ^ (16 * (n + 1)) := Nat.pow_le_pow_left hbase _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  calc
    _ ≤ 2 ^ (112 * (n + 1) ^ 2) * 2 ^ (2 * n) := Nat.mul_le_mul_right _ hmodulus
    _ = 2 ^ (112 * (n + 1) ^ 2 + 2 * n) := (pow_add _ _ _).symm
    _ ≤ _ := by
      apply pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
      unfold sampleCount
      nlinarith [sq_nonneg (n : ℤ)]

/-- Each column's square-root masking term is bounded by a simple exponentially small function. -/
theorem family_sqrt_ratio_le_half_pow (n : ℕ) :
    Real.sqrt ((GSWBootstrapParameters.coefficientModulus n : ℝ) ^ (n + 1) /
      (2 : ℝ) ^ sampleCount n) ≤ (1 / 2 : ℝ) ^ n := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hmargin :
      (GSWBootstrapParameters.coefficientModulus n : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n) ≤
        (2 : ℝ) ^ sampleCount n := by exact_mod_cast family_cardinality_margin n
  calc
    _ ≤ 1 / (2 : ℝ) ^ (2 * n) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      simpa only [one_mul] using hmargin
    _ = _ := by rw [div_pow, one_pow, div_pow, one_pow, ← pow_mul, Nat.mul_comm n 2]

theorem familyMaskingBound_le_half_pow (n : ℕ) :
    familyMaskingBound n ≤ (16 * (n + 1) : ℕ) * (1 / 2 : ℝ) ^ n := by
  have h := family_sqrt_ratio_le_half_pow n
  unfold familyMaskingBound
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hnonneg := Real.sqrt_nonneg
    ((GSWBootstrapParameters.coefficientModulus n : ℝ) ^ (n + 1) / (2 : ℝ) ^ sampleCount n)
  linarith

/-- The whole-matrix masking error is negligible for the existing correctness parameters. -/
theorem familyMaskingBound_negligible :
    negligible (fun n ↦ ENNReal.ofReal (familyMaskingBound n)) := by
  apply negligible_of_le (g := fun n ↦
    ((16 * (n + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n))
  · intro n
    have h := ENNReal.ofReal_le_ofReal (familyMaskingBound_le_half_pow n)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  · have h := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
      ((16 * (Polynomial.X + 1)) : Polynomial ℕ)
    simpa using h

end FormalProof4FHE.LWE.GSWMasking
