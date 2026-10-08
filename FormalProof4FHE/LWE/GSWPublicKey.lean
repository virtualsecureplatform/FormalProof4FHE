/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWCircuit

/-!
# Stored public-key GSW encryption under the same bootstrap secret

The public key is a stored table of ordinary zero-message LWE samples. Public
encryption selects binary combinations of its columns and adds the
bit gadget. The secret is used only when creating the public key and self-key
controls; public encryption and circuit evaluation take finite public data.

The selected public-key sample count fits the proved circuit noise invariant for
every positive secret dimension. The final theorem proves whole-circuit correctness
for actual public input encryption and actual private generation of same-key controls,
subject to explicit bounds on the original sampled errors. It has no codeword-margin,
lookup-correctness, or circular-security premise. Error-sampler support/tail bounds,
bit-operation costs, and security of the complete joint public/self-key view are
separate obligations; ordinary-LWE security is not asserted here.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWPublicKey

open GSWGadget GSWAccumulator

abbrev PublicKey (Q dimension samples : ℕ) :=
  Vector (Vector (ZMod Q) samples) (dimension + 1)

/-- Materialize the public-key coefficients before handing the key to the evaluator. -/
def storePublicKey {Q dimension samples : ℕ}
    (matrix : Matrix (Fin (dimension + 1)) (Fin samples) (ZMod Q)) : PublicKey Q dimension samples :=
  Vector.ofFn fun row ↦ Vector.ofFn fun column ↦ matrix row column

def publicKeyView {Q dimension samples : ℕ} (key : PublicKey Q dimension samples) :
    Matrix (Fin (dimension + 1)) (Fin samples) (ZMod Q) :=
  fun row column ↦ (key.get row).get column

@[simp]
theorem publicKeyView_storePublicKey {Q dimension samples : ℕ}
    (matrix : Matrix (Fin (dimension + 1)) (Fin samples) (ZMod Q)) :
    publicKeyView (storePublicKey matrix) = matrix := by
  ext row column
  simp [publicKeyView, storePublicKey]

/-- Actual private generation of an ordinary LWE zero-sample public key. -/
def freshPublicKey {Q dimension samples : ℕ} (secret : Fin dimension → ZMod Q)
    (challenge : Matrix (Fin dimension) (Fin samples) (ZMod Q)) (error : Fin samples → ZMod Q) :
    PublicKey Q dimension samples :=
  storePublicKey (GSWOperations.ciphertextMatrix (challenge, vecMul secret challenge + error))

/-- The generated table has exactly the originally sampled zero-message error. -/
theorem freshPublicKey_phase {Q dimension samples : ℕ} (secret : Fin dimension → ZMod Q)
    (challenge : Matrix (Fin dimension) (Fin samples) (ZMod Q)) (error : Fin samples → ZMod Q) :
    vecMul (GSWOperations.extendedSecret secret)
      (publicKeyView (freshPublicKey secret challenge error)) = error := by
  rw [freshPublicKey, publicKeyView_storePublicKey, GSWOperations.vecMul_ciphertextMatrix]
  simp

/-- Concrete independent selection coins, one vector per public-key sample. -/
abbrev SelectorCoins (samples columns : ℕ) := Vector (Vector Bool columns) samples

def selectors {Q samples columns : ℕ} (coins : SelectorCoins samples columns) :
    Matrix (Fin samples) (Fin columns) (ZMod Q) :=
  fun sample column ↦ bitMessage ((coins.get sample).get column)

/-- Every public selection coefficient has centered magnitude at most one. -/
theorem selectors_bound {Q samples columns : ℕ} [NeZero Q]
    (coins : SelectorCoins samples columns) (sample : Fin samples) (column : Fin columns) :
    (LatticeCrypto.centeredRepr (selectors (Q := Q) coins sample column)).natAbs ≤ 1 := by
  unfold selectors
  cases (coins.get sample).get column
  · simp [bitMessage, LatticeCrypto.centeredRepr_eq_valMinAbs]
  · simpa [bitMessage] using TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le (q := Q) 1

/-- Public bit encryption uses only stored public-key entries and fresh binary selection coins. -/
def encryptMatrix {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples) (coins : SelectorCoins samples ((dimension + 1) * params.levels))
    (bit : Bool) : Ciphertext params (dimension + 1) :=
  publicKeyView key * selectors coins + (bitMessage bit : ZMod Q) • gadget params (dimension + 1)

def encryptStored {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples) (coins : SelectorCoins samples ((dimension + 1) * params.levels))
    (bit : Bool) : StoredCiphertext params (dimension + 1) :=
  storeCiphertext params (encryptMatrix params key coins bit)

/-- Gadget addition cancels exactly: public encryption noise is the selected public-key error. -/
theorem noise_encryptMatrix {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (secret : Fin dimension → ZMod Q) (key : PublicKey Q dimension samples)
    (coins : SelectorCoins samples ((dimension + 1) * params.levels)) (bit : Bool) :
    GSWOperations.noise (GSWOperations.extendedSecret secret) (gadget params (dimension + 1))
      (encryptMatrix params key coins bit) (bitMessage bit) =
      vecMul (vecMul (GSWOperations.extendedSecret secret) (publicKeyView key)) (selectors coins) := by
  simp only [encryptMatrix, GSWOperations.noise, vecMul_add, vecMul_smul,
    ← vecMul_vecMul]
  abel

/-- A deterministic public-encryption bound, allowing arbitrary correlations in the key errors. -/
theorem noiseBound_encryptStored {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
    (secret : Fin dimension → ZMod Q) (key : PublicKey Q dimension samples)
    (coins : SelectorCoins samples ((dimension + 1) * params.levels)) (bit : Bool) (bound : ℕ)
    (hkey : ∀ sample, (LatticeCrypto.centeredRepr
      (vecMul (GSWOperations.extendedSecret secret) (publicKeyView key) sample)).natAbs ≤ bound) :
    NoiseBound params (GSWOperations.extendedSecret secret)
      (ciphertextView params (encryptStored params key coins bit)) (bitMessage bit) (samples * bound) := by
  intro column
  rw [encryptStored, ciphertextView_storeCiphertext, noise_encryptMatrix]
  change (LatticeCrypto.centeredRepr (∑ sample,
    vecMul (GSWOperations.extendedSecret secret) (publicKeyView key) sample *
      selectors coins sample column)).natAbs ≤ _
  calc
    _ ≤ ∑ sample, (LatticeCrypto.centeredRepr
        (vecMul (GSWOperations.extendedSecret secret) (publicKeyView key) sample *
          selectors coins sample column)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
    _ ≤ ∑ _sample : Fin samples, bound := by
      apply Finset.sum_le_sum
      intro sample _
      have h := (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
        (Nat.mul_le_mul (hkey sample) (selectors_bound coins sample column))
      simpa only [Nat.mul_one] using h
    _ = samples * bound := by simp

/-- Polynomial public-key sample count, with enough room in the deterministic error budget. -/
@[irreducible] def sampleCount (dimension : ℕ) : ℕ := 256 * (dimension + 1) ^ 2

theorem sampleCount_le_budget {dimension : ℕ} (hdimension : 0 < dimension) :
    sampleCount dimension ≤ GSWBootstrapParameters.lookupModulus dimension * dimension *
      growth (GSWBootstrapParameters.params dimension) (dimension + 1) := by
  have hb := GSWBootstrapParameters.base_ge dimension
  have hshort : dimension + 1 ≤ GSWBootstrapParameters.base dimension - 1 := by
    unfold GSWBootstrapParameters.base
    omega
  have hg : 16 * (dimension + 1) ^ 2 ≤ growth (GSWBootstrapParameters.params dimension) (dimension + 1) := by
    unfold growth GSWBootstrapParameters.params
    calc
      _ = ((dimension + 1) * 16) * (dimension + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hshort
  have hp : 16 ≤ GSWBootstrapParameters.lookupModulus dimension := by
    have hpow := pow_le_pow_right' (by omega : 1 ≤ GSWBootstrapParameters.base dimension)
      (by decide : 1 ≤ 3)
    simp only [pow_one] at hpow
    exact (by omega : 16 ≤ GSWBootstrapParameters.base dimension).trans hpow
  have hpn : 16 ≤ GSWBootstrapParameters.lookupModulus dimension * dimension :=
    hp.trans (Nat.le_mul_of_pos_right _ hdimension)
  calc
    _ = 16 * (16 * (dimension + 1) ^ 2) := by unfold sampleCount; ring
    _ ≤ _ := Nat.mul_le_mul hpn hg

/-- Public encryption from an actual generated key fits the circuit invariant. -/
theorem noiseBound_freshPublicEncryption {dimension : ℕ} (hdimension : 0 < dimension)
    (bits : Fin dimension → Bool)
    (challenge : Matrix (Fin dimension) (Fin (sampleCount dimension))
      (ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension)))
    (error : Fin (sampleCount dimension) →
      ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension))
    (coins : SelectorCoins (sampleCount dimension) ((dimension + 1) * (GSWBootstrapParameters.params dimension).levels))
    (bit : Bool)
    (herror : ∀ sample, (LatticeCrypto.centeredRepr (error sample)).natAbs ≤ GSWBootstrapParameters.keyBound dimension) :
    NoiseBound (GSWBootstrapParameters.params dimension) (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (ciphertextView (GSWBootstrapParameters.params dimension)
        (encryptStored (GSWBootstrapParameters.params dimension)
          (freshPublicKey (GSWSelfKey.binaryEmbed bits) challenge error) coins bit))
      (bitMessage bit) (GSWBootstrapParameters.outputBound dimension) := by
  have hkey : ∀ sample, (LatticeCrypto.centeredRepr
      (vecMul (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
        (publicKeyView (freshPublicKey (GSWSelfKey.binaryEmbed bits) challenge error)) sample)).natAbs ≤
        GSWBootstrapParameters.keyBound dimension := by
    simpa only [freshPublicKey_phase] using herror
  have hbound := noiseBound_encryptStored (GSWBootstrapParameters.params dimension)
    (GSWSelfKey.binaryEmbed bits) _ coins bit (GSWBootstrapParameters.keyBound dimension) hkey
  intro column
  exact (hbound column).trans
    (Nat.mul_le_mul_right (GSWBootstrapParameters.keyBound dimension) (sampleCount_le_budget hdimension))

/-- Actual fresh self-key controls, materialized under the one underlying secret. -/
def storedFreshBootKey {Q dimension : ℕ} [NeZero Q] (params : Parameters Q)
    (bits : Fin dimension → Bool)
    (challenges : Fin dimension →
      Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod Q))
    (errors : Fin dimension → Fin ((dimension + 1) * params.levels) → ZMod Q) :
    Vector (StoredCiphertext params (dimension + 1)) dimension :=
  Vector.ofFn fun index ↦ storeCiphertext params ((freshBootKey params bits challenges errors) index)

/-- Independently stored public encryptions of a vector of input bits. -/
def encryptInputsStored {Q dimension samples inputs : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples)
    (coins : Vector (SelectorCoins samples ((dimension + 1) * params.levels)) inputs)
    (messages : Vector Bool inputs) : Vector (StoredCiphertext params (dimension + 1)) inputs :=
  Vector.ofFn fun index ↦ encryptStored params key (coins.get index) (messages.get index)

/-- Whole shared-circuit correctness for actual public encryption and actual same-key controls.
The only noise premises concern the original errors used in generating those keys. -/
theorem decrypt_evaluate_freshPublicKey {dimension inputs wires : ℕ} (hdimension : 0 < dimension)
    (bits : Fin dimension → Bool)
    (publicChallenge : Matrix (Fin dimension) (Fin (sampleCount dimension))
      (ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension)))
    (publicErrors : Fin (sampleCount dimension) →
      ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension))
    (controlChallenges : Fin dimension → Matrix (Fin dimension)
      (Fin ((dimension + 1) * (GSWBootstrapParameters.params dimension).levels))
      (ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension)))
    (controlErrors : Fin dimension → Fin ((dimension + 1) * (GSWBootstrapParameters.params dimension).levels) →
      ZMod (GSWBootstrapParameters.factor dimension * GSWBootstrapParameters.lookupModulus dimension))
    (coins : Vector (SelectorCoins (sampleCount dimension)
      ((dimension + 1) * (GSWBootstrapParameters.params dimension).levels)) inputs)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires)
    (hpublic : ∀ sample, (LatticeCrypto.centeredRepr (publicErrors sample)).natAbs ≤
      GSWBootstrapParameters.keyBound dimension)
    (hcontrols : ∀ index column, (LatticeCrypto.centeredRepr (controlErrors index column)).natAbs ≤
      GSWBootstrapParameters.keyBound dimension) :
    decrypt (GSWBootstrapParameters.params dimension) (GSWSelfKey.binaryEmbed bits)
      (ciphertextView (GSWBootstrapParameters.params dimension)
        (GSWCircuit.evaluate (GSWBootstrapParameters.params dimension) (GSWBootstrapParameters.level dimension)
          (GSWBootstrapParameters.oneCode dimension)
          (storedFreshBootKey (GSWBootstrapParameters.params dimension) bits controlChallenges controlErrors)
          (encryptInputsStored (GSWBootstrapParameters.params dimension)
            (freshPublicKey (GSWSelfKey.binaryEmbed bits) publicChallenge publicErrors) coins messages)
          program output)) (GSWBootstrapParameters.level dimension) =
      (GSWCircuit.runBits messages program).get output := by
  apply GSWCircuit.decrypt_evaluate bits _ _ messages program output
  · intro index
    simpa only [storedFreshBootKey, Vector.get_ofFn, ciphertextView_storeCiphertext, freshBootKey] using
      noiseBound_fresh (GSWBootstrapParameters.params dimension) (GSWSelfKey.binaryEmbed bits)
        (bits index) (controlChallenges index) (controlErrors index)
        (GSWBootstrapParameters.keyBound dimension) (hcontrols index)
  · intro index
    simpa only [encryptInputsStored, Vector.get_ofFn] using
      noiseBound_freshPublicEncryption hdimension bits publicChallenge publicErrors
        (coins.get index) (messages.get index) hpublic

end FormalProof4FHE.LWE.GSWPublicKey
