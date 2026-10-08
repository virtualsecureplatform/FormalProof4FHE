/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWPublicKey
import FormalProof4FHE.Probability.LeftoverHash

/-!
# Independent masks linked into same-key GSW controls

An independent binary subset mask statistically hides any fixed gadget offset
when the pad bits are omitted from the view. Encrypted pad bits permit a public
linking computation with a checked GSW noise bound. Its factorization exposes
the joint distribution that a security reduction must handle: with public GSW
pad encryptions, the independent subset mask cancels and the output is a GSW
message gadget minus a selected public-key matrix.

This module studies a concrete one-key compiler, not an ordinary-LWE security
proof of its complete linked view. The noise bound is explicit; compatibility
with a particular bootstrap parameter family requires a separate check.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWLinkedMask

open GSWGadget GSWPublicKey

abbrev Seed {Q : ℕ} (params : Parameters Q) (dimension pads : ℕ) :=
  Fin pads → Ciphertext params (dimension + 1)

/-- Independent binary subset mask on the full ciphertext matrix group. -/
def padMask {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (seed : Seed params dimension pads) (bits : Fin pads → Bool) : Ciphertext params (dimension + 1) :=
  ∑ index, (bitMessage (bits index) : ZMod Q) • seed index

theorem padMask_eq_binarySubsetSum {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (seed : Seed params dimension pads) (bits : Fin pads → Bool) :
    padMask params seed bits = LeftoverHash.binarySubsetSum seed bits := by
  unfold padMask LeftoverHash.binarySubsetSum
  apply Finset.sum_congr rfl
  intro index _
  cases bits index <;> simp [bitMessage]

/-- Retain the public seed but omit the pad bits and all their encryptions. -/
def standaloneView {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (offset : Ciphertext params (dimension + 1)) :
    ProbComp (Seed params dimension pads × Ciphertext params (dimension + 1)) := do
  let seed ← $ᵗ (Seed params dimension pads)
  let bits ← $ᵗ (Fin pads → Bool)
  return (seed, padMask params seed bits + offset)

def shiftEquiv {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (offset : Ciphertext params (dimension + 1)) :
    (Seed params dimension pads × Ciphertext params (dimension + 1)) ≃
      (Seed params dimension pads × Ciphertext params (dimension + 1)) where
  toFun pair := (pair.1, pair.2 + offset)
  invFun pair := (pair.1, pair.2 - offset)
  left_inv pair := by simp
  right_inv pair := by simp

/-- Statistical hiding for the standalone masked hint. This theorem expressly
omits the encrypted pad tape needed by the linking computation. -/
theorem standaloneView_tvDist_le {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (offset : Ciphertext params (dimension + 1)) :
    tvDist (standaloneView (pads := pads) params offset)
      ($ᵗ (Seed params dimension pads × Ciphertext params (dimension + 1))) ≤
        Real.sqrt ((Q : ℝ) ^ ((dimension + 1) * ((dimension + 1) * params.levels)) / 2 ^ pads) / 2 := by
  let hash : Seed params dimension pads → (Fin pads → Bool) → Ciphertext params (dimension + 1) :=
    LeftoverHash.binarySubsetSum
  have hreal : 𝒟[standaloneView (pads := pads) params offset] =
      𝒟[shiftEquiv params offset <$> LeftoverHash.hashed hash] := by
    simp only [standaloneView, LeftoverHash.hashed, map_bind, map_pure,
      padMask_eq_binarySubsetSum]
    rfl
  have hideal : 𝒟[shiftEquiv (pads := pads) params offset <$>
      ($ᵗ (Seed params dimension pads × Ciphertext params (dimension + 1)))] =
        𝒟[$ᵗ (Seed params dimension pads × Ciphertext params (dimension + 1))] :=
    evalDist_map_bijective_uniform_cross _ _ (shiftEquiv params offset).bijective
  calc
    _ = tvDist (shiftEquiv params offset <$> LeftoverHash.hashed hash)
        (shiftEquiv params offset <$> LeftoverHash.ideal) := by
      simp only [tvDist, hreal, LeftoverHash.ideal, hideal]
    _ ≤ tvDist (LeftoverHash.hashed hash)
        (LeftoverHash.ideal (Seed := Seed params dimension pads)
          (Output := Ciphertext params (dimension + 1))) := tvDist_map_le _ _ _
    _ ≤ Real.sqrt
        (Fintype.card (Ciphertext params (dimension + 1)) / Fintype.card (Fin pads → Bool)) / 2 :=
      LeftoverHash.leftover_hash_lemma hash LeftoverHash.binarySubsetSum_isTwoUniversal
    _ = _ := by
      simp [Ciphertext, Matrix, ← pow_mul, Nat.mul_comm]

/-- The offset may depend on an arbitrary earlier key/context. Its entire joint
distribution is retained, provided the later subset masks are independent. -/
theorem standaloneView_context_tvDist_le {Context : Type} {Q dimension pads : ℕ} [NeZero Q]
    (params : Parameters Q) (contextSampler : ProbComp Context)
    (offset : Context → Ciphertext params (dimension + 1)) :
    tvDist
      (contextSampler >>= fun context => Prod.mk context <$>
        standaloneView (pads := pads) params (offset context))
      (contextSampler >>= fun context => Prod.mk context <$>
        ($ᵗ (Seed params dimension pads × Ciphertext params (dimension + 1)))) ≤
      Real.sqrt ((Q : ℝ) ^ ((dimension + 1) * ((dimension + 1) * params.levels)) / 2 ^ pads) / 2 := by
  apply tvDist_bind_left_le_const
  intro context _
  exact (tvDist_map_le _ _ _).trans (standaloneView_tvDist_le params (offset context))

/-- A secret-dependent message may be formed privately; its pad masks are public. -/
def masked {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (seed : Seed params dimension pads) (bits : Fin pads → Bool) (message : ZMod Q) :
    Ciphertext params (dimension + 1) :=
  padMask params seed bits + message • gadget params (dimension + 1)

/-- Public linking using ciphertexts of the pad bits under the same decryption key. -/
def link {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (seed : Seed params dimension pads) (encryptedBits : Fin pads → Ciphertext params (dimension + 1)) :
    Ciphertext params (dimension + 1) :=
  ∑ index, encryptedBits index * digitMatrix params (seed index)

/-- The evaluator only subtracts public matrices. -/
def compiled {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (seed : Seed params dimension pads) (maskedMessage : Ciphertext params (dimension + 1))
    (encryptedBits : Fin pads → Ciphertext params (dimension + 1)) :
    Ciphertext params (dimension + 1) := maskedMessage - link params seed encryptedBits

/-- The pad mask cancels from the decryption phase; only encryption noise is left. -/
theorem noise_compiled {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (secret : Fin (dimension + 1) → ZMod Q) (seed : Seed params dimension pads)
    (bits : Fin pads → Bool) (encryptedBits : Fin pads → Ciphertext params (dimension + 1))
    (message : ZMod Q) :
    GSWOperations.noise secret (gadget params (dimension + 1))
      (compiled params seed (masked params seed bits message) encryptedBits) message =
        -(∑ index, vecMul
          (GSWOperations.noise secret (gadget params (dimension + 1))
            (encryptedBits index) (bitMessage (bits index)))
          (digitMatrix params (seed index))) := by
  have hsingle (index : Fin pads) :
      vecMul secret (encryptedBits index * digitMatrix params (seed index)) =
        vecMul (GSWOperations.noise secret (gadget params (dimension + 1))
          (encryptedBits index) (bitMessage (bits index))) (digitMatrix params (seed index)) +
            vecMul secret ((bitMessage (bits index) : ZMod Q) • seed index) := by
    simp only [GSWOperations.noise, sub_vecMul, smul_vecMul, vecMul_vecMul,
      gadget_mul_digitMatrix, vecMul_smul]
    abel
  change vecMul secret (compiled params seed (masked params seed bits message) encryptedBits) -
    message • vecMul secret (gadget params (dimension + 1)) = _
  simp only [compiled, masked, link, padMask,
    vecMul_sub, vecMul_add, vecMul_sum, vecMul_smul]
  simp_rw [hsingle]
  simp only [vecMul_smul, Finset.sum_add_distrib]
  abel

/-- A polynomial number of links has an explicit, deterministic error budget. -/
theorem noiseBound_compiled {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (secret : Fin (dimension + 1) → ZMod Q) (seed : Seed params dimension pads)
    (bits : Fin pads → Bool) (encryptedBits : Fin pads → Ciphertext params (dimension + 1))
    (message : ZMod Q) (bound : ℕ)
    (hbits : ∀ index, NoiseBound params secret (encryptedBits index) (bitMessage (bits index)) bound) :
    NoiseBound params secret (compiled params seed (masked params seed bits message) encryptedBits)
      message (pads * growth params (dimension + 1) * bound) := by
  intro column
  rw [noise_compiled]
  simp only [Pi.neg_apply, Finset.sum_apply, LatticeCrypto.centeredRepr_natAbs_neg]
  calc
    _ ≤ ∑ index, (LatticeCrypto.centeredRepr (vecMul
          (GSWOperations.noise secret (gadget params (dimension + 1))
            (encryptedBits index) (bitMessage (bits index)))
          (digitMatrix params (seed index)) column)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
    _ ≤ ∑ _index : Fin pads, growth params (dimension + 1) * bound := by
      apply Finset.sum_le_sum
      intro index _
      exact vecMul_error_bound params _ (seed index) bound (hbits index) column
    _ = _ := by simp [mul_assoc]

/-- Public-key selector coefficients of all linking ciphertexts after decomposition. -/
def compiledSelectors {Q dimension pads samples : ℕ} [NeZero Q] (params : Parameters Q)
    (seed : Seed params dimension pads)
    (coins : Fin pads → SelectorCoins samples ((dimension + 1) * params.levels)) :
    Matrix (Fin samples) (Fin ((dimension + 1) * params.levels)) (ZMod Q) :=
  ∑ index, selectors (coins index) * digitMatrix params (seed index)

/-- Factorization of the actual public GSW linking algorithm. -/
theorem link_public {Q dimension pads samples : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples) (seed : Seed params dimension pads) (bits : Fin pads → Bool)
    (coins : Fin pads → SelectorCoins samples ((dimension + 1) * params.levels)) :
    link params seed (fun index => encryptMatrix params key (coins index) (bits index)) =
      publicKeyView key * compiledSelectors params seed coins + padMask params seed bits := by
  simp only [link, encryptMatrix, Matrix.add_mul, Matrix.smul_mul, gadget_mul_digitMatrix,
    compiledSelectors, Matrix.mul_sum, padMask, Matrix.mul_assoc, Finset.sum_add_distrib]

/-- The independent pad cancels exactly. Security must cover the pad encryptions
jointly with the masked message, because the resulting control is public. -/
theorem compiled_public_eq {Q dimension pads samples : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples) (seed : Seed params dimension pads) (bits : Fin pads → Bool)
    (coins : Fin pads → SelectorCoins samples ((dimension + 1) * params.levels)) (message : ZMod Q) :
    compiled params seed (masked params seed bits message)
        (fun index => encryptMatrix params key (coins index) (bits index)) =
      message • gadget params (dimension + 1) - publicKeyView key * compiledSelectors params seed coins := by
  rw [compiled, masked, link_public]
  abel

theorem noise_compiled_public {Q dimension pads samples : ℕ} [NeZero Q] (params : Parameters Q)
    (key : PublicKey Q dimension samples) (secret : Fin (dimension + 1) → ZMod Q)
    (seed : Seed params dimension pads) (bits : Fin pads → Bool)
    (coins : Fin pads → SelectorCoins samples ((dimension + 1) * params.levels)) (message : ZMod Q) :
    GSWOperations.noise secret (gadget params (dimension + 1))
      (compiled params seed (masked params seed bits message)
        (fun index => encryptMatrix params key (coins index) (bits index))) message =
      -vecMul (vecMul secret (publicKeyView key)) (compiledSelectors params seed coins) := by
  rw [compiled_public_eq]
  simp only [GSWOperations.noise, vecMul_sub, vecMul_smul, ← vecMul_vecMul]
  abel

/-- The public-key error bound propagates through every encrypted pad and link. -/
theorem noiseBound_compiled_public {Q dimension pads samples : ℕ} [NeZero Q]
    (params : Parameters Q) (key : PublicKey Q dimension samples)
    (secret : Fin dimension → ZMod Q) (seed : Seed params dimension pads)
    (bits : Fin pads → Bool)
    (coins : Fin pads → SelectorCoins samples ((dimension + 1) * params.levels))
    (message : ZMod Q) (bound : ℕ)
    (hkey : ∀ sample, (LatticeCrypto.centeredRepr
      (vecMul (GSWOperations.extendedSecret secret) (publicKeyView key) sample)).natAbs ≤ bound) :
    NoiseBound params (GSWOperations.extendedSecret secret)
      (compiled params seed (masked params seed bits message)
        (fun index => encryptMatrix params key (coins index) (bits index))) message
      (pads * growth params (dimension + 1) * (samples * bound)) := by
  apply noiseBound_compiled
  intro index
  simpa only [encryptStored, GSWAccumulator.ciphertextView_storeCiphertext] using
    noiseBound_encryptStored params secret key (coins index) (bits index) bound hkey

/-- On a mask-gadget column the linked self-key control has the same quadratic
phase as a direct GSW control, with the exact linked noise term retained. -/
theorem selfKey_mask_phase {Q dimension pads : ℕ} [NeZero Q] (params : Parameters Q)
    (bits : Fin dimension → Bool) (seed : Seed params dimension pads) (padBits : Fin pads → Bool)
    (encryptedBits : Fin pads → Ciphertext params (dimension + 1))
    (encrypted row : Fin dimension) (level : Fin params.levels) :
    vecMul (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
        (compiled params seed (masked params seed padBits (bitMessage (bits encrypted))) encryptedBits)
        (finProdFinEquiv (row.succ, level)) =
      -(bitMessage (bits encrypted) * bitMessage (bits row) * TFHE.Gadget.Base.gadget params level) +
        GSWOperations.noise (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
          (gadget params (dimension + 1))
          (compiled params seed (masked params seed padBits (bitMessage (bits encrypted))) encryptedBits)
          (bitMessage (bits encrypted)) (finProdFinEquiv (row.succ, level)) := by
  have h := congrFun (sub_add_cancel
    (vecMul (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (compiled params seed (masked params seed padBits (bitMessage (bits encrypted))) encryptedBits))
    ((bitMessage (bits encrypted) : ZMod Q) •
      vecMul (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
        (gadget params (dimension + 1)))) (finProdFinEquiv (row.succ, level))
  rw [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, vecMul_gadget_column] at h
  simpa only [GSWOperations.noise, Pi.sub_apply, Pi.smul_apply, vecMul_gadget_column, GSWOperations.extendedSecret,
    Fin.cases_succ, GSWSelfKey.binaryEmbed, bitMessage, smul_eq_mul, mul_neg,
    neg_mul, mul_assoc, add_comm] using h.symm

end FormalProof4FHE.LWE.GSWLinkedMask
