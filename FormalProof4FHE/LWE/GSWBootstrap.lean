/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWModulusSwitch

/-!
# Public same-key large-modulus GSW refresh

Extract one public body-gadget column, floor-reduce its mask and body, and apply
the stored cyclic lookup. The evaluator has no secret argument. The correctness
theorem derives the lookup bit from the original ciphertext's noise bound and
the explicit rounding margin, rather than assuming that the lookup is correct.
The actual `freshBootKey` corollary uses one unchanged binary secret for controls,
input, and output. These results do not prove security of that self-key tape.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWBootstrap

open GSWGadget GSWModulusSwitch TFHE.BootstrappingCorrectness

/-- Public mask of the selected body-gadget column. -/
def sourceMask {Q dimension : ℕ} (params : Parameters Q)
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels) :
    Fin dimension → ZMod Q :=
  fun index ↦ ciphertext index.succ (finProdFinEquiv (0, level))

/-- Public body of the same selected column. -/
def sourceBody {Q dimension : ℕ} (params : Parameters Q)
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels) : ZMod Q :=
  ciphertext 0 (finProdFinEquiv (0, level))

/-- Extraction changes neither the decryption secret nor the column's phase. -/
theorem source_phase {Q dimension : ℕ} (params : Parameters Q)
    (secret : Fin dimension → ZMod Q) (ciphertext : Ciphertext params (dimension + 1))
    (level : Fin params.levels) :
    sourceBody params ciphertext level - dotProduct secret (sourceMask params ciphertext level) =
      vecMul (GSWOperations.extendedSecret secret) ciphertext (finProdFinEquiv (0, level)) := by
  simp [sourceBody, sourceMask, vecMul, dotProduct, GSWOperations.extendedSecret,
    Fin.sum_univ_succ, sub_eq_add_neg]

/-- Concrete public refresh returning data, so later matrix reads do not repeat the computation. -/
def bootstrapStored {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p))
    (controls : Fin dimension → Ciphertext params (dimension + 1))
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels)
    (oneCode : ZMod p) : GSWAccumulator.StoredCiphertext params (dimension + 1) :=
  GSWAccumulator.refreshStored params controls
    (down factor p ∘ sourceMask params ciphertext level)
    (down factor p (sourceBody params ciphertext level)) (decodeNearest 0 oneCode)

/-- Proof-facing matrix view of the already stored output. -/
def bootstrap {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p))
    (controls : Fin dimension → Ciphertext params (dimension + 1))
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels)
    (oneCode : ZMod p) : Ciphertext params (dimension + 1) :=
  GSWAccumulator.ciphertextView params (bootstrapStored params controls ciphertext level oneCode)

/-- The full column noise bound supplies the exact source-codeword distance premise. -/
theorem source_distance_of_noiseBound {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin dimension → Bool)
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels)
    (oneCode : ZMod p) (bit : Bool) (bound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hnoise : NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      ciphertext (bitMessage bit) bound) :
    centeredDistance (sourceBody params ciphertext level -
      dotProduct (GSWSelfKey.binaryEmbed bits) (sourceMask params ciphertext level))
      (up factor p (encodeBit 0 oneCode bit)) ≤ bound := by
  have hgadget : vecMul (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (gadget params (dimension + 1)) (finProdFinEquiv (0, level)) =
      TFHE.Gadget.Base.gadget params level := by
    rw [vecMul_gadget_column]
    simp [GSWOperations.extendedSecret]
  have hencode : (bitMessage bit : ZMod (factor * p)) * TFHE.Gadget.Base.gadget params level =
      up factor p (encodeBit 0 oneCode bit) := by
    cases bit <;> simp [bitMessage, encodeBit, hcode]
  rw [source_phase]
  simpa only [centeredDistance, GSWOperations.noise, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, hgadget, hencode] using hnoise (finProdFinEquiv (0, level))

/-- Actual refresh preserves the input bit and resets its noise under the same secret. -/
theorem noiseBound_bootstrap {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin dimension → Bool)
    (controls : Fin dimension → Ciphertext params (dimension + 1))
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels)
    (oneCode : ZMod p) (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hinput : NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      ciphertext (bitMessage bit) inputBound)
    (hcontrols : ∀ index, NoiseBound params
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) (controls index)
      (bitMessage (bits index)) keyBound)
    (hround : 2 * (inputBound + (dimension + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode) :
    NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (bootstrap params controls ciphertext level oneCode) (bitMessage bit)
      (p * dimension * growth params (dimension + 1) * keyBound) := by
  have hdecode := decode_switchedPhase factor p bits (sourceMask params ciphertext level)
    (sourceBody params ciphertext level) oneCode bit inputBound
    (source_distance_of_noiseBound params bits ciphertext level oneCode bit inputBound hcode hinput)
    hround
  have hrefresh := GSWAccumulator.noiseBound_refresh params
    (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) bits controls
    (down factor p ∘ sourceMask params ciphertext level)
    (down factor p (sourceBody params ciphertext level)) (decodeNearest 0 oneCode) keyBound hcontrols
  change decodeNearest 0 oneCode
    (down factor p (sourceBody params ciphertext level) -
      dotProduct (GSWSelfKey.binaryEmbed bits) (down factor p ∘ sourceMask params ciphertext level)) =
      bit at hdecode
  rw [hdecode] at hrefresh
  exact hrefresh

/-- The same theorem for the actual fresh control generator, with explicit error bounds. -/
theorem noiseBound_bootstrap_freshBootKey {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin dimension → Bool)
    (challenges : Fin dimension →
      Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod (factor * p)))
    (errors : Fin dimension → Fin ((dimension + 1) * params.levels) → ZMod (factor * p))
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels)
    (oneCode : ZMod p) (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hinput : NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      ciphertext (bitMessage bit) inputBound)
    (herrors : ∀ index column, (LatticeCrypto.centeredRepr (errors index column)).natAbs ≤ keyBound)
    (hround : 2 * (inputBound + (dimension + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode) :
    NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (bootstrap params (GSWAccumulator.freshBootKey params bits challenges errors)
        ciphertext level oneCode) (bitMessage bit)
      (p * dimension * growth params (dimension + 1) * keyBound) := by
  apply noiseBound_bootstrap params bits _ ciphertext level oneCode bit inputBound keyBound
    hcode hinput _ hround
  intro index
  exact noiseBound_fresh params (GSWSelfKey.binaryEmbed bits) (bits index)
    (challenges index) (errors index) keyBound (herrors index)

/-- Nearest-codeword decryption of the refreshed output, with both margins made explicit. -/
theorem decrypt_bootstrap_freshBootKey {factor p dimension : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin dimension → Bool)
    (challenges : Fin dimension →
      Matrix (Fin dimension) (Fin ((dimension + 1) * params.levels)) (ZMod (factor * p)))
    (errors : Fin dimension → Fin ((dimension + 1) * params.levels) → ZMod (factor * p))
    (ciphertext : Ciphertext params (dimension + 1)) (level : Fin params.levels)
    (oneCode : ZMod p) (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hinput : NoiseBound params (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      ciphertext (bitMessage bit) inputBound)
    (herrors : ∀ index column, (LatticeCrypto.centeredRepr (errors index column)).natAbs ≤ keyBound)
    (hround : 2 * (inputBound + (dimension + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode)
    (houtput : 2 * (p * dimension * growth params (dimension + 1) * keyBound) <
      centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decrypt params (GSWSelfKey.binaryEmbed bits)
      (bootstrap params (GSWAccumulator.freshBootKey params bits challenges errors)
        ciphertext level oneCode) level = bit :=
  decrypt_eq_bit params (GSWSelfKey.binaryEmbed bits) _ bit _ level
    (noiseBound_bootstrap_freshBootKey params bits challenges errors ciphertext level oneCode bit
      inputBound keyBound hcode hinput herrors hround) houtput

end FormalProof4FHE.LWE.GSWBootstrap
