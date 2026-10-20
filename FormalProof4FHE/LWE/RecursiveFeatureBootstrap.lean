/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureGSW
import FormalProof4FHE.LWE.GSWModulusSwitch

/-!
# Same-key refresh over the recursive quadratic feature vector

The public evaluator extracts the negative coefficients of one recursive GSW
column. Its small-modulus phase is decoded with controls for the binary features
`1`, `s_i`, and `s_i * s_j`. The constant control is the public gadget; product
controls are formed by public GSW multiplication of original-bit controls.
All expanded controls and the refreshed result are materialized as finite data.

The correctness statements retain the original secret, the actual product-control
noise, and both modulus-switching and output-decoding margins. They do not assume
security of the controls. Reducing the joint original-bit control view (with cubic
gadget-feature messages) to ordinary LWE remains necessary for FHE security.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.RecursiveFeatureBootstrap

open RecursiveMultiplication RecursiveFeatureGSW GSWModulusSwitch
open TFHE.BootstrappingCorrectness

/-- Binary values of the existing features; this draws no additional secret. -/
def featureBit {n : ℕ} (bits : Fin n → Bool) : Feature n → Bool
  | none => true
  | some (.inl index) => bits index
  | some (.inr pair) => bits pair.1 && bits pair.2

def featureBits {n : ℕ} (bits : Fin n → Bool) : Fin (rows n) → Bool :=
  fun index ↦ featureBit bits ((featureEquiv n).symm index)

theorem feature_eq_bitMessage {q n : ℕ} (bits : Fin n → Bool) (index : Feature n) :
    feature (GSWSelfKey.binaryEmbed (R := ZMod q) bits) index =
      GSWGadget.bitMessage (featureBit bits index) := by
  cases index with
  | none => simp [feature, featureBit, GSWGadget.bitMessage]
  | some index =>
    cases index with
    | inl index => cases h : bits index <;>
        simp [feature, featureBit, GSWSelfKey.binaryEmbed, GSWGadget.bitMessage, h]
    | inr pair =>
        rcases pair with ⟨first, second⟩
        cases hfirst : bits first <;> cases hsecond : bits second <;>
          simp [feature, featureBit, GSWSelfKey.binaryEmbed, GSWGadget.bitMessage, hfirst, hsecond]

theorem featureSecret_binary {q n : ℕ} (bits : Fin n → Bool) :
    featureSecret (GSWSelfKey.binaryEmbed (R := ZMod q) bits) =
      GSWSelfKey.binaryEmbed (featureBits bits) := by
  funext index
  exact feature_eq_bitMessage bits ((featureEquiv n).symm index)

/-- Only the original-bit ciphertexts need to be generated privately. -/
def expandedControl {q n : ℕ} [NeZero q] (params : Parameters q)
    (original : Fin n → Batch params n) : Feature n → Batch params n
  | none => gadgetBatch params
  | some (.inl index) => original index
  | some (.inr pair) => multiply params (original pair.1) (original pair.2)

/-- Store every expanded matrix before the accumulator reads it. -/
def expandControlsStored {q n : ℕ} [NeZero q] (params : Parameters q)
    (original : Fin n → Batch params n) :
    Vector (GSWAccumulator.StoredCiphertext params (rows n)) (rows n) :=
  Vector.ofFn fun index ↦ GSWAccumulator.storeCiphertext params
    (matrix params (expandedControl params original ((featureEquiv n).symm index)))

theorem expandedControls_view {q n : ℕ} [NeZero q] (params : Parameters q)
    (original : Fin n → Batch params n) (index : Fin (rows n)) :
    GSWAccumulator.ciphertextView params ((expandControlsStored params original).get index) =
      matrix params (expandedControl params original ((featureEquiv n).symm index)) := by
  simp [expandControlsStored, Vector.get]

theorem noiseBound_gadgetBatch {q n : ℕ} [NeZero q] (params : Parameters q)
    (secret : Fin n → ZMod q) (bound : ℕ) :
    NoiseBound params secret (gadgetBatch params) 1 bound := by
  intro column
  simp [noise, LatticeCrypto.centeredRepr_eq_valMinAbs]

/-- Product controls have their multiplication error, rather than fresh quartic errors. -/
theorem noiseBound_expandedControl {q n : ℕ} [NeZero q] (params : Parameters q)
    (bits : Fin n → Bool) (original : Fin n → Batch params n) (bound : ℕ)
    (hcontrols : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits) (original index)
      (GSWGadget.bitMessage (bits index)) bound) (index : Feature n) :
    NoiseBound params (GSWSelfKey.binaryEmbed bits) (expandedControl params original index)
      (GSWGadget.bitMessage (featureBit bits index))
      ((GSWGadget.growth params (rows n) + 1) * bound) := by
  cases index with
  | none =>
      simpa [expandedControl, featureBit, GSWGadget.bitMessage] using
        (noiseBound_gadgetBatch params (GSWSelfKey.binaryEmbed bits)
          ((GSWGadget.growth params (rows n) + 1) * bound))
  | some index =>
    cases index with
    | inl index =>
        intro column
        exact (hcontrols index column).trans (Nat.le_mul_of_pos_left _ (by omega))
    | inr pair =>
        have h := noiseBound_multiply_bits params (GSWSelfKey.binaryEmbed bits)
          (original pair.1) (original pair.2) (bits pair.1) (bits pair.2) bound bound
          (hcontrols pair.1) (hcontrols pair.2)
        simpa [expandedControl, featureBit, Nat.add_mul] using h

/-- Public extraction: negate every coefficient, including the constant, and use body zero. -/
def sourceMask {q n : ℕ} (params : Parameters q) (ciphertext : Batch params n)
    (level : Fin params.levels) : Fin (rows n) → ZMod q :=
  fun index ↦ -matrix params ciphertext index (finProdFinEquiv (featureEquiv n none, level))

theorem source_phase {q n : ℕ} [NeZero q] (params : Parameters q) (bits : Fin n → Bool)
    (ciphertext : Batch params n) (level : Fin params.levels) :
    0 - dotProduct (GSWSelfKey.binaryEmbed (featureBits bits)) (sourceMask params ciphertext level) =
      phase params (GSWSelfKey.binaryEmbed bits) ciphertext
        (finProdFinEquiv (featureEquiv n none, level)) := by
  rw [phase_eq_vecMul, featureSecret_binary]
  simp [sourceMask, vecMul, dotProduct]

def bootstrapStored {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : Fin n → Batch params n)
    (ciphertext : Batch params n) (level : Fin params.levels) (oneCode : ZMod p) :
    GSWAccumulator.StoredCiphertext params (rows n) :=
  let controls := expandControlsStored params original
  GSWAccumulator.refreshStored params
    (fun index ↦ GSWAccumulator.ciphertextView params (controls.get index))
    (down factor p ∘ sourceMask params ciphertext level) 0 (decodeNearest 0 oneCode)

def bootstrap {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : Fin n → Batch params n)
    (ciphertext : Batch params n) (level : Fin params.levels) (oneCode : ZMod p) : Batch params n :=
  ofMatrix params (GSWAccumulator.ciphertextView params
    (bootstrapStored params original ciphertext level oneCode))

theorem matrix_bootstrap {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : Fin n → Batch params n)
    (ciphertext : Batch params n) (level : Fin params.levels) (oneCode : ZMod p) :
    matrix params (bootstrap params original ciphertext level oneCode) =
      GSWAccumulator.refresh params
        (fun index ↦ matrix params (expandedControl params original ((featureEquiv n).symm index)))
        (down factor p ∘ sourceMask params ciphertext level) 0 (decodeNearest 0 oneCode) := by
  simp only [bootstrap, matrix_ofMatrix, bootstrapStored, GSWAccumulator.refresh,
    expandedControls_view]

theorem source_distance_of_noiseBound {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin n → Bool) (ciphertext : Batch params n)
    (level : Fin params.levels) (oneCode : ZMod p) (bit : Bool) (bound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hnoise : NoiseBound params (GSWSelfKey.binaryEmbed bits) ciphertext (GSWGadget.bitMessage bit) bound) :
    centeredDistance (0 - dotProduct (GSWSelfKey.binaryEmbed (featureBits bits))
      (sourceMask params ciphertext level)) (up factor p (encodeBit 0 oneCode bit)) ≤ bound := by
  have hgadget := gadgetBatch_phase params (GSWSelfKey.binaryEmbed (R := ZMod (factor * p)) bits) none level
  simp only [feature, mul_one] at hgadget
  have hencode : (GSWGadget.bitMessage bit : ZMod (factor * p)) *
      TFHE.Gadget.Base.gadget params level = up factor p (encodeBit 0 oneCode bit) := by
    cases bit <;> simp [GSWGadget.bitMessage, encodeBit, hcode]
  rw [source_phase]
  simpa only [centeredDistance, noise, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    hgadget, hencode] using hnoise (finProdFinEquiv (featureEquiv n none, level))

/-- Reset the noise under the same underlying binary secret and the same feature format. -/
theorem noiseBound_bootstrap {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin n → Bool)
    (original : Fin n → Batch params n) (ciphertext : Batch params n)
    (level : Fin params.levels) (oneCode : ZMod p) (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hinput : NoiseBound params (GSWSelfKey.binaryEmbed bits) ciphertext (GSWGadget.bitMessage bit) inputBound)
    (hcontrols : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits) (original index)
      (GSWGadget.bitMessage (bits index)) keyBound)
    (hround : 2 * (inputBound + (rows n + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode) :
    NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (bootstrap params original ciphertext level oneCode) (GSWGadget.bitMessage bit)
      (p * rows n * GSWGadget.growth params (rows n) *
        ((GSWGadget.growth params (rows n) + 1) * keyBound)) := by
  have hdecode := decode_switchedPhase factor p (featureBits bits) (sourceMask params ciphertext level)
    0 oneCode bit inputBound
    (source_distance_of_noiseBound params bits ciphertext level oneCode bit inputBound hcode hinput) hround
  have hbound := GSWAccumulator.noiseBound_refresh params
    (featureSecret (GSWSelfKey.binaryEmbed bits)) (featureBits bits)
    (fun index ↦ matrix params (expandedControl params original ((featureEquiv n).symm index)))
    (down factor p ∘ sourceMask params ciphertext level) 0 (decodeNearest 0 oneCode)
    ((GSWGadget.growth params (rows n) + 1) * keyBound)
    (fun index ↦ (noiseBound_iff_gsw _ _ _ _ _).mp
      (noiseBound_expandedControl params bits original keyBound hcontrols ((featureEquiv n).symm index)))
  have hzero : down factor p (0 : ZMod (factor * p)) = 0 := by simp [down]
  simp only [switchedPhase, hzero] at hdecode
  rw [hdecode] at hbound
  rw [noiseBound_iff_gsw, matrix_bootstrap]
  exact hbound

theorem decode_bootstrap {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin n → Bool)
    (original : Fin n → Batch params n) (ciphertext : Batch params n)
    (level : Fin params.levels) (oneCode : ZMod p) (bit : Bool) (inputBound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hinput : NoiseBound params (GSWSelfKey.binaryEmbed bits) ciphertext (GSWGadget.bitMessage bit) inputBound)
    (hcontrols : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits) (original index)
      (GSWGadget.bitMessage (bits index)) keyBound)
    (hround : 2 * (inputBound + (rows n + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode)
    (houtput : 2 * (p * rows n * GSWGadget.growth params (rows n) *
      ((GSWGadget.growth params (rows n) + 1) * keyBound)) <
      centeredDistance 0 (TFHE.Gadget.Base.gadget params level)) :
    decode params (GSWSelfKey.binaryEmbed bits)
      (bootstrap params original ciphertext level oneCode) level = bit :=
  decode_eq_bit params (GSWSelfKey.binaryEmbed bits) _ bit _ level
    (noiseBound_bootstrap params bits original ciphertext level oneCode bit inputBound keyBound
      hcode hinput hcontrols hround) houtput

/-- Backing data for the complete original-bit control table. -/
abbrev StoredOriginal {q : ℕ} (params : Parameters q) (n : ℕ) :=
  Vector (GSWAccumulator.StoredCiphertext params (rows n)) n

def storeOriginal {q n : ℕ} (params : Parameters q) (original : Fin n → Batch params n) :
    StoredOriginal params n :=
  Vector.ofFn fun index ↦ GSWAccumulator.storeCiphertext params (matrix params (original index))

def originalView {q n : ℕ} (params : Parameters q) (original : StoredOriginal params n) :
    Fin n → Batch params n :=
  fun index ↦ ofMatrix params (GSWAccumulator.ciphertextView params (original.get index))

theorem originalView_storeOriginal {q n : ℕ} (params : Parameters q)
    (original : Fin n → Batch params n) : originalView params (storeOriginal params original) = original := by
  funext index
  simp [originalView, storeOriginal, Vector.get, ofMatrix_matrix]

/-- The public runtime interface receives stored control data and no secret. -/
def bootstrapFromStored {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : StoredOriginal params n)
    (ciphertext : GSWAccumulator.StoredCiphertext params (rows n))
    (level : Fin params.levels) (oneCode : ZMod p) : GSWAccumulator.StoredCiphertext params (rows n) :=
  bootstrapStored params (originalView params original)
    (ofMatrix params (GSWAccumulator.ciphertextView params ciphertext)) level oneCode

/-- Private generation in the existing recursive scalar law. Its cubic plaintexts
are explicit; this definition supplies correctness, not a security reduction. -/
def freshOriginal {q n : ℕ} [NeZero q] (params : Parameters q) (bits : Fin n → Bool)
    (masks : Fin n → Fin (rows n * params.levels) → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : Fin n → Fin (rows n * params.levels) → Fin n → ZMod q)
    (bodyErrors : Fin n → Fin (rows n * params.levels) → ZMod q) : Fin n → Batch params n :=
  fun index column ↦ freshCiphertext (GSWSelfKey.binaryEmbed bits)
    (GSWGadget.bitMessage (bits index) * phase params (GSWSelfKey.binaryEmbed bits) (gadgetBatch params) column)
    (masks index column) (innerMasks index column) (errors index column) (bodyErrors index column)

theorem noise_freshOriginal {q n : ℕ} [NeZero q] (params : Parameters q) (bits : Fin n → Bool)
    (masks : Fin n → Fin (rows n * params.levels) → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : Fin n → Fin (rows n * params.levels) → Fin n → ZMod q)
    (bodyErrors : Fin n → Fin (rows n * params.levels) → ZMod q)
    (index : Fin n) (column : Fin (rows n * params.levels)) :
    noise params (GSWSelfKey.binaryEmbed bits) (freshOriginal params bits masks innerMasks errors bodyErrors index)
      (GSWGadget.bitMessage (bits index)) column =
      bodyErrors index column + dotProduct (errors index column) (GSWSelfKey.binaryEmbed bits) := by
  simp only [noise, phase, freshOriginal, decrypt_freshCiphertext, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem noiseBound_freshOriginal {q n : ℕ} [NeZero q] (params : Parameters q) (bits : Fin n → Bool)
    (masks : Fin n → Fin (rows n * params.levels) → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : Fin n → Fin (rows n * params.levels) → Fin n → ZMod q)
    (bodyErrors : Fin n → Fin (rows n * params.levels) → ZMod q) (bound : ℕ)
    (herrors : ∀ index column row, (LatticeCrypto.centeredRepr (errors index column row)).natAbs ≤ bound)
    (hbody : ∀ index column, (LatticeCrypto.centeredRepr (bodyErrors index column)).natAbs ≤ bound)
    (index : Fin n) :
    NoiseBound params (GSWSelfKey.binaryEmbed bits) (freshOriginal params bits masks innerMasks errors bodyErrors index)
      (GSWGadget.bitMessage (bits index)) ((n + 1) * bound) := by
  intro column
  rw [noise_freshOriginal]
  have hterm : ∀ row, (LatticeCrypto.centeredRepr
      (errors index column row * GSWSelfKey.binaryEmbed (R := ZMod q) bits row)).natAbs ≤ bound := by
    intro row
    cases hb : bits row <;> simp [GSWSelfKey.binaryEmbed, hb, LatticeCrypto.centeredRepr_eq_valMinAbs]
    simpa only [LatticeCrypto.centeredRepr_eq_valMinAbs] using herrors index column row
  have hsum := centered_sum_bound
    (fun row ↦ errors index column row * GSWSelfKey.binaryEmbed (R := ZMod q) bits row) bound hterm
  calc
    _ ≤ (LatticeCrypto.centeredRepr (bodyErrors index column)).natAbs +
        (LatticeCrypto.centeredRepr (dotProduct (errors index column) (GSWSelfKey.binaryEmbed bits))).natAbs :=
      TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _
    _ ≤ bound + n * bound := Nat.add_le_add (hbody index column)
      (by simpa only [dotProduct, Fintype.card_fin] using hsum)
    _ = _ := by ring

/-- Complete private materialization before exposing any control ciphertext. -/
def freshOriginalStored {q n : ℕ} [NeZero q] (params : Parameters q) (bits : Fin n → Bool)
    (masks : Fin n → Fin (rows n * params.levels) → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : Fin n → Fin (rows n * params.levels) → Fin n → ZMod q)
    (bodyErrors : Fin n → Fin (rows n * params.levels) → ZMod q) : StoredOriginal params n :=
  storeOriginal params (freshOriginal params bits masks innerMasks errors bodyErrors)

theorem originalView_freshOriginalStored {q n : ℕ} [NeZero q] (params : Parameters q) (bits : Fin n → Bool)
    (masks : Fin n → Fin (rows n * params.levels) → Matrix (Fin n) (Fin n) (ZMod q))
    (innerMasks errors : Fin n → Fin (rows n * params.levels) → Fin n → ZMod q)
    (bodyErrors : Fin n → Fin (rows n * params.levels) → ZMod q) :
    originalView params (freshOriginalStored params bits masks innerMasks errors bodyErrors) =
      freshOriginal params bits masks innerMasks errors bodyErrors :=
  originalView_storeOriginal params _

/-- One gate returns stored data after NAND and refresh. -/
def refreshedNandStored {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : Fin n → Batch params n)
    (first second : Batch params n) (level : Fin params.levels) (oneCode : ZMod p) :
    GSWAccumulator.StoredCiphertext params (rows n) :=
  bootstrapStored params original (nand params first second) level oneCode

def refreshedNand {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (original : Fin n → Batch params n)
    (first second : Batch params n) (level : Fin params.levels) (oneCode : ZMod p) : Batch params n :=
  ofMatrix params (GSWAccumulator.ciphertextView params
    (refreshedNandStored params original first second level oneCode))

/-- A single invariant is restored after every gate, without a new secret or key schedule. -/
theorem noiseBound_refreshedNand {factor p n : ℕ} [NeZero factor] [NeZero p]
    (params : Parameters (factor * p)) (bits : Fin n → Bool)
    (original : Fin n → Batch params n) (first second : Batch params n)
    (level : Fin params.levels) (oneCode : ZMod p) (firstBit secondBit : Bool) (bound keyBound : ℕ)
    (hcode : TFHE.Gadget.Base.gadget params level = up factor p oneCode)
    (hfirst : NoiseBound params (GSWSelfKey.binaryEmbed bits) first (GSWGadget.bitMessage firstBit) bound)
    (hsecond : NoiseBound params (GSWSelfKey.binaryEmbed bits) second (GSWGadget.bitMessage secondBit) bound)
    (hcontrols : ∀ index, NoiseBound params (GSWSelfKey.binaryEmbed bits) (original index)
      (GSWGadget.bitMessage (bits index)) keyBound)
    (hround : 2 * ((GSWGadget.growth params (rows n) + 1) * bound + (rows n + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode) :
    NoiseBound params (GSWSelfKey.binaryEmbed bits)
      (refreshedNand params original first second level oneCode) (GSWGadget.bitMessage (!(firstBit && secondBit)))
      (p * rows n * GSWGadget.growth params (rows n) *
        ((GSWGadget.growth params (rows n) + 1) * keyBound)) := by
  have hproduct := noiseBound_nand params (GSWSelfKey.binaryEmbed bits) first second
    firstBit secondBit bound bound hfirst hsecond
  have hinput : NoiseBound params (GSWSelfKey.binaryEmbed bits) (nand params first second)
      (GSWGadget.bitMessage (!(firstBit && secondBit))) ((GSWGadget.growth params (rows n) + 1) * bound) := by
    simpa only [Nat.add_mul, one_mul] using hproduct
  exact noiseBound_bootstrap params bits original _ level oneCode _ _ keyBound hcode hinput hcontrols hround

end FormalProof4FHE.LWE.RecursiveFeatureBootstrap
