/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialCorrectness

/-!
# Fresh Centered-Binomial TFHE Refresh Correctness

This file connects the concrete Boolean-table bootstrapping theorem to a freshly encrypted
Boolean input.  At modulus `q = 2N`, the two input phases are placed at the antipodal residues
`0` and `N`.  The anti-periodic lookup table classifies every centered-binomial error of width
`eta` correctly when `2 * eta < N`.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomialRefresh

noncomputable section

/-- Antipodal Boolean input encoding at the exact native modulus `q = 2N`. -/
def inputCode (degree : ℕ) (bit : Bool) : ZMod (2 * (degree + 1)) :=
  BootstrappingCorrectness.encodeBit 0 (degree + 1) bit

/-- The first-half threshold table whose anti-periodic extension recognizes the two antipodal
input codewords.  The doubled comparison avoids any parity convention at `N / 2`; the strict
noise margin ensures that supported inputs never lie on the boundary. -/
def firstHalfThreshold (degree : ℕ) (index : Fin (degree + 1)) : Bool :=
  decide (degree + 1 ≤ 2 * index.val)

@[simp]
theorem exactRoundExponent_val (degree : ℕ)
    (value : ZMod (2 * (degree + 1))) :
    (RotationLookup.exactRoundExponent degree value).val = value.val := by
  rfl

/-- An integer already in the canonical residue interval has that integer as its `ZMod` value. -/
theorem val_intCast_eq_of_nonneg_of_lt {q : ℕ} [NeZero q] (value : ℤ)
    (hnonneg : 0 ≤ value) (hlt : value < q) :
    ((value : ZMod q).val : ℤ) = value := by
  rw [ZMod.val_intCast, Int.emod_eq_of_lt hnonneg hlt]

/-! ## Deterministic threshold regions -/

theorem antiPeriodicThreshold_eq_false_of_low (degree : ℕ)
    (exponent : Fin (2 * (degree + 1)))
    (hfirst : exponent.val < degree + 1)
    (hlow : 2 * exponent.val < degree + 1) :
    RotationLookup.antiPeriodicBit (firstHalfThreshold degree) exponent = false := by
  simp [RotationLookup.antiPeriodicBit, hfirst, firstHalfThreshold,
    RotationLookup.halfIndex_val_of_lt exponent hfirst, Nat.not_le.mpr hlow]

theorem antiPeriodicThreshold_eq_true_of_firstHigh (degree : ℕ)
    (exponent : Fin (2 * (degree + 1)))
    (hfirst : exponent.val < degree + 1)
    (hhigh : degree + 1 ≤ 2 * exponent.val) :
    RotationLookup.antiPeriodicBit (firstHalfThreshold degree) exponent = true := by
  simp [RotationLookup.antiPeriodicBit, hfirst, firstHalfThreshold,
    RotationLookup.halfIndex_val_of_lt exponent hfirst, hhigh]

theorem antiPeriodicThreshold_eq_true_of_secondLow (degree : ℕ)
    (exponent : Fin (2 * (degree + 1)))
    (hsecond : ¬exponent.val < degree + 1)
    (hlow : 2 * (exponent.val - (degree + 1)) < degree + 1) :
    RotationLookup.antiPeriodicBit (firstHalfThreshold degree) exponent = true := by
  simp [RotationLookup.antiPeriodicBit, hsecond, firstHalfThreshold,
    RotationLookup.halfIndex_val_of_not_lt exponent hsecond, Nat.not_le.mpr hlow]

theorem antiPeriodicThreshold_eq_false_of_secondHigh (degree : ℕ)
    (exponent : Fin (2 * (degree + 1)))
    (hsecond : ¬exponent.val < degree + 1)
    (hhigh : degree + 1 ≤ 2 * (exponent.val - (degree + 1))) :
    RotationLookup.antiPeriodicBit (firstHalfThreshold degree) exponent = false := by
  simp [RotationLookup.antiPeriodicBit, hsecond, firstHalfThreshold,
    RotationLookup.halfIndex_val_of_not_lt exponent hsecond, hhigh]

/-! ## Classification of a bounded modular input phase -/

/-- The anti-periodic threshold table recognizes an antipodal Boolean codeword after adding any
signed error in `[-eta, eta]`, provided the two noise neighborhoods do not reach the midpoint. -/
theorem antiPeriodicThreshold_inputCode_add_intCast
    (degree eta : ℕ) (bit : Bool) (value : ℤ)
    (hvalue : |value| ≤ eta) (hmargin : 2 * eta < degree + 1) :
    RotationLookup.antiPeriodicBit (firstHalfThreshold degree)
        (RotationLookup.exactRoundExponent degree
          (inputCode degree bit + (value : ZMod (2 * (degree + 1))))) = bit := by
  cases bit with
  | false =>
      by_cases hnonneg : 0 ≤ value
      · have hupper : value ≤ (eta : ℤ) := by
          simpa [abs_of_nonneg hnonneg] using hvalue
        have hlt : value < (2 * (degree + 1) : ℕ) := by omega
        have hphase :
            inputCode degree false + (value : ZMod (2 * (degree + 1))) =
              (value : ZMod (2 * (degree + 1))) := by
          simp [inputCode, BootstrappingCorrectness.encodeBit]
        have hexponent :
            ((RotationLookup.exactRoundExponent degree
              (inputCode degree false +
                (value : ZMod (2 * (degree + 1))))).val : ℤ) = value := by
          rw [exactRoundExponent_val, hphase]
          exact val_intCast_eq_of_nonneg_of_lt value hnonneg hlt
        apply antiPeriodicThreshold_eq_false_of_low degree
        · omega
        · omega
      · have hnegative : value < 0 := lt_of_not_ge hnonneg
        have hlower : -value ≤ (eta : ℤ) := by
          simpa [abs_of_neg hnegative] using hvalue
        let wrapped : ℤ := (2 * (degree + 1) : ℕ) + value
        have hwrappedNonneg : 0 ≤ wrapped := by
          dsimp [wrapped]
          omega
        have hwrappedLt : wrapped < (2 * (degree + 1) : ℕ) := by
          dsimp [wrapped]
          omega
        have hphase :
            inputCode degree false + (value : ZMod (2 * (degree + 1))) =
              (wrapped : ZMod (2 * (degree + 1))) := by
          dsimp [wrapped]
          simp only [inputCode, BootstrappingCorrectness.encodeBit, Bool.false_eq_true,
            if_false, zero_add]
          rw [ZMod.intCast_eq_intCast_iff']
          simp
        have hexponent :
            ((RotationLookup.exactRoundExponent degree
              (inputCode degree false +
                (value : ZMod (2 * (degree + 1))))).val : ℤ) = wrapped := by
          rw [exactRoundExponent_val, hphase]
          exact val_intCast_eq_of_nonneg_of_lt wrapped hwrappedNonneg hwrappedLt
        apply antiPeriodicThreshold_eq_false_of_secondHigh degree
        · omega
        · dsimp [wrapped] at hexponent
          omega
  | true =>
      by_cases hnonneg : 0 ≤ value
      · have hupper : value ≤ (eta : ℤ) := by
          simpa [abs_of_nonneg hnonneg] using hvalue
        let shifted : ℤ := (degree + 1 : ℕ) + value
        have hshiftedNonneg : 0 ≤ shifted := by
          dsimp [shifted]
          omega
        have hshiftedLt : shifted < (2 * (degree + 1) : ℕ) := by
          dsimp [shifted]
          omega
        have hphase :
            inputCode degree true + (value : ZMod (2 * (degree + 1))) =
              (shifted : ZMod (2 * (degree + 1))) := by
          dsimp [shifted]
          simp [inputCode, BootstrappingCorrectness.encodeBit, Int.cast_add]
        have hexponent :
            ((RotationLookup.exactRoundExponent degree
              (inputCode degree true +
                (value : ZMod (2 * (degree + 1))))).val : ℤ) = shifted := by
          rw [exactRoundExponent_val, hphase]
          exact val_intCast_eq_of_nonneg_of_lt shifted hshiftedNonneg hshiftedLt
        apply antiPeriodicThreshold_eq_true_of_secondLow degree
        · dsimp [shifted] at hexponent
          omega
        · dsimp [shifted] at hexponent
          omega
      · have hnegative : value < 0 := lt_of_not_ge hnonneg
        have hlower : -value ≤ (eta : ℤ) := by
          simpa [abs_of_neg hnegative] using hvalue
        let shifted : ℤ := (degree + 1 : ℕ) + value
        have hshiftedNonneg : 0 ≤ shifted := by
          dsimp [shifted]
          omega
        have hshiftedLt : shifted < (2 * (degree + 1) : ℕ) := by
          dsimp [shifted]
          omega
        have hphase :
            inputCode degree true + (value : ZMod (2 * (degree + 1))) =
              (shifted : ZMod (2 * (degree + 1))) := by
          dsimp [shifted]
          simp [inputCode, BootstrappingCorrectness.encodeBit, Int.cast_add]
        have hexponent :
            ((RotationLookup.exactRoundExponent degree
              (inputCode degree true +
                (value : ZMod (2 * (degree + 1))))).val : ℤ) = shifted := by
          rw [exactRoundExponent_val, hphase]
          exact val_intCast_eq_of_nonneg_of_lt shifted hshiftedNonneg hshiftedLt
        apply antiPeriodicThreshold_eq_true_of_firstHigh degree
        · dsimp [shifted] at hexponent
          omega
        · dsimp [shifted] at hexponent
          omega

/-- The signed-lift formulation used by the concrete scalar centered-binomial sampler implies the
same threshold classification result. -/
theorem antiPeriodicThreshold_inputCode_add_of_scalarBounded
    (degree eta : ℕ) (bit : Bool) (error : ZMod (2 * (degree + 1)))
    (herror : CenteredBinomial.ScalarBounded eta error)
    (hmargin : 2 * eta < degree + 1) :
    RotationLookup.antiPeriodicBit (firstHalfThreshold degree)
        (RotationLookup.exactRoundExponent degree (inputCode degree bit + error)) = bit := by
  obtain ⟨value, hvalue, rfl⟩ := herror
  exact antiPeriodicThreshold_inputCode_add_intCast degree eta bit value hvalue hmargin

/-! ## Fresh TLWE encryption support -/

/-- A fresh scalar TLWE ciphertext in support has phase equal to its encoded input plus an error
from the configured scalar sampler. -/
theorem phase_eq_inputCode_add_error_of_mem_support_encrypt
    {degree lweDimension eta : ℕ}
    (lweSecret : BinarySecret lweDimension) (bit : Bool)
    {input : ScalarCiphertext (2 * (degree + 1)) lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt (2 * (degree + 1)) lweDimension
        (CenteredBinomial.scalarSampler (2 * (degree + 1)) eta)
        (inputCode degree) lweSecret bit)) :
    ∃ error ∈ support
        (CenteredBinomial.scalarSampler (2 * (degree + 1)) eta),
      TLWE.phase (embedBinarySecret lweSecret) input = inputCode degree bit + error := by
  unfold Encryption.encrypt TLWE.encrypt at hinput
  rw [mem_support_bind_iff] at hinput
  obtain ⟨mask, _, hinput⟩ := hinput
  rw [mem_support_bind_iff] at hinput
  obtain ⟨error, herror, hinput⟩ := hinput
  simp only [support_pure, Set.mem_singleton_iff] at hinput
  subst input
  exact ⟨error, herror, TLWE.phase_assemble _ _ _ _⟩

/-- Every fresh centered-binomial encryption in support is recognized as its source Boolean by
the exact anti-periodic threshold lookup. -/
theorem bitTableExpectedResult_eq_of_mem_support_encrypt
    {degree lweDimension eta : ℕ}
    (lweSecret : BinarySecret lweDimension) (bit : Bool)
    {input : ScalarCiphertext (2 * (degree + 1)) lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt (2 * (degree + 1)) lweDimension
        (CenteredBinomial.scalarSampler (2 * (degree + 1)) eta)
        (inputCode degree) lweSecret bit))
    (hmargin : 2 * eta < degree + 1) :
    CenteredBinomialCorrectness.bitTableExpectedResult input lweSecret
        (firstHalfThreshold degree) = bit := by
  obtain ⟨error, herror, hphase⟩ :=
    phase_eq_inputCode_add_error_of_mem_support_encrypt lweSecret bit hinput
  unfold CenteredBinomialCorrectness.bitTableExpectedResult
  rw [hphase]
  exact antiPeriodicThreshold_inputCode_add_of_scalarBounded degree eta bit error
    (CenteredBinomial.scalarBounded_of_mem_support herror) hmargin

/-- Fresh centered-binomial input encryption is classified correctly with probability one. -/
theorem probEvent_bitTableExpectedResult_eq_one
    {degree lweDimension eta : ℕ}
    (lweSecret : BinarySecret lweDimension) (bit : Bool)
    (hmargin : 2 * eta < degree + 1) :
    Pr[(fun input ↦
      CenteredBinomialCorrectness.bitTableExpectedResult input lweSecret
          (firstHalfThreshold degree) = bit) |
      Encryption.encrypt (2 * (degree + 1)) lweDimension
        (CenteredBinomial.scalarSampler (2 * (degree + 1)) eta)
        (inputCode degree) lweSecret bit] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp
  · intro input hinput
    exact bitTableExpectedResult_eq_of_mem_support_encrypt lweSecret bit hinput hmargin

/-! ## Fresh-input bootstrapping correctness -/

/-- A fresh centered-binomial input together with an independently generated centered-binomial
bootstrapping key.  This is the concrete sampling experiment used by the final probability-one
refresh theorem. -/
noncomputable def freshInputAndBootstrappingKey
    {degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (inputEta bootstrappingEta : ℕ)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1)) (bit : Bool) :
    ProbComp
      (ScalarCiphertext (2 * (degree + 1)) lweDimension ×
        Native.BootstrappingKey (2 * (degree + 1)) (degree + 1) rank
          params.levels lweDimension) := do
  let input ← Encryption.encrypt (2 * (degree + 1)) lweDimension
    (CenteredBinomial.scalarSampler (2 * (degree + 1)) inputEta)
    (inputCode degree) lweSecret bit
  let bootstrappingKey ← Native.generateBootstrappingKey
    (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler
      (2 * (degree + 1)) (degree + 1) bootstrappingEta)
    (Gadget.Base.ringGadget params) lweSecret ringSecret
  return (input, bootstrappingKey)

/-- Support-wise correctness of a complete fresh Boolean refresh: bounded input noise selects the
intended table region, and bounded bootstrapping-key noise preserves the selected output codeword. -/
theorem bitTableBootstrappingResult_eq_bit_of_mem_support
    {degree rank lweDimension inputEta bootstrappingEta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1))) (bit : Bool)
    {input : ScalarCiphertext (2 * (degree + 1)) lweDimension}
    {bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt (2 * (degree + 1)) lweDimension
        (CenteredBinomial.scalarSampler (2 * (degree + 1)) inputEta)
        (inputCode degree) lweSecret bit))
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey
        (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler
          (2 * (degree + 1)) (degree + 1) bootstrappingEta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret))
    (hopposite : oneCode = -zeroCode)
    (hinputMargin : 2 * inputEta < degree + 1)
    (houtputMargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension bootstrappingEta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    CenteredBinomialCorrectness.bitTableBootstrappingResult params input bootstrappingKey
        ringSecret zeroCode oneCode (firstHalfThreshold degree) = bit := by
  calc
    CenteredBinomialCorrectness.bitTableBootstrappingResult params input bootstrappingKey
        ringSecret zeroCode oneCode (firstHalfThreshold degree) =
        CenteredBinomialCorrectness.bitTableExpectedResult input lweSecret
          (firstHalfThreshold degree) :=
      CenteredBinomialCorrectness.bitTableBootstrappingResult_eq_of_mem_support
        params input lweSecret ringSecret zeroCode oneCode (firstHalfThreshold degree)
        hkey hopposite houtputMargin
    _ = bit :=
      bitTableExpectedResult_eq_of_mem_support_encrypt lweSecret bit hinput hinputMargin

/-- Support-wise correctness of a complete fresh Boolean refresh under the sharp linear
signed-rotation budget.  Exact native rotations preserve coefficient infinity norm, so every
historical row error is charged once rather than multiplied by a geometric propagation factor. -/
theorem bitTableBootstrappingResult_eq_bit_of_mem_support_linear
    {degree rank lweDimension inputEta bootstrappingEta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1))) (bit : Bool)
    {input : ScalarCiphertext (2 * (degree + 1)) lweDimension}
    {bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt (2 * (degree + 1)) lweDimension
        (CenteredBinomial.scalarSampler (2 * (degree + 1)) inputEta)
        (inputCode degree) lweSecret bit))
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey
        (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler
          (2 * (degree + 1)) (degree + 1) bootstrappingEta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret))
    (hopposite : oneCode = -zeroCode)
    (hinputMargin : 2 * inputEta < degree + 1)
    (houtputMargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension bootstrappingEta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    CenteredBinomialCorrectness.bitTableBootstrappingResult params input bootstrappingKey
        ringSecret zeroCode oneCode (firstHalfThreshold degree) = bit := by
  calc
    CenteredBinomialCorrectness.bitTableBootstrappingResult params input bootstrappingKey
        ringSecret zeroCode oneCode (firstHalfThreshold degree) =
        CenteredBinomialCorrectness.bitTableExpectedResult input lweSecret
          (firstHalfThreshold degree) :=
      CenteredBinomialCorrectness.bitTableBootstrappingResult_eq_of_mem_support_linear
        params input lweSecret ringSecret zeroCode oneCode (firstHalfThreshold degree)
        hkey hopposite houtputMargin
    _ = bit :=
      bitTableExpectedResult_eq_of_mem_support_encrypt lweSecret bit hinput hinputMargin

/-- **Complete concrete fresh TFHE refresh correctness.** Independently sampling both the fresh
centered-binomial input ciphertext and the centered-binomial bootstrapping key produces the source
Boolean after native blind rotation, sample extraction, and nearest-codeword decoding with
probability one, under the two explicit public margin inequalities. -/
theorem probEvent_fresh_bitTableBootstrappingResult_eq_one
    {degree rank lweDimension inputEta bootstrappingEta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1))) (bit : Bool)
    (hopposite : oneCode = -zeroCode)
    (hinputMargin : 2 * inputEta < degree + 1)
    (houtputMargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension bootstrappingEta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    Pr[(fun sample ↦
      CenteredBinomialCorrectness.bitTableBootstrappingResult params sample.1 sample.2
          ringSecret zeroCode oneCode (firstHalfThreshold degree) = bit) |
      freshInputAndBootstrappingKey params inputEta bootstrappingEta
        lweSecret ringSecret bit] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp [freshInputAndBootstrappingKey]
  · intro sample hsample
    unfold freshInputAndBootstrappingKey at hsample
    rw [mem_support_bind_iff] at hsample
    obtain ⟨input, hinput, hsample⟩ := hsample
    rw [mem_support_bind_iff] at hsample
    obtain ⟨bootstrappingKey, hkey, hsample⟩ := hsample
    simp only [support_pure, Set.mem_singleton_iff] at hsample
    subst sample
    exact bitTableBootstrappingResult_eq_bit_of_mem_support params lweSecret ringSecret
      zeroCode oneCode bit hinput hkey hopposite hinputMargin houtputMargin

/-- **Complete fresh TFHE refresh correctness with linear rotation-noise accumulation.**
Independently sampling both centered-binomial objects returns the source Boolean with probability
one whenever the input margin and the sharp linear output margin hold. -/
theorem probEvent_fresh_bitTableBootstrappingResult_eq_one_linear
    {degree rank lweDimension inputEta bootstrappingEta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1))) (bit : Bool)
    (hopposite : oneCode = -zeroCode)
    (hinputMargin : 2 * inputEta < degree + 1)
    (houtputMargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension bootstrappingEta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    Pr[(fun sample ↦
      CenteredBinomialCorrectness.bitTableBootstrappingResult params sample.1 sample.2
          ringSecret zeroCode oneCode (firstHalfThreshold degree) = bit) |
      freshInputAndBootstrappingKey params inputEta bootstrappingEta
        lweSecret ringSecret bit] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp [freshInputAndBootstrappingKey]
  · intro sample hsample
    unfold freshInputAndBootstrappingKey at hsample
    rw [mem_support_bind_iff] at hsample
    obtain ⟨input, hinput, hsample⟩ := hsample
    rw [mem_support_bind_iff] at hsample
    obtain ⟨bootstrappingKey, hkey, hsample⟩ := hsample
    simp only [support_pure, Set.mem_singleton_iff] at hsample
    subst sample
    exact bitTableBootstrappingResult_eq_bit_of_mem_support_linear params lweSecret ringSecret
      zeroCode oneCode bit hinput hkey hopposite hinputMargin houtputMargin

end

end FormalProof4FHE.TFHE.CenteredBinomialRefresh
