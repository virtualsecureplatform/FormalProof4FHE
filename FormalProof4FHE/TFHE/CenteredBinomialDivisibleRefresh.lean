/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialRefresh
import FormalProof4FHE.TFHE.DivisibleModulusRotation

/-!
# Centered-Binomial Refresh at a Larger Divisible Modulus

This module lifts the complete fresh Boolean refresh theorem from the special coefficient modulus
`q = 2N` to any nonzero `q` divisible by `2N`.  Input phases still reduce to the same antipodal
rotation exponents, while output codewords may use the much larger coefficient distance in
`ZMod q`.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomialDivisibleRefresh

noncomputable section

/-- Boolean input codes whose images modulo `2N` are the exact antipodal rotation exponents. -/
def inputCode (q degree : ℕ) (bit : Bool) : ZMod q :=
  BootstrappingCorrectness.encodeBit 0 (degree + 1) bit

/-- Divisible-modulus reduction preserves the public Boolean input code. -/
theorem castHom_inputCode {q degree : ℕ}
    (hdiv : 2 * (degree + 1) ∣ q) (bit : Bool) :
    ZMod.castHom hdiv (ZMod (2 * (degree + 1))) (inputCode q degree bit) =
      CenteredBinomialRefresh.inputCode degree bit := by
  cases bit with
  | false =>
      simp [inputCode, CenteredBinomialRefresh.inputCode,
        BootstrappingCorrectness.encodeBit]
  | true =>
      simp only [inputCode, CenteredBinomialRefresh.inputCode,
        BootstrappingCorrectness.encodeBit, if_true]
      simpa using
        map_natCast (ZMod.castHom hdiv (ZMod (2 * (degree + 1)))) (degree + 1)

/-- Casting a bounded centered-binomial error to the rotation modulus preserves its signed lift. -/
theorem scalarBounded_castHom {q degree eta : ℕ}
    (hdiv : 2 * (degree + 1) ∣ q) (error : ZMod q)
    (herror : CenteredBinomial.ScalarBounded eta error) :
    CenteredBinomial.ScalarBounded eta
      (ZMod.castHom hdiv (ZMod (2 * (degree + 1))) error) := by
  obtain ⟨value, hvalue, rfl⟩ := herror
  exact ⟨value, hvalue, by simp⟩

/-- The existing anti-periodic threshold recognizes the reduced phase of any bounded fresh input
error. -/
theorem antiPeriodicThreshold_inputCode_add_of_scalarBounded
    {q : ℕ} (degree eta : ℕ)
    (hdiv : 2 * (degree + 1) ∣ q)
    (bit : Bool) (error : ZMod q)
    (herror : CenteredBinomial.ScalarBounded eta error)
    (hmargin : 2 * eta < degree + 1) :
    RotationLookup.antiPeriodicBit
        (CenteredBinomialRefresh.firstHalfThreshold degree)
        (RotationLookup.divisibleRoundExponent hdiv
          (inputCode q degree bit + error)) = bit := by
  change RotationLookup.antiPeriodicBit
      (CenteredBinomialRefresh.firstHalfThreshold degree)
      (RotationLookup.exactRoundExponent degree
        (ZMod.castHom hdiv (ZMod (2 * (degree + 1)))
          (inputCode q degree bit + error))) = bit
  rw [map_add, castHom_inputCode]
  exact CenteredBinomialRefresh.antiPeriodicThreshold_inputCode_add_of_scalarBounded
    degree eta bit _ (scalarBounded_castHom hdiv error herror) hmargin

/-! ## Evaluator and expected result -/

/-- Decoded Boolean-table bootstrapping result at a divisible coefficient modulus. -/
noncomputable def bitTableBootstrappingResult
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hdiv : 2 * (degree + 1) ∣ q)
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod q)
    (firstHalfBit : Fin (degree + 1) → Bool) : Bool :=
  BootstrappingCorrectness.decodeNearest zeroCode oneCode
    (TLWE.phase
      (SampleExtraction.extractedSecret (embedRingSecret q ringSecret))
      (SampleExtraction.apply
        (BlindRotation.nativeBlindRotate params
          (RotationLookup.divisibleRoundExponent hdiv) input bootstrappingKey
          (RotationLookup.testVectorAccumulator
            (RotationLookup.divisibleRoundExponent hdiv input.body)
            (RotationLookup.bitTableTestVector zeroCode oneCode firstHalfBit)))))

/-- Expected anti-periodic output at the exactly reduced scalar phase. -/
def bitTableExpectedResult
    {q degree lweDimension : ℕ}
    (hdiv : 2 * (degree + 1) ∣ q)
    (input : ScalarCiphertext q lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (firstHalfBit : Fin (degree + 1) → Bool) : Bool :=
  RotationLookup.antiPeriodicBit firstHalfBit
    (RotationLookup.divisibleRoundExponent hdiv
      (TLWE.phase (embedBinarySecret lweSecret) input))

/-- Every centered-binomial BRK in generator support evaluates the divisible-modulus table
correctly under the sharp deterministic margin. -/
theorem bitTableBootstrappingResult_eq_of_mem_support
    {q degree rank lweDimension eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hdiv : 2 * (degree + 1) ∣ q)
    (input : ScalarCiphertext q lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod q)
    (firstHalfBit : Fin (degree + 1) → Bool)
    {bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey q (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret))
    (hopposite : oneCode = -zeroCode)
    (hmargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension eta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    bitTableBootstrappingResult params hdiv input bootstrappingKey ringSecret
        zeroCode oneCode firstHalfBit =
      bitTableExpectedResult hdiv input lweSecret firstHalfBit := by
  unfold bitTableBootstrappingResult bitTableExpectedResult
  apply RotationLookup.decode_nativeBlindRotate_apply_bitTable_divisible_linear
    params hdiv input bootstrappingKey lweSecret (embedRingSecret q ringSecret)
    zeroCode oneCode firstHalfBit eta hopposite
  · intro coordinate index
    exact CenteredBinomialCorrectness.cInfNorm_bootstrappingKey_rowError_le_eta
      (Gadget.Base.ringGadget params) lweSecret ringSecret hkey coordinate index
  · exact hmargin

/-! ## Fresh-input support and complete refresh -/

/-- A fresh input in support has phase equal to its public divisible-modulus code plus a sampled
scalar error. -/
theorem phase_eq_inputCode_add_error_of_mem_support_encrypt
    {q degree lweDimension eta : ℕ} [NeZero q]
    (lweSecret : BinarySecret lweDimension) (bit : Bool)
    {input : ScalarCiphertext q lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt q lweDimension
        (CenteredBinomial.scalarSampler q eta)
        (inputCode q degree) lweSecret bit)) :
    ∃ error ∈ support (CenteredBinomial.scalarSampler q eta),
      TLWE.phase (embedBinarySecret lweSecret) input =
        inputCode q degree bit + error := by
  unfold Encryption.encrypt TLWE.encrypt at hinput
  rw [mem_support_bind_iff] at hinput
  obtain ⟨mask, _, hinput⟩ := hinput
  rw [mem_support_bind_iff] at hinput
  obtain ⟨error, herror, hinput⟩ := hinput
  simp only [support_pure, Set.mem_singleton_iff] at hinput
  subst input
  exact ⟨error, herror, TLWE.phase_assemble _ _ _ _⟩

/-- Every supported fresh centered-binomial encryption reduces to its intended Boolean table
region. -/
theorem bitTableExpectedResult_eq_of_mem_support_encrypt
    {q degree lweDimension eta : ℕ} [NeZero q]
    (hdiv : 2 * (degree + 1) ∣ q)
    (lweSecret : BinarySecret lweDimension) (bit : Bool)
    {input : ScalarCiphertext q lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt q lweDimension
        (CenteredBinomial.scalarSampler q eta)
        (inputCode q degree) lweSecret bit))
    (hmargin : 2 * eta < degree + 1) :
    bitTableExpectedResult hdiv input lweSecret
        (CenteredBinomialRefresh.firstHalfThreshold degree) = bit := by
  obtain ⟨error, herror, hphase⟩ :=
    phase_eq_inputCode_add_error_of_mem_support_encrypt lweSecret bit hinput
  unfold bitTableExpectedResult
  rw [hphase]
  exact antiPeriodicThreshold_inputCode_add_of_scalarBounded degree eta hdiv bit error
    (CenteredBinomial.scalarBounded_of_mem_support herror) hmargin

/-- Fresh input and independently sampled BRK experiment at a divisible coefficient modulus. -/
noncomputable def freshInputAndBootstrappingKey
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (inputEta bootstrappingEta : ℕ)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1)) (bit : Bool) :
    ProbComp
      (ScalarCiphertext q lweDimension ×
        Native.BootstrappingKey q (degree + 1) rank
          params.levels lweDimension) := do
  let input ← Encryption.encrypt q lweDimension
    (CenteredBinomial.scalarSampler q inputEta)
    (inputCode q degree) lweSecret bit
  let bootstrappingKey ← Native.generateBootstrappingKey
    q (degree + 1) rank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) bootstrappingEta)
    (Gadget.Base.ringGadget params) lweSecret ringSecret
  return (input, bootstrappingKey)

/-- Support-wise complete fresh Boolean refresh at a larger divisible coefficient modulus. -/
theorem bitTableBootstrappingResult_eq_bit_of_mem_support
    {q degree rank lweDimension inputEta bootstrappingEta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hdiv : 2 * (degree + 1) ∣ q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod q) (bit : Bool)
    {input : ScalarCiphertext q lweDimension}
    {bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension}
    (hinput : input ∈ support
      (Encryption.encrypt q lweDimension
        (CenteredBinomial.scalarSampler q inputEta)
        (inputCode q degree) lweSecret bit))
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey q (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) bootstrappingEta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret))
    (hopposite : oneCode = -zeroCode)
    (hinputMargin : 2 * inputEta < degree + 1)
    (houtputMargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension bootstrappingEta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    bitTableBootstrappingResult params hdiv input bootstrappingKey ringSecret
        zeroCode oneCode (CenteredBinomialRefresh.firstHalfThreshold degree) = bit := by
  calc
    bitTableBootstrappingResult params hdiv input bootstrappingKey ringSecret
        zeroCode oneCode (CenteredBinomialRefresh.firstHalfThreshold degree) =
        bitTableExpectedResult hdiv input lweSecret
          (CenteredBinomialRefresh.firstHalfThreshold degree) :=
      bitTableBootstrappingResult_eq_of_mem_support params hdiv input lweSecret
        ringSecret zeroCode oneCode (CenteredBinomialRefresh.firstHalfThreshold degree)
        hkey hopposite houtputMargin
    _ = bit :=
      bitTableExpectedResult_eq_of_mem_support_encrypt hdiv lweSecret bit
        hinput hinputMargin

/-- **Complete probability-one fresh refresh at a divisible coefficient modulus.** -/
theorem probEvent_fresh_bitTableBootstrappingResult_eq_one
    {q degree rank lweDimension inputEta bootstrappingEta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hdiv : 2 * (degree + 1) ∣ q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod q) (bit : Bool)
    (hopposite : oneCode = -zeroCode)
    (hinputMargin : 2 * inputEta < degree + 1)
    (houtputMargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension bootstrappingEta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    Pr[(fun sample ↦
      bitTableBootstrappingResult params hdiv sample.1 sample.2 ringSecret
          zeroCode oneCode (CenteredBinomialRefresh.firstHalfThreshold degree) = bit) |
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
    exact bitTableBootstrappingResult_eq_bit_of_mem_support params hdiv
      lweSecret ringSecret zeroCode oneCode bit hinput hkey hopposite
      hinputMargin houtputMargin

end

end FormalProof4FHE.TFHE.CenteredBinomialDivisibleRefresh
