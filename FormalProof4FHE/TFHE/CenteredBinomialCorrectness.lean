/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialInstantiation
import FormalProof4FHE.TFHE.RotationLookup

/-!
# Centered-Binomial TFHE Bootstrapping Correctness

This file derives the deterministic bootstrapping-key row hypothesis used by
`TFHE.RotationLookup` from the support of the executable centered-binomial key generator.  Since
centered-binomial noise has bounded support, the resulting correctness event holds with
probability one whenever the public decoding margin holds.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.CenteredBinomialCorrectness

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- A coefficient-bounded ring error has centered coefficient infinity norm at most its width. -/
theorem cInfNorm_le_of_coeffBounded {q degree eta : ℕ} [NeZero q]
    {error : RLWE.Rq q (degree + 1)}
    (herror : RLWE.CenteredBinomial.CoeffBounded eta error) :
    LatticeCrypto.cInfNorm error ≤ eta := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  obtain ⟨value, hvalue, hcoefficient⟩ := herror coefficient
  have hnatAbs : value.natAbs ≤ eta := by
    have hcast : (value.natAbs : ℤ) ≤ (eta : ℤ) := by
      rw [← Int.natAbs_abs value, Int.natAbs_of_nonneg (abs_nonneg value)]
      exact hvalue
    exact Int.ofNat_le.mp hcast
  rw [hcoefficient]
  exact (NoiseBounds.centeredRepr_intCast_natAbs_le value).trans hnatAbs

/-- Every executable centered-binomial ring error in support has norm at most `eta`. -/
theorem cInfNorm_le_eta_of_mem_support {q degree eta : ℕ} [NeZero q]
    {error : RLWE.Rq q (degree + 1)}
    (herror : error ∈ support (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) :
    LatticeCrypto.cInfNorm error ≤ eta :=
  cInfNorm_le_of_coeffBounded
    (RLWE.CenteredBinomial.coeffBounded_of_mem_support herror)

/-! ## Support of structured TGSW encryption -/

/-- Coordinatewise support membership for an independent finite product. -/
theorem mem_support_fin_mOfFn_apply {Alpha : Type} (count : ℕ)
    (samplers : Fin count → ProbComp Alpha) (values : Fin count → Alpha)
    (hvalues : values ∈ support (Fin.mOfFn count samplers)) (coordinate : Fin count) :
    values coordinate ∈ support (samplers coordinate) := by
  induction count with
  | zero => exact coordinate.elim0
  | succ count ih =>
      rw [Fin.mOfFn, mem_support_bind_iff] at hvalues
      obtain ⟨head, hhead, hvalues⟩ := hvalues
      rw [mem_support_bind_iff] at hvalues
      obtain ⟨tail, htail, hvalues⟩ := hvalues
      simp only [support_pure, Set.mem_singleton_iff] at hvalues
      subst values
      refine Fin.cases ?_ (fun index ↦ ?_) coordinate
      · simpa using hhead
      · rw [Fin.cons_succ]
        exact ih (fun index ↦ samplers index.succ) tail htail index

/-- The row error of a structured TGSW encryption assembled from explicit homogeneous errors is
exactly the corresponding sampled error row. -/
@[simp]
theorem rowError_addGadget_batchAssemble {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (errors : Fin (TGSW.rowCount dimension levels) → R)
    (index : Fin (dimension + 1) × Fin levels) :
    TGSW.rowError secret gadget message
        (TGSW.addGadget gadget message
          (TLWE.batchAssemble secret challenge 0 errors)) index =
      errors (finProdFinEquiv index) := by
  unfold TGSW.rowError
  rw [TLWE.phase_entry, TGSW.batchPhase_addGadget,
    TLWE.batchPhase_batchAssemble]
  simp

/-- Every row error of a TGSW ciphertext in the support of `TGSW.encrypt` belongs to the original
one-row error sampler support. -/
theorem rowError_mem_support_of_mem_support_encrypt
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {dimension levels : ℕ}
    (errorSampler : ProbComp R)
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    {ciphertext : TGSW.Ciphertext R dimension levels}
    (hciphertext : ciphertext ∈ support
      (TGSW.encrypt dimension levels errorSampler secret gadget message))
    (index : Fin (dimension + 1) × Fin levels) :
    TGSW.rowError secret gadget message ciphertext index ∈ support errorSampler := by
  unfold TGSW.encrypt at hciphertext
  rw [mem_support_bind_iff] at hciphertext
  obtain ⟨homogeneous, hhomogeneous, hciphertext⟩ := hciphertext
  simp only [support_pure, Set.mem_singleton_iff] at hciphertext
  subst ciphertext
  unfold TLWE.batchEncrypt at hhomogeneous
  rw [mem_support_bind_iff] at hhomogeneous
  obtain ⟨challenge, _, hhomogeneous⟩ := hhomogeneous
  rw [mem_support_bind_iff] at hhomogeneous
  obtain ⟨errors, herrors, hhomogeneous⟩ := hhomogeneous
  simp only [support_pure, Set.mem_singleton_iff] at hhomogeneous
  subst homogeneous
  rw [rowError_addGadget_batchAssemble]
  exact mem_support_fin_mOfFn_apply (TGSW.rowCount dimension levels)
    (fun _ ↦ errorSampler) errors herrors (finProdFinEquiv index)

/-! ## Native bootstrapping-key row bounds -/

/-- Support membership of a native bootstrapping key projects to support membership of every
coordinate TGSW encryption. -/
theorem bootstrappingKey_apply_mem_support
    {q degree rank levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    {bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey q (degree + 1) rank levels lweDimension
        errorSampler gadget lweSecret ringSecret))
    (coordinate : Fin lweDimension) :
    bootstrappingKey coordinate ∈ support
      (TGSW.encrypt rank levels errorSampler (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (degree + 1) (lweSecret coordinate))) := by
  unfold Native.generateBootstrappingKey at hkey
  exact mem_support_fin_mOfFn_apply lweDimension
    (fun index ↦ TGSW.encrypt rank levels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q (degree + 1) (lweSecret index)))
    bootstrappingKey hkey coordinate

/-- Every native bootstrapping-key row error remains in the one-row sampler support. -/
theorem bootstrappingKey_rowError_mem_support
    {q degree rank levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    {bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey q (degree + 1) rank levels lweDimension
        errorSampler gadget lweSecret ringSecret))
    (coordinate : Fin lweDimension)
    (index : Fin (rank + 1) × Fin levels) :
    TGSW.rowError (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (degree + 1) (lweSecret coordinate))
        (bootstrappingKey coordinate) index ∈ support errorSampler := by
  apply rowError_mem_support_of_mem_support_encrypt errorSampler
    (embedRingSecret q ringSecret) gadget
      (embedConstantBit q (degree + 1) (lweSecret coordinate))
  exact bootstrappingKey_apply_mem_support errorSampler gadget lweSecret ringSecret
    hkey coordinate

/-- A native BRK generated with centered-binomial ring noise satisfies every deterministic row
bound required by the blind-rotation correctness theorem. -/
theorem cInfNorm_bootstrappingKey_rowError_le_eta
    {q degree rank levels lweDimension eta : ℕ} [NeZero q]
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    {bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey q (degree + 1) rank levels lweDimension
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        gadget lweSecret ringSecret))
    (coordinate : Fin lweDimension)
    (index : Fin (rank + 1) × Fin levels) :
    LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1))
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ eta := by
  apply cInfNorm_le_eta_of_mem_support
  exact bootstrappingKey_rowError_mem_support
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) gadget
      lweSecret ringSecret hkey coordinate index

/-! ## Concrete support-wise and probability-one correctness -/

/-- The decoded output of the exact-`q = 2N` Boolean-table bootstrapping evaluator. -/
noncomputable def bitTableBootstrappingResult
    {degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool) : Bool :=
  BootstrappingCorrectness.decodeNearest zeroCode oneCode
    (TLWE.phase
      (SampleExtraction.extractedSecret
        (embedRingSecret (2 * (degree + 1)) ringSecret))
      (SampleExtraction.apply
        (BlindRotation.nativeBlindRotate params
          (RotationLookup.exactRoundExponent degree) input bootstrappingKey
          (RotationLookup.testVectorAccumulator
            (RotationLookup.exactRoundExponent degree input.body)
            (RotationLookup.bitTableTestVector zeroCode oneCode firstHalfBit)))))

/-- Expected anti-periodic table output at the exact scalar TLWE phase. -/
def bitTableExpectedResult {degree lweDimension : ℕ}
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (firstHalfBit : Fin (degree + 1) → Bool) : Bool :=
  RotationLookup.antiPeriodicBit firstHalfBit
    (RotationLookup.exactRoundExponent degree
      (TLWE.phase (embedBinarySecret lweSecret) input))

/-- Every centered-binomial BRK in generator support evaluates the concrete Boolean table
correctly, provided the public deterministic decoding margin holds. -/
theorem bitTableBootstrappingResult_eq_of_mem_support
    {degree rank lweDimension eta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool)
    {bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey
        (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler
          (2 * (degree + 1)) (degree + 1) eta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret))
    (hopposite : oneCode = -zeroCode)
    (hmargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension eta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    bitTableBootstrappingResult params input bootstrappingKey ringSecret
        zeroCode oneCode firstHalfBit =
      bitTableExpectedResult input lweSecret firstHalfBit := by
  unfold bitTableBootstrappingResult bitTableExpectedResult
  apply RotationLookup.decode_nativeBlindRotate_apply_bitTable params input
    bootstrappingKey lweSecret
      (embedRingSecret (2 * (degree + 1)) ringSecret)
    zeroCode oneCode firstHalfBit eta hopposite
  · intro coordinate index
    exact cInfNorm_bootstrappingKey_rowError_le_eta
      (Gadget.Base.ringGadget params) lweSecret ringSecret hkey coordinate index
  · exact hmargin

/-- Support-wise centered-binomial Boolean-table correctness under the sharp linear native
rotation budget. -/
theorem bitTableBootstrappingResult_eq_of_mem_support_linear
    {degree rank lweDimension eta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool)
    {bootstrappingKey : Native.BootstrappingKey
      (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension}
    (hkey : bootstrappingKey ∈ support
      (Native.generateBootstrappingKey
        (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler
          (2 * (degree + 1)) (degree + 1) eta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret))
    (hopposite : oneCode = -zeroCode)
    (hmargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension eta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    bitTableBootstrappingResult params input bootstrappingKey ringSecret
        zeroCode oneCode firstHalfBit =
      bitTableExpectedResult input lweSecret firstHalfBit := by
  unfold bitTableBootstrappingResult bitTableExpectedResult
  apply RotationLookup.decode_nativeBlindRotate_apply_bitTable_linear params input
    bootstrappingKey lweSecret
      (embedRingSecret (2 * (degree + 1)) ringSecret)
    zeroCode oneCode firstHalfBit eta hopposite
  · intro coordinate index
    exact cInfNorm_bootstrappingKey_rowError_le_eta
      (Gadget.Base.ringGadget params) lweSecret ringSecret hkey coordinate index
  · exact hmargin

/-- Centered-binomial BRK generation satisfies the concrete Boolean-table correctness event with
probability one.  Bounded support removes a separate tail-probability loss. -/
theorem probEvent_bitTableBootstrappingResult_eq_one
    {degree rank lweDimension eta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool)
    (hopposite : oneCode = -zeroCode)
    (hmargin :
      2 * BootstrappingCorrectness.nativeNoiseBudget degree rank params.levels params.base
          lweDimension eta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    Pr[(fun bootstrappingKey ↦
      bitTableBootstrappingResult params input bootstrappingKey ringSecret
          zeroCode oneCode firstHalfBit =
        bitTableExpectedResult input lweSecret firstHalfBit) |
      Native.generateBootstrappingKey
        (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler
          (2 * (degree + 1)) (degree + 1) eta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp
  · intro bootstrappingKey hkey
    exact bitTableBootstrappingResult_eq_of_mem_support params input lweSecret ringSecret
      zeroCode oneCode firstHalfBit hkey hopposite hmargin

/-- Probability-one centered-binomial BRK correctness under the sharp linear rotation budget. -/
theorem probEvent_bitTableBootstrappingResult_eq_one_linear
    {degree rank lweDimension eta : ℕ}
    (params : Gadget.Base.Parameters (2 * (degree + 1)))
    (input : ScalarCiphertext (2 * (degree + 1)) lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret rank (degree + 1))
    (zeroCode oneCode : ZMod (2 * (degree + 1)))
    (firstHalfBit : Fin (degree + 1) → Bool)
    (hopposite : oneCode = -zeroCode)
    (hmargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension eta <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    Pr[(fun bootstrappingKey ↦
      bitTableBootstrappingResult params input bootstrappingKey ringSecret
          zeroCode oneCode firstHalfBit =
        bitTableExpectedResult input lweSecret firstHalfBit) |
      Native.generateBootstrappingKey
        (2 * (degree + 1)) (degree + 1) rank params.levels lweDimension
        (RLWE.CenteredBinomial.sampler
          (2 * (degree + 1)) (degree + 1) eta)
        (Gadget.Base.ringGadget params) lweSecret ringSecret] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp
  · intro bootstrappingKey hkey
    exact bitTableBootstrappingResult_eq_of_mem_support_linear params input
      lweSecret ringSecret zeroCode oneCode firstHalfBit hkey hopposite hmargin

end


end FormalProof4FHE.TFHE.CenteredBinomialCorrectness
