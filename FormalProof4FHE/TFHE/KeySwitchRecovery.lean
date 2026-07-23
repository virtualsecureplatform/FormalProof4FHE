/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BootstrappingCorrectness
import FormalProof4FHE.TFHE.CenteredBinomialInstantiation

/-!
# Recovering the Native TFHE Key-Switch Source Key

A real native key-switch key contains, for every source-key coordinate and gadget level, a fresh
TLWE encryption of the corresponding gadget-scaled source bit under the target key.  Consequently,
once the target key is known, any gadget level whose two codewords are separated by more than twice
the scalar error radius recovers every source bit by nearest-codeword decoding.

This observation is useful for the auxiliary-input CircLWE search problem: recovering the scalar
TFHE key is enough to recover the extracted ring key from the retained real KSK.  Thus the paired
search target does not require an independent randomization of all ring-key coefficients.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.KeySwitchRecovery

/-- Decrypt and decode one source-key coordinate from a selected native KSK gadget level. -/
noncomputable def recoverSourceBit
    {q targetDimension sourceDimension keySwitchLevels : ℕ} [NeZero q]
    (targetSecret : BinarySecret targetDimension)
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (keySwitchKey : Native.KeySwitchKey
      q targetDimension sourceDimension keySwitchLevels)
    (coordinate : Fin sourceDimension) : Bool :=
  BootstrappingCorrectness.decodeNearest 0 (gadget level)
    (TLWE.phase (embedBinarySecret targetSecret)
      (TLWE.entry keySwitchKey (finProdFinEquiv (coordinate, level))))

/-- Recover the complete binary source key from a native KSK once its target key is known. -/
noncomputable def recoverSourceSecret
    {q targetDimension sourceDimension keySwitchLevels : ℕ} [NeZero q]
    (targetSecret : BinarySecret targetDimension)
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (keySwitchKey : Native.KeySwitchKey
      q targetDimension sourceDimension keySwitchLevels) :
    BinarySecret sourceDimension :=
  fun coordinate ↦ recoverSourceBit targetSecret gadget level keySwitchKey coordinate

/-- Reassemble the recovered KSK source vector into the native vector-of-polynomials ring-key
layout. -/
noncomputable def recoverRingSecret
    {q targetDimension ringRank degree keySwitchLevels : ℕ} [NeZero q]
    (targetSecret : BinarySecret targetDimension)
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (keySwitchKey : Native.KeySwitchKey
      q targetDimension (ringRank * degree) keySwitchLevels) :
    RingBinarySecret ringRank degree :=
  keyUnextract (recoverSourceSecret targetSecret gadget level keySwitchKey)

/-- Complete a scalar-key candidate to the paired native secret by decrypting the retained KSK. -/
noncomputable def completeCandidate
    {q targetDimension ringRank degree keySwitchLevels : ℕ} [NeZero q]
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (keySwitchKey : Native.KeySwitchKey
      q targetDimension (ringRank * degree) keySwitchLevels)
    (candidate : BinarySecret targetDimension) :
    BinarySecret targetDimension × RingBinarySecret ringRank degree :=
  (candidate, recoverRingSecret candidate gadget level keySwitchKey)

/-- A scalar error with a centered integer lift in `[-eta, eta]` has centered modular distance at
most `eta` from zero. -/
theorem centeredDistance_zero_le_of_scalarBounded
    {q eta : ℕ} [NeZero q] {error : ZMod q}
    (herror : CenteredBinomial.ScalarBounded eta error) :
    BootstrappingCorrectness.centeredDistance error 0 ≤ eta := by
  obtain ⟨value, hvalue, rfl⟩ := herror
  have hnatAbs : value.natAbs ≤ eta := by
    have hcast : (value.natAbs : ℤ) ≤ (eta : ℤ) := by
      rw [← Int.natAbs_abs value, Int.natAbs_of_nonneg (abs_nonneg value)]
      exact hvalue
    exact Int.ofNat_le.mp hcast
  simpa [BootstrappingCorrectness.centeredDistance] using
    (NoiseBounds.centeredRepr_intCast_natAbs_le (q := q) value).trans hnatAbs

/-- Adding a bounded scalar error moves a codeword by at most the same centered radius. -/
theorem centeredDistance_add_le_of_scalarBounded
    {q eta : ℕ} [NeZero q] (message : ZMod q) {error : ZMod q}
    (herror : CenteredBinomial.ScalarBounded eta error) :
    BootstrappingCorrectness.centeredDistance (message + error) message ≤ eta := by
  simpa [BootstrappingCorrectness.centeredDistance] using
    centeredDistance_zero_le_of_scalarBounded herror

/-- Coordinatewise support membership for the independent product used by `sampleIID`. -/
theorem mem_support_mOfFn_apply {Alpha : Type} (count : ℕ)
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

/-- The phase of a selected deterministically assembled KSK row is its gadget-scaled source bit
plus the selected error. -/
theorem phase_entry_keySwitchBatchAssemble
    {q targetDimension sourceDimension keySwitchLevels : ℕ} [NeZero q]
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension)
    (gadget : Fin keySwitchLevels → ZMod q)
    (challenge : Matrix (Fin targetDimension)
      (Fin (sourceDimension * keySwitchLevels)) (ZMod q))
    (error : Fin (sourceDimension * keySwitchLevels) → ZMod q)
    (coordinate : Fin sourceDimension) (level : Fin keySwitchLevels) :
    TLWE.phase (embedBinarySecret targetSecret)
        (TLWE.entry
          (TLWE.batchAssemble (embedBinarySecret targetSecret) challenge
            (Native.keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret)
            error)
          (finProdFinEquiv (coordinate, level))) =
      embedBit (sourceSecret coordinate) * gadget level +
        error (finProdFinEquiv (coordinate, level)) := by
  rw [TLWE.phase_entry, TLWE.batchPhase_batchAssemble]
  simp only [Pi.add_apply, Native.keySwitchMessages_apply]

/-- **Support-wise native KSK source-key recovery.**

For executable centered-binomial scalar noise, every generated KSK in the sampler support reveals
its complete source key after the target key is supplied, provided one selected gadget level has
the usual strict nearest-codeword margin. -/
theorem recoverSourceSecret_eq_of_mem_support_generate_centeredBinomial
    {q targetDimension sourceDimension keySwitchLevels eta : ℕ} [NeZero q]
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension)
    {keySwitchKey : Native.KeySwitchKey
      q targetDimension sourceDimension keySwitchLevels}
    (hkey : keySwitchKey ∈ support
      (Native.generateKeySwitchKey q targetDimension sourceDimension keySwitchLevels
        (CenteredBinomial.scalarSampler q eta) gadget sourceSecret targetSecret))
    (hmargin : 2 * eta <
      BootstrappingCorrectness.centeredDistance 0 (gadget level)) :
    recoverSourceSecret targetSecret gadget level keySwitchKey = sourceSecret := by
  unfold Native.generateKeySwitchKey TLWE.batchEncrypt at hkey
  rw [mem_support_bind_iff] at hkey
  obtain ⟨challenge, _, hkey⟩ := hkey
  rw [mem_support_bind_iff] at hkey
  obtain ⟨errors, herrors, hkey⟩ := hkey
  simp only [support_pure, Set.mem_singleton_iff] at hkey
  subst keySwitchKey
  funext coordinate
  unfold recoverSourceSecret recoverSourceBit
  apply BootstrappingCorrectness.decodeNearest_encodeBit_of_distance_le
      0 (gadget level) _ eta (sourceSecret coordinate) hmargin
  have herror : errors (finProdFinEquiv (coordinate, level)) ∈
      support (CenteredBinomial.scalarSampler q eta) :=
    mem_support_mOfFn_apply (sourceDimension * keySwitchLevels)
      (fun _ ↦ CenteredBinomial.scalarSampler q eta) errors herrors
      (finProdFinEquiv (coordinate, level))
  rw [phase_entry_keySwitchBatchAssemble]
  have hcode :
      embedBit (R := ZMod q) (sourceSecret coordinate) * gadget level =
        BootstrappingCorrectness.encodeBit 0 (gadget level)
          (sourceSecret coordinate) := by
    cases sourceSecret coordinate <;>
      simp [embedBit, BootstrappingCorrectness.encodeBit]
  rw [hcode]
  exact centeredDistance_add_le_of_scalarBounded _
    (CenteredBinomial.scalarBounded_of_mem_support herror)

/-- Supplying the true scalar key to a supported centered-binomial KSK recovers the original
native ring key, not merely its flattened representation. -/
theorem recoverRingSecret_eq_of_mem_support_generate_centeredBinomial
    {q targetDimension ringRank degree keySwitchLevels eta : ℕ} [NeZero q]
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (ringSecret : RingBinarySecret ringRank degree)
    (targetSecret : BinarySecret targetDimension)
    {keySwitchKey : Native.KeySwitchKey
      q targetDimension (ringRank * degree) keySwitchLevels}
    (hkey : keySwitchKey ∈ support
      (Native.generateKeySwitchKey q targetDimension (ringRank * degree) keySwitchLevels
        (CenteredBinomial.scalarSampler q eta) gadget
        (keyExtract ringSecret) targetSecret))
    (hmargin : 2 * eta <
      BootstrappingCorrectness.centeredDistance 0 (gadget level)) :
    recoverRingSecret targetSecret gadget level keySwitchKey = ringSecret := by
  unfold recoverRingSecret
  rw [recoverSourceSecret_eq_of_mem_support_generate_centeredBinomial
    gadget level (keyExtract ringSecret) targetSecret hkey hmargin]
  exact keyUnextract_keyExtract ringSecret

/-- On every supported real KSK, completing a scalar candidate gives the exact paired native
secret if and only if that scalar candidate is correct. -/
theorem completeCandidate_eq_iff_of_mem_support_generate_centeredBinomial
    {q targetDimension ringRank degree keySwitchLevels eta : ℕ} [NeZero q]
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (ringSecret : RingBinarySecret ringRank degree)
    (targetSecret candidate : BinarySecret targetDimension)
    {keySwitchKey : Native.KeySwitchKey
      q targetDimension (ringRank * degree) keySwitchLevels}
    (hkey : keySwitchKey ∈ support
      (Native.generateKeySwitchKey q targetDimension (ringRank * degree) keySwitchLevels
        (CenteredBinomial.scalarSampler q eta) gadget
        (keyExtract ringSecret) targetSecret))
    (hmargin : 2 * eta <
      BootstrappingCorrectness.centeredDistance 0 (gadget level)) :
    completeCandidate gadget level keySwitchKey candidate = (targetSecret, ringSecret) ↔
      candidate = targetSecret := by
  constructor
  · intro heq
    exact congrArg Prod.fst heq
  · intro heq
    subst candidate
    apply Prod.ext
    · rfl
    · exact recoverRingSecret_eq_of_mem_support_generate_centeredBinomial
        gadget level ringSecret targetSecret hkey hmargin

/-- Centered-binomial KSK generation recovers the complete source key with probability one under
the same public gadget-separation margin. -/
theorem probEvent_recoverSourceSecret_eq_one
    {q targetDimension sourceDimension keySwitchLevels eta : ℕ} [NeZero q]
    (gadget : Fin keySwitchLevels → ZMod q) (level : Fin keySwitchLevels)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : BinarySecret targetDimension)
    (hmargin : 2 * eta <
      BootstrappingCorrectness.centeredDistance 0 (gadget level)) :
    Pr[(fun keySwitchKey ↦
        recoverSourceSecret targetSecret gadget level keySwitchKey = sourceSecret) |
      Native.generateKeySwitchKey q targetDimension sourceDimension keySwitchLevels
        (CenteredBinomial.scalarSampler q eta) gadget sourceSecret targetSecret] = 1 := by
  rw [probEvent_eq_one_iff]
  constructor
  · simp [Native.generateKeySwitchKey, TLWE.batchEncrypt]
  · intro keySwitchKey hkey
    exact recoverSourceSecret_eq_of_mem_support_generate_centeredBinomial
      gadget level sourceSecret targetSecret hkey hmargin

end FormalProof4FHE.TFHE.Native.KeySwitchRecovery
