/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedUniform
import FormalProof4FHE.LWE.BlockBinaryReduction
import FormalProof4FHE.TFHE.NoiseBounds
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Uniform interval errors with finite-budget sampling

Exact modular interval errors use a ticket in Fin (2*radius+1). A cyclic
ticket coupling proves unit-shift TV at most 1/(2*radius+1), independently
of the coefficient modulus. Repeated shifts and centered integer lifts give
the arbitrary-shift bound used by the ordinary-LWE small-secret reduction.
The executable finite-budget sampler is compared with that exact law; its
support remains bounded even on rejection-budget exhaustion.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.UniformInterval

def value (q radius : ℕ) [NeZero q] (ticket : Fin (2 * radius + 1)) : ZMod q :=
  (ticket.val : ZMod q) - radius

def draw (q radius : ℕ) [NeZero q] : ProbComp (ZMod q) :=
  value q radius <$> ($ᵗ Fin (2 * radius + 1))

theorem value_rotate_of_ne_last (q radius : ℕ) [NeZero q]
    (ticket : Fin (2 * radius + 1)) (h : ticket ≠ Fin.last (2 * radius)) :
    value q radius (finRotate (2 * radius + 1) ticket) = 1 + value q radius ticket := by
  unfold value
  rw [coe_finRotate_of_ne_last h]
  push_cast
  ring

/-- One disagreeing ticket suffices; the bound does not require an injective modular map. -/
theorem unit_shift_le (q radius : ℕ) [NeZero q] :
    FiniteProduct.addShiftDistance (draw q radius) 1 ≤ 1 / (2 * radius + 1 : ℝ) := by
  let tickets : ProbComp (Fin (2 * radius + 1)) := $ᵗ _
  let left := fun ticket ↦ (pure (1 + value q radius ticket) : ProbComp (ZMod q))
  let right := fun ticket ↦ (pure (value q radius (finRotate (2 * radius + 1) ticket)) :
    ProbComp (ZMod q))
  have hrotate : 𝒟[tickets >>= right] = 𝒟[draw q radius] := by
    have h := evalDist_map_bijective_uniform_cross
      (α := Fin (2 * radius + 1)) (β := Fin (2 * radius + 1))
      (finRotate (2 * radius + 1)) (finRotate (2 * radius + 1)).bijective
    have hm := evalDist_map_eq_of_evalDist_eq h (value q radius)
    simpa [tickets, right, draw, monad_norm] using hm
  have hpoint (ticket : Fin (2 * radius + 1)) :
      tvDist (left ticket) (right ticket) ≤
        if ticket = Fin.last (2 * radius) then 1 else 0 := by
    by_cases h : ticket = Fin.last (2 * radius)
    · rw [if_pos h]
      exact tvDist_le_one _ _
    · rw [if_neg h]
      simp only [left, right, value_rotate_of_ne_last q radius ticket h, tvDist_self]
      exact le_rfl
  calc
    _ = tvDist (tickets >>= left) (tickets >>= right) := by
      unfold FiniteProduct.addShiftDistance tvDist
      rw [hrotate]
      simp [draw, tickets, left, monad_norm]
    _ ≤ ∑' ticket, Pr[= ticket | tickets].toReal * tvDist (left ticket) (right ticket) :=
      tvDist_bind_left_le tickets left right
    _ ≤ ∑' ticket, Pr[= ticket | tickets].toReal *
        (if ticket = Fin.last (2 * radius) then 1 else 0) := by
      rw [tsum_fintype, tsum_fintype]
      apply Finset.sum_le_sum
      intro ticket _
      exact mul_le_mul_of_nonneg_left (hpoint ticket) ENNReal.toReal_nonneg
    _ = _ := by
      simp [tickets, tsum_fintype, probOutput_uniformSample, Fintype.card_fin,
        ENNReal.toReal_inv]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
      norm_num

theorem shift_neg {R : Type} [AddCommGroup R] (sampler : ProbComp R) (shift : R) :
    FiniteProduct.addShiftDistance sampler (-shift) =
      FiniteProduct.addShiftDistance sampler shift := by
  have h (shift : R) : FiniteProduct.addShiftDistance sampler shift ≤
      FiniteProduct.addShiftDistance sampler (-shift) := by
    have hm := tvDist_map_le (fun value : R ↦ shift + value)
      ((fun value : R ↦ -shift + value) <$> sampler) sampler
    simpa [FiniteProduct.addShiftDistance, Functor.map_map, Function.comp_def,
      add_assoc, tvDist_comm] using hm
  exact le_antisymm (by simpa using h (-shift)) (h shift)

theorem shift_nsmul_le {R : Type} [AddCommGroup R]
    (sampler : ProbComp R) (shift : R) (count : ℕ) :
    FiniteProduct.addShiftDistance sampler (count • shift) ≤
      (count : ℝ) * FiniteProduct.addShiftDistance sampler shift := by
  induction count with
  | zero => simp
  | succ count ih =>
    calc
      _ = FiniteProduct.addShiftDistance sampler (count • shift + shift) := by
        rw [add_nsmul, one_nsmul]
      _ ≤ FiniteProduct.addShiftDistance sampler (count • shift) +
          FiniteProduct.addShiftDistance sampler shift := FiniteProduct.addShiftDistance_add_le _ _ _
      _ ≤ (count : ℝ) * FiniteProduct.addShiftDistance sampler shift +
          FiniteProduct.addShiftDistance sampler shift := add_le_add ih le_rfl
      _ = _ := by push_cast; ring

theorem shift_zsmul_le {R : Type} [AddCommGroup R]
    (sampler : ProbComp R) (shift : R) (multiple : ℤ) :
    FiniteProduct.addShiftDistance sampler (multiple • shift) ≤
      (multiple.natAbs : ℝ) * FiniteProduct.addShiftDistance sampler shift := by
  cases multiple with
  | ofNat count =>
      simpa only [Int.ofNat_eq_natCast, natCast_zsmul, Int.natAbs_natCast] using
        shift_nsmul_le sampler shift count
  | negSucc count =>
      rw [negSucc_zsmul, shift_neg]
      simpa using shift_nsmul_le sampler shift (count + 1)

theorem shift_intCast_le (q radius : ℕ) [NeZero q] (shift : ℤ) :
    FiniteProduct.addShiftDistance (draw q radius) (shift : ZMod q) ≤
      (shift.natAbs : ℝ) / (2 * radius + 1 : ℝ) := by
  have h := shift_zsmul_le (draw q radius) (1 : ZMod q) shift
  rw [zsmul_one] at h
  exact h.trans (by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (unit_shift_le q radius) (by positivity : 0 ≤ (shift.natAbs : ℝ)))

theorem shift_le_centered (q radius : ℕ) [NeZero q] (shift : ZMod q) :
    FiniteProduct.addShiftDistance (draw q radius) shift ≤
      ((LatticeCrypto.centeredRepr shift).natAbs : ℝ) / (2 * radius + 1 : ℝ) := by
  have h := shift_intCast_le q radius (LatticeCrypto.centeredRepr shift)
  rw [← LatticeCrypto.centeredRepr_intCast shift] at h
  exact h

def sample (q radius rounds : ℕ) [NeZero q] : ProbComp (ZMod q) :=
  value q radius <$> BoundedUniform.sampleFin (2 * radius + 1) rounds

theorem coinBound_sample (q radius rounds : ℕ) [NeZero q] :
    BoundedUniform.CoinBound (sample q radius rounds)
      (rounds * BoundedUniform.ticketWidth (2 * radius + 1)) := by
  exact BoundedUniform.coinBound_map _ (BoundedUniform.coinBound_sampleFin _ _)

theorem sample_tvDist_le (q radius rounds : ℕ) [NeZero q] :
    tvDist (sample q radius rounds) (draw q radius) ≤ (1 / 2 : ℝ) ^ rounds := by
  exact (tvDist_map_le (value q radius) (BoundedUniform.sampleFin (2 * radius + 1) rounds)
    ($ᵗ Fin (2 * radius + 1))).trans (BoundedUniform.tvDist_sampleFin_le _ _)

theorem value_centered_bound (q radius : ℕ) [NeZero q] (ticket : Fin (2 * radius + 1)) :
    (LatticeCrypto.centeredRepr (value q radius ticket)).natAbs ≤ radius := by
  have habs : ((ticket.val : ℤ) - radius).natAbs ≤ radius := by
    have ht := ticket.isLt
    cases hx : ((ticket.val : ℤ) - radius) with
    | ofNat count =>
        change count ≤ radius
        simp only [Int.ofNat_eq_natCast] at hx
        omega
    | negSucc count => change count + 1 ≤ radius; omega
  have hcast : value q radius ticket = (((ticket.val : ℤ) - radius : ℤ) : ZMod q) := by
    simp [value]
  rw [hcast]
  exact (TFHE.NoiseBounds.centeredRepr_intCast_natAbs_le _).trans habs

theorem draw_total (q radius : ℕ) [NeZero q] : Pr[⊥ | draw q radius] = 0 := by
  simp [draw]

theorem sample_total (q radius rounds : ℕ) [NeZero q] :
    Pr[⊥ | sample q radius rounds] = 0 := by simp

theorem sample_support_centered_bound (q radius rounds : ℕ) [NeZero q]
    (error : ZMod q) (h : error ∈ support (sample q radius rounds)) :
    (LatticeCrypto.centeredRepr error).natAbs ≤ radius := by
  obtain ⟨ticket, _, ht⟩ := mem_support_map_peel (value q radius)
    (BoundedUniform.sampleFin (2 * radius + 1) rounds) h
  rw [ht]
  exact value_centered_bound q radius ticket

/-- The first-moment premise can be supplied by an actual bounded interval sampler. -/
theorem mapped_firstMoment_le (q radius : ℕ) [NeZero q]
    (tickets : ProbComp (Fin (2 * radius + 1))) :
    FormalProof4FHE.BlockBinary.scalarFirstMoment (value q radius <$> tickets)
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) ≤ (radius : ℝ) := by
  have hmass : (∑ ticket, Pr[= ticket | tickets].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold FormalProof4FHE.BlockBinary.scalarFirstMoment
  rw [← tsum_fintype (L := .unconditional _)]
  rw [FiniteProduct.tsum_probOutput_map_toReal_mul tickets (value q radius)
    (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) (fun _ ↦ by positivity)]
  rw [tsum_fintype]
  calc
    _ ≤ ∑ ticket, Pr[= ticket | tickets].toReal * (radius : ℝ) := by
      apply Finset.sum_le_sum
      intro ticket _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast value_centered_bound q radius ticket
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem sample_firstMoment_le (q radius rounds : ℕ) [NeZero q] :
    FormalProof4FHE.BlockBinary.scalarFirstMoment (sample q radius rounds)
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) ≤ (radius : ℝ) :=
  mapped_firstMoment_le q radius _

/-- An exponentially wide interval uses only a linear number of bits per retry. -/
theorem exponential_ticketWidth_le (parameter : ℕ) :
    BoundedUniform.ticketWidth (2 * 2 ^ parameter + 1) ≤ parameter + 2 := by
  apply BoundedUniform.ticketWidth_le (by positivity)
  have hpositive : 0 < (2 : ℕ) ^ parameter := by positivity
  rw [pow_add]
  norm_num
  omega

theorem coinBound_exponential_sample (q parameter rounds : ℕ) [NeZero q] :
    BoundedUniform.CoinBound (sample q (2 ^ parameter) rounds) (rounds * (parameter + 2)) :=
  (coinBound_sample q (2 ^ parameter) rounds).mono
    (Nat.mul_le_mul_left rounds (exponential_ticketWidth_le parameter))

/-- Finite-budget sampling costs two approximation terms when comparing a law to its shift. -/
theorem sample_shift_le_centered (q radius rounds : ℕ) [NeZero q] (shift : ZMod q) :
    FiniteProduct.addShiftDistance (sample q radius rounds) shift ≤
      ((LatticeCrypto.centeredRepr shift).natAbs : ℝ) / (2 * radius + 1 : ℝ) +
        2 * (1 / 2 : ℝ) ^ rounds := by
  let translate := fun value : ZMod q ↦ shift + value
  calc
    _ ≤ tvDist (translate <$> sample q radius rounds) (translate <$> draw q radius) +
        tvDist (translate <$> draw q radius) (sample q radius rounds) :=
      tvDist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ rounds +
        (FiniteProduct.addShiftDistance (draw q radius) shift +
          tvDist (draw q radius) (sample q radius rounds)) := by
      apply add_le_add
      · exact (tvDist_map_le translate _ _).trans (sample_tvDist_le q radius rounds)
      · exact tvDist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ rounds +
        (((LatticeCrypto.centeredRepr shift).natAbs : ℝ) / (2 * radius + 1 : ℝ) +
          (1 / 2 : ℝ) ^ rounds) := by
      apply add_le_add le_rfl
      apply add_le_add (shift_le_centered q radius shift)
      rw [tvDist_comm]
      exact sample_tvDist_le q radius rounds
    _ = _ := by ring

/-- A total narrow law convolved with interval errors is close to the interval law itself. -/
theorem convolution_tvDist_le (q radius : ℕ) [NeZero q]
    (narrow : ProbComp (ZMod q)) (hTotal : Pr[⊥ | narrow] = 0) :
    tvDist (do
      let small ← narrow
      let wide ← draw q radius
      pure (small + wide)) (draw q radius) ≤
      FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
        (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) /
          (2 * radius + 1 : ℝ) := by
  have hconst : 𝒟[narrow >>= fun _ ↦ draw q radius] = 𝒟[draw q radius] :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      narrow hTotal _
  calc
    _ = tvDist (narrow >>= fun small ↦ (fun wide ↦ small + wide) <$> draw q radius)
        (narrow >>= fun _ ↦ draw q radius) := by
      unfold tvDist
      rw [hconst]
      rfl
    _ ≤ ∑' small, Pr[= small | narrow].toReal *
        FiniteProduct.addShiftDistance (draw q radius) small :=
      tvDist_bind_left_le _ _ _
    _ ≤ ∑' small, Pr[= small | narrow].toReal *
        (((LatticeCrypto.centeredRepr small).natAbs : ℝ) / (2 * radius + 1 : ℝ)) := by
      rw [tsum_fintype, tsum_fintype]
      apply Finset.sum_le_sum
      intro small _
      exact mul_le_mul_of_nonneg_left (shift_le_centered q radius small) ENNReal.toReal_nonneg
    _ = _ := by
      simp only [tsum_fintype, FormalProof4FHE.BlockBinary.scalarFirstMoment,
        mul_div_assoc, Finset.sum_div]

/-- The implementable flooding sampler adds just one approximation term to the convolution bound. -/
theorem sampled_convolution_tvDist_le (q radius rounds : ℕ) [NeZero q]
    (narrow : ProbComp (ZMod q)) (hTotal : Pr[⊥ | narrow] = 0) :
    tvDist (do
      let small ← narrow
      let wide ← sample q radius rounds
      pure (small + wide)) (draw q radius) ≤
      FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
        (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) /
          (2 * radius + 1 : ℝ) + (1 / 2 : ℝ) ^ rounds := by
  have happrox := tvDist_bind_left_le_const' (m := ProbComp) narrow
    (fun small ↦ (fun wide : ZMod q ↦ small + wide) <$> sample q radius rounds)
    (fun small ↦ (fun wide : ZMod q ↦ small + wide) <$> draw q radius)
    ((1 / 2 : ℝ) ^ rounds)
    (fun small ↦ (tvDist_map_le (fun wide : ZMod q ↦ small + wide)
      (sample q radius rounds) (draw q radius)).trans (sample_tvDist_le q radius rounds))
  have hconv : tvDist
      (narrow >>= fun small ↦ (fun wide : ZMod q ↦ small + wide) <$> draw q radius)
      (draw q radius) ≤
      FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
        (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) /
          (2 * radius + 1 : ℝ) := by
    simpa only [map_eq_bind_pure_comp, Function.comp_def] using
      convolution_tvDist_le q radius narrow hTotal
  have htriangle := tvDist_triangle
    (narrow >>= fun small ↦ (fun wide : ZMod q ↦ small + wide) <$> sample q radius rounds)
    (narrow >>= fun small ↦ (fun wide : ZMod q ↦ small + wide) <$> draw q radius)
    (draw q radius)
  have hbound := htriangle.trans (add_le_add happrox hconv)
  simpa only [map_eq_bind_pure_comp, Function.comp_def, add_comm] using hbound

/-- The interval translation bound directly discharges the small-secret reduction's slope premise. -/
theorem noiseAbsorptionGap_le (q radius blockLength blockCount extractedDimension samples : ℕ)
    [NeZero q] (narrow : ProbComp (ZMod q)) (momentBound : ℝ)
    (hmoment : FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) ≤ momentBound) :
    FormalProof4FHE.BlockBinary.noiseAbsorptionGap blockLength blockCount
      extractedDimension samples narrow (draw q radius) ≤
    min 1 (((samples : ℝ) * (blockCount * blockLength : ℝ) / (blockLength + 1 : ℝ)) *
      (momentBound / (2 * radius + 1 : ℝ))) := by
  have h := FormalProof4FHE.BlockBinary.noiseAbsorptionGap_le_shiftMoment
    blockLength blockCount extractedDimension samples narrow (draw q radius)
    (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ))
    (1 / (2 * radius + 1 : ℝ)) momentBound (by positivity)
    (fun error ↦ by simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      shift_le_centered q radius error) hmoment
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

end FormalProof4FHE.UniformInterval
