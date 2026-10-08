/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Fin

/-!
# Bounded fair-bit sampling

Uniform binary words use only primitive fair-bit queries. Bounded rejection
returns a valid ticket even when its fixed retry budget is exhausted. The
structural query predicate checks both the oracle index and the worst-case
number of queries; an abstract large-range uniform oracle is not used.
-/

open OracleComp ProbComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.BoundedUniform

/-- All queries are fair bits, with a bound on every execution path. -/
def CoinBound {Output : Type} (sampler : ProbComp Output) (budget : ℕ) : Prop :=
  sampler.IsQueryBound budget (fun index left => index = 1 ∧ 0 < left)
    (fun _ left => left - 1)

theorem coinBound_pure {Output : Type} (value : Output) (budget : ℕ) :
    CoinBound (pure value) budget := by
  simp [CoinBound]

theorem coinBound_bind {Input Output : Type} {sampler : ProbComp Input}
    {next : Input → ProbComp Output} {first second : ℕ}
    (hfirst : CoinBound sampler first) (hsecond : ∀ value, CoinBound (next value) second) :
    CoinBound (sampler >>= next) (first + second) := by
  apply isQueryBound_bind Nat.add _ _ hfirst hsecond
  · intro index left right budget h
    exact ⟨⟨h.1, by dsimp; omega⟩, ⟨h.1, by dsimp; omega⟩⟩
  · intro index left right budget h
    constructor <;> dsimp <;> omega

theorem coinBound_map {Input Output : Type} (f : Input → Output)
    {sampler : ProbComp Input} {budget : ℕ} (h : CoinBound sampler budget) :
    CoinBound (f <$> sampler) budget := by
  simpa only [CoinBound, isQueryBound_map_iff] using h

theorem coinBound_total {Output : Type} {sampler : ProbComp Output} {budget : ℕ}
    (h : CoinBound sampler budget) : sampler.IsTotalQueryBound budget :=
  h.proj id (fun _ _ allowed => allowed.2) (fun _ _ _ => rfl)

theorem CoinBound.mono {Output : Type} {sampler : ProbComp Output} {first second : ℕ}
    (h : CoinBound sampler first) (hle : first ≤ second) : CoinBound sampler second := by
  induction sampler using OracleComp.inductionOn generalizing first second with
  | pure value => exact coinBound_pure value second
  | query_bind index next ih =>
    rw [CoinBound, isQueryBound_query_bind_iff] at h ⊢
    exact ⟨⟨h.1.1, Nat.lt_of_lt_of_le h.1.2 hle⟩,
      fun value => ih value (h.2 value) (Nat.sub_le_sub_right hle 1)⟩

/-- Prepend one bit using a public bijection, independent of every secret. -/
def appendBitEquiv (width : ℕ) : (Fin 2 × Fin (2 ^ width)) ≃ Fin (2 ^ (width + 1)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_succ']))

/-- Exactly `width` primitive fair-bit queries. -/
def drawBits : (width : ℕ) → ProbComp (Fin (2 ^ width))
  | 0 => pure ⟨0, by decide⟩
  | width + 1 => do
    let bit ← $[0..1]
    let rest ← drawBits width
    return appendBitEquiv width (bit, rest)

theorem coinBound_drawBits (width : ℕ) : CoinBound (drawBits width) width := by
  induction width with
  | zero => exact coinBound_pure _ _
  | succ width ih =>
    simp only [drawBits, ProbComp.uniformFin_def, CoinBound,
      isQueryBound_query_bind_iff]
    refine ⟨⟨trivial, by omega⟩, fun bit => ?_⟩
    simpa only [CoinBound, Nat.add_sub_cancel, map_eq_bind_pure_comp, Function.comp_def] using
      coinBound_map (fun rest => appendBitEquiv width (bit, rest)) ih

theorem evalDist_drawBits (width : ℕ) :
    𝒟[drawBits width] = 𝒟[$ᵗ (Fin (2 ^ width))] := by
  induction width with
  | zero =>
    apply evalDist_ext
    intro value
    have hvalue : value = ⟨0, by decide⟩ := by
      apply Fin.ext
      have := value.isLt
      simp only [pow_zero] at this
      omega
    simp [drawBits, hvalue, probOutput_uniformSample]
  | succ width ih =>
    have hbit : 𝒟[($[0..1] : ProbComp (Fin 2))] = 𝒟[$ᵗ (Fin 2)] := by
      apply evalDist_ext
      intro bit
      norm_num [probOutput_uniformSample]
    calc
      𝒟[drawBits (width + 1)] =
          𝒟[appendBitEquiv width <$> (do
            let bit ← $ᵗ (Fin 2)
            let rest ← $ᵗ (Fin (2 ^ width))
            return (bit, rest))] := by
              simp only [drawBits, map_bind, map_pure, evalDist_bind, evalDist_pure,
                hbit, ih]
      _ = 𝒟[appendBitEquiv width <$> ($ᵗ (Fin 2 × Fin (2 ^ width)))] := by
        rw [evalDist_map, FiniteProduct.evalDist_independent_uniform_product,
          ← evalDist_map]
      _ = _ := evalDist_map_bijective_uniform_cross _ _ (appendBitEquiv width).bijective

/-- Minimal floor-log width plus one, so acceptance is at least one half. -/
def ticketWidth (tickets : ℕ) : ℕ := Nat.log2 tickets + 1

theorem tickets_lt_capacity (tickets : ℕ) : tickets < 2 ^ ticketWidth tickets := by
  simpa only [ticketWidth, Nat.log2_eq_log_two] using
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) tickets

theorem capacity_le_twice_tickets (tickets : ℕ) (hpositive : 0 < tickets) :
    2 ^ ticketWidth tickets ≤ 2 * tickets := by
  rw [ticketWidth, Nat.log2_eq_log_two, pow_succ']
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

theorem ticketWidth_le {tickets width : ℕ} (hpositive : 0 < tickets)
    (hbound : tickets < 2 ^ width) : ticketWidth tickets ≤ width := by
  rw [ticketWidth, Nat.log2_eq_log_two]
  exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow (by omega) hbound)

/-- Fixed-budget rejection; ticket zero is a valid terminal fallback. -/
def sampleFin (tickets : ℕ) [NeZero tickets] : ℕ → ProbComp (Fin tickets)
  | 0 => pure ⟨0, Nat.pos_of_ne_zero (NeZero.ne tickets)⟩
  | rounds + 1 => do
    let candidate ← drawBits (ticketWidth tickets)
    if h : candidate.val < tickets then
      return ⟨candidate.val, h⟩
    else sampleFin tickets rounds

theorem coinBound_sampleFin (tickets rounds : ℕ) [NeZero tickets] :
    CoinBound (sampleFin tickets rounds) (rounds * ticketWidth tickets) := by
  induction rounds with
  | zero => exact coinBound_pure _ _
  | succ rounds ih =>
    have hbranches : ∀ candidate : Fin (2 ^ ticketWidth tickets),
        CoinBound
          (if h : candidate.val < tickets then pure ⟨candidate.val, h⟩
            else sampleFin tickets rounds) (rounds * ticketWidth tickets) := by
      intro candidate
      split
      · exact coinBound_pure _ _
      · exact ih
    simpa only [sampleFin, Nat.succ_mul, Nat.add_comm] using
      coinBound_bind (coinBound_drawBits (ticketWidth tickets)) hbranches

/-- Enumerate one accepted output and all rejected words, without expanding the
executable representation into a list of tickets. -/
theorem sum_step {capacity tickets : ℕ} (hsize : tickets ≤ capacity)
    (target : Fin tickets) (accepted rejected : ℝ≥0∞) :
    (∑ candidate : Fin capacity,
      if h : candidate.val < tickets then
        (if target = (⟨candidate.val, h⟩ : Fin tickets) then accepted else 0)
      else rejected) = accepted + ((capacity - tickets : ℕ) : ℝ≥0∞) * rejected := by
  classical
  let lift : Fin capacity := ⟨target.val, lt_of_lt_of_le target.isLt hsize⟩
  have hpoint : ∀ candidate : Fin capacity,
      (if h : candidate.val < tickets then
        (if target = (⟨candidate.val, h⟩ : Fin tickets) then accepted else 0)
      else rejected) =
        (if candidate = lift then accepted else 0) +
          (if ¬ candidate.val < tickets then rejected else 0) := by
    intro candidate
    by_cases h : candidate.val < tickets
    · have heq : target = (⟨candidate.val, h⟩ : Fin tickets) ↔ candidate = lift := by
        simp only [Fin.ext_iff, lift]
        exact eq_comm
      simp [h, heq]
    · have hne : candidate ≠ lift := by
        intro heq
        apply h
        simpa only [heq, lift] using target.isLt
      simp [h, hne]
  have hcard : (Finset.univ.filter (fun candidate : Fin capacity =>
      ¬ candidate.val < tickets)).card = capacity - tickets := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun candidate : Fin capacity => candidate.val < tickets)
    have haccepted : (Finset.univ.filter (fun candidate : Fin capacity =>
        candidate.val < tickets)).card = tickets := by
      simpa only [Nat.min_eq_right hsize] using
        (Fin.card_filter_val_lt (n := capacity) (m := tickets))
    simp only [haccepted, Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]

/-- One idealized rejection step with an arbitrary continuation. -/
def step (tickets : ℕ) [NeZero tickets] (next : ProbComp (Fin tickets)) :
    ProbComp (Fin tickets) := do
  let candidate ← drawBits (ticketWidth tickets)
  if h : candidate.val < tickets then return ⟨candidate.val, h⟩ else next

theorem probOutput_step (tickets : ℕ) [NeZero tickets]
    (next : ProbComp (Fin tickets)) (target : Fin tickets) :
    Pr[= target | step tickets next] =
      ((2 ^ ticketWidth tickets : ℕ) : ℝ≥0∞)⁻¹ +
        ((2 ^ ticketWidth tickets - tickets : ℕ) : ℝ≥0∞) *
          ((2 ^ ticketWidth tickets : ℕ) : ℝ≥0∞)⁻¹ * Pr[= target | next] := by
  rw [step, probOutput_bind_eq_sum_fintype]
  have hdraw : ∀ candidate : Fin (2 ^ ticketWidth tickets),
      Pr[= candidate | drawBits (ticketWidth tickets)] =
        ((2 ^ ticketWidth tickets : ℕ) : ℝ≥0∞)⁻¹ := by
    intro candidate
    rw [probOutput_congr rfl (evalDist_drawBits (ticketWidth tickets))]
    simp only [probOutput_uniformSample, Fintype.card_fin]
  simp_rw [hdraw]
  have hsum := sum_step (Nat.le_of_lt (tickets_lt_capacity tickets)) target
    (((2 ^ ticketWidth tickets : ℕ) : ℝ≥0∞)⁻¹)
    (((2 ^ ticketWidth tickets : ℕ) : ℝ≥0∞)⁻¹ * Pr[= target | next])
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro candidate _
    split <;> simp [probOutput_pure]
  · ring

theorem evalDist_step_uniform (tickets : ℕ) [NeZero tickets] :
    𝒟[step tickets ($ᵗ (Fin tickets))] = 𝒟[$ᵗ (Fin tickets)] := by
  apply evalDist_ext
  intro target
  apply (ENNReal.toReal_eq_toReal_iff' probOutput_ne_top probOutput_ne_top).mp
  rw [probOutput_step]
  have htickets : tickets ≠ 0 := NeZero.ne tickets
  have hcapacity : (2 ^ ticketWidth tickets : ℕ) ≠ 0 := by positivity
  have hsize := Nat.le_of_lt (tickets_lt_capacity tickets)
  simp only [probOutput_uniformSample, Fintype.card_fin]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_mul]
  rw [Nat.cast_sub hsize]
  have ht : (tickets : ℝ) ≠ 0 := by exact_mod_cast htickets
  have hc : ((2 ^ ticketWidth tickets : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hcapacity
  field_simp
  ring

/-- Rejection probability for one uniform word. -/
noncomputable def rejectionRate (tickets : ℕ) : ℝ :=
  (2 ^ ticketWidth tickets - tickets : ℕ) / (2 ^ ticketWidth tickets : ℕ)

theorem rejectionRate_nonneg (tickets : ℕ) : 0 ≤ rejectionRate tickets := by
  unfold rejectionRate
  positivity

theorem rejectionRate_le_half (tickets : ℕ) [NeZero tickets] :
    rejectionRate tickets ≤ 1 / 2 := by
  have hpositive : 0 < tickets := Nat.pos_of_ne_zero (NeZero.ne tickets)
  have hsize := Nat.le_of_lt (tickets_lt_capacity tickets)
  have hcapacity := capacity_le_twice_tickets tickets hpositive
  have hreal : ((2 ^ ticketWidth tickets : ℕ) : ℝ) ≤ 2 * tickets := by
    exact_mod_cast hcapacity
  have hcapPos : (0 : ℝ) < (2 ^ ticketWidth tickets : ℕ) := by positivity
  rw [rejectionRate, Nat.cast_sub hsize, div_le_iff₀ hcapPos]
  linarith

theorem tvDist_step_le (tickets : ℕ) [NeZero tickets]
    (next : ProbComp (Fin tickets)) :
    tvDist (step tickets next) ($ᵗ (Fin tickets)) ≤
      rejectionRate tickets * tvDist next ($ᵗ (Fin tickets)) := by
  classical
  let left (candidate : Fin (2 ^ ticketWidth tickets)) : ProbComp (Fin tickets) :=
    if h : candidate.val < tickets then pure ⟨candidate.val, h⟩ else next
  let right (candidate : Fin (2 ^ ticketWidth tickets)) : ProbComp (Fin tickets) :=
    if h : candidate.val < tickets then pure ⟨candidate.val, h⟩ else $ᵗ (Fin tickets)
  have hbound := FiniteProduct.tvDist_bind_left_le_expectation
    (drawBits (ticketWidth tickets)) left right
  have hpoint : ∀ candidate : Fin (2 ^ ticketWidth tickets),
      Pr[= candidate | drawBits (ticketWidth tickets)].toReal *
          tvDist (left candidate) (right candidate) =
        if ¬ candidate.val < tickets then
          ((2 ^ ticketWidth tickets : ℕ) : ℝ)⁻¹ * tvDist next ($ᵗ (Fin tickets)) else 0 := by
    intro candidate
    have hdraw := probOutput_congr (x := candidate) rfl
      (evalDist_drawBits (ticketWidth tickets))
    rw [hdraw]
    by_cases h : candidate.val < tickets
    · simp [left, right, h]
    · simp [left, right, h, probOutput_uniformSample]
  have hcard : (Finset.univ.filter (fun candidate : Fin (2 ^ ticketWidth tickets) =>
      ¬ candidate.val < tickets)).card = 2 ^ ticketWidth tickets - tickets := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun candidate : Fin (2 ^ ticketWidth tickets) =>
        candidate.val < tickets)
    have haccepted : (Finset.univ.filter (fun candidate : Fin (2 ^ ticketWidth tickets) =>
        candidate.val < tickets)).card = tickets := by
      simpa only [Nat.min_eq_right (Nat.le_of_lt (tickets_lt_capacity tickets))] using
        (Fin.card_filter_val_lt (n := 2 ^ ticketWidth tickets) (m := tickets))
    simp only [haccepted, Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  rw [tsum_fintype] at hbound
  simp_rw [hpoint] at hbound
  rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul] at hbound
  have hid : tvDist (step tickets next) ($ᵗ (Fin tickets)) =
      tvDist (drawBits (ticketWidth tickets) >>= left)
        (drawBits (ticketWidth tickets) >>= right) := by
    change (𝒟[step tickets next]).tvDist (𝒟[$ᵗ (Fin tickets)]) = _
    rw [← evalDist_step_uniform tickets]
    rfl
  rw [hid]
  simpa only [rejectionRate, div_eq_mul_inv, mul_assoc] using hbound

/-- Exhausting `rounds` can change the ticket distribution by at most `2⁻rounds`. -/
theorem tvDist_sampleFin_le (tickets rounds : ℕ) [NeZero tickets] :
    tvDist (sampleFin tickets rounds) ($ᵗ (Fin tickets)) ≤ (1 / 2 : ℝ) ^ rounds := by
  induction rounds with
  | zero => simpa only [pow_zero] using tvDist_le_one (sampleFin tickets 0) ($ᵗ (Fin tickets))
  | succ rounds ih =>
    calc
      tvDist (sampleFin tickets (rounds + 1)) ($ᵗ (Fin tickets)) ≤
          rejectionRate tickets * tvDist (sampleFin tickets rounds) ($ᵗ (Fin tickets)) :=
        tvDist_step_le tickets (sampleFin tickets rounds)
      _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ rounds :=
        mul_le_mul (rejectionRate_le_half tickets) ih (tvDist_nonneg _ _) (by positivity)
      _ = _ := by rw [pow_succ']

end FormalProof4FHE.BoundedUniform
