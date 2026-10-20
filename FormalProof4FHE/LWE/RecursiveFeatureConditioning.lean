/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.RecursiveFeatureControlPolynomial

/-!
# Testing key-bit conditioning for the genuine cubic-control hop

Knowing one factor gives an explicit quadratic polynomial for a cubic control
message. Covering all genuine three-distinct-coordinate control messages by
this construction, however, leaves at most two unknown key bits. A fixed
guess for the necessary known coordinates matches a uniform key with
probability at most 4/2^n. This filters the conditioning/guessing reduction
template; it is not an attack on the unconditioned scheme or an obstruction
to every computational reduction for the actual plaintext observer.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.RecursiveFeatureConditioning

open RecursiveFeatureControlPolynomial RecursiveFeatureBootstrap RecursiveFeatureGSW

def CoversCubics {n : ℕ} (known : Finset (Fin n)) : Prop :=
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    i ∈ known ∨ j ∈ known ∨ k ∈ known

/-- A known bit is a coefficient, so the resulting message is quadratic. -/
def conditionedCubic {q n : ℕ} [NeZero q] (weight : ZMod q)
    (known : Finset (Fin n)) (fixed : Fin n → Bool) (i j k : Fin n) :
    RecursiveQuadratic.Polynomial (ZMod q) n 1 :=
  if i ∈ known then pairPolynomial (weight * GSWSelfKey.binaryEmbed fixed i) j k
  else if j ∈ known then pairPolynomial (weight * GSWSelfKey.binaryEmbed fixed j) i k
  else pairPolynomial (weight * GSWSelfKey.binaryEmbed fixed k) i j

theorem message_conditionedCubic {q n : ℕ} [NeZero q] (weight : ZMod q)
    (known : Finset (Fin n)) (fixed bits : Fin n → Bool) (i j k : Fin n)
    (hknown : i ∈ known ∨ j ∈ known ∨ k ∈ known)
    (hfixed : ∀ a ∈ known, bits a = fixed a) :
    RecursiveQuadratic.message (conditionedCubic weight known fixed i j k)
      (GSWSelfKey.binaryEmbed bits) 0 =
        weight * GSWSelfKey.binaryEmbed bits i * GSWSelfKey.binaryEmbed bits j *
          GSWSelfKey.binaryEmbed bits k := by
  have hemb (a : Fin n) (ha : a ∈ known) :
      GSWSelfKey.binaryEmbed (R := ZMod q) fixed a = GSWSelfKey.binaryEmbed bits a := by
    simp [GSWSelfKey.binaryEmbed, hfixed a ha]
  by_cases hi : i ∈ known
  · simp only [conditionedCubic, if_pos hi, message_pairPolynomial, hemb i hi]
  · by_cases hj : j ∈ known
    · simp only [conditionedCubic, if_neg hi, if_pos hj, message_pairPolynomial, hemb j hj]
      ring
    · have hk : k ∈ known := hknown.resolve_left hi |>.resolve_left hj
      simp only [conditionedCubic, if_neg hi, if_neg hj, message_pairPolynomial, hemb k hk]
      ring

/-- This is the actual quadratic-feature control message, not an unrelated cubic. -/
theorem conditioned_control_message {q n : ℕ} [NeZero q]
    (params : RecursiveMultiplication.Parameters q) (level : Fin params.levels)
    (known : Finset (Fin n)) (fixed bits : Fin n → Bool) (i j k : Fin n)
    (hcover : CoversCubics known) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hfixed : ∀ a ∈ known, bits a = fixed a) :
    RecursiveQuadratic.message
      (conditionedCubic (TFHE.Gadget.Base.gadget params level) known fixed i j k)
      (GSWSelfKey.binaryEmbed bits) 0 =
        controlMessage params (GSWSelfKey.binaryEmbed bits) i (some (.inr (j, k))) level := by
  rw [controlMessage_quadratic]
  exact message_conditionedCubic _ known fixed bits i j k (hcover i j k hij hik hjk) hfixed

theorem coversCubics_iff_unknown_card_le_two {n : ℕ} (known : Finset (Fin n)) :
    CoversCubics known ↔ knownᶜ.card ≤ 2 := by
  constructor
  · intro hcover
    by_contra h
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
      Finset.two_lt_card_iff.mp (by omega : 2 < knownᶜ.card)
    simp only [Finset.mem_compl] at hi hj hk
    exact (hcover i j k hij hik hjk).elim hi (fun h ↦ h.elim hj hk)
  · intro hcard i j k hij hik hjk
    by_contra h
    have hi : i ∈ knownᶜ := by simp only [Finset.mem_compl]; tauto
    have hj : j ∈ knownᶜ := by simp only [Finset.mem_compl]; tauto
    have hk : k ∈ knownᶜ := by simp only [Finset.mem_compl]; tauto
    have hthree := Finset.two_lt_card_iff.mpr ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩
    omega

theorem known_card_lower_bound {n : ℕ} (known : Finset (Fin n))
    (hcover : CoversCubics known) : n ≤ known.card + 2 := by
  have hunknown := (coversCubics_iff_unknown_card_le_two known).mp hcover
  have hsum := Finset.card_add_card_compl known
  simp only [Fintype.card_fin] at hsum
  omega

theorem compatible_key_count_le_four {n : ℕ} (known : Finset (Fin n))
    (fixed : Fin n → Bool) (hcover : CoversCubics known) :
    (Finset.univ.filter fun bits : Fin n → Bool ↦ ∀ i ∈ known, bits i = fixed i).card ≤ 4 := by
  classical
  let Candidate := {bits : Fin n → Bool // ∀ i ∈ known, bits i = fixed i}
  let restrict (bits : Candidate) : {i : Fin n // i ∉ known} → Bool := fun i ↦ bits.val i
  have hinjective : Function.Injective restrict := by
    intro a b hab
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ known
    · exact (a.property i hi).trans (b.property i hi).symm
    · exact congrFun hab ⟨i, hi⟩
  have hcount := Fintype.card_le_of_injective restrict hinjective
  have hset : (Finset.univ.filter fun i : Fin n ↦ i ∉ known) = knownᶜ := by
    ext i
    simp
  have hunknown : Fintype.card {i : Fin n // i ∉ known} ≤ 2 := by
    simpa only [Fintype.card_subtype, hset] using
      (coversCubics_iff_unknown_card_le_two known).mp hcover
  have hpower : 2 ^ Fintype.card {i : Fin n // i ∉ known} ≤ 4 := by
    calc
      _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hunknown
      _ = 4 := by norm_num
  have hfinal : Fintype.card Candidate ≤ 4 := by
    simpa only [Fintype.card_fun, Fintype.card_bool] using hcount.trans
      (by simpa only [Fintype.card_fun, Fintype.card_bool] using hpower)
  simpa only [Candidate, Fintype.card_subtype] using hfinal

theorem uniform_guess_probability_le_four_div {n : ℕ} (known : Finset (Fin n))
    (fixed : Fin n → Bool) (hcover : CoversCubics known) :
    (Pr[(fun bits : Fin n → Bool ↦ ∀ i ∈ known, bits i = fixed i) |
      ($ᵗ (Fin n → Bool))]).toReal ≤ 4 / (2 : ℝ) ^ n := by
  classical
  rw [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast compatible_key_count_le_four known fixed hcover

/-- The entropy term used by the quadratic source reduction cannot be made
negligible by applying that bound to at most two unknown uniform bits. This
is a lower bound on this proof's loss term, not on an adversary's advantage. -/
theorem low_entropy_source_gap_ge_quarter (q d unknown : ℕ)
    (hq : 2 ≤ q) (hd : 1 ≤ d) (hunknown : unknown ≤ 2) :
    (1 / 4 : ℝ) ≤ Real.sqrt (((q : ℝ) ^ d - 1) / (2 : ℝ) ^ unknown) / 2 := by
  have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpower : (2 : ℝ) ≤ (q : ℝ) ^ d := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hk : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ (by linarith)
    rw [pow_succ]
    nlinarith
  have hdenom : (2 : ℝ) ^ unknown ≤ 4 := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide) hunknown : 2 ^ unknown ≤ 2 ^ 2)
  have hquarter : (1 / 4 : ℝ) ≤ ((q : ℝ) ^ d - 1) / (2 : ℝ) ^ unknown := by
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ unknown)).mpr
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hquarter
  have hsqrtquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrtquarter] at hsqrt
  linarith

end FormalProof4FHE.LWE.RecursiveFeatureConditioning
