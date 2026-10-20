/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWQuadraticPreimageRowSupport
import FormalProof4FHE.LWE.GSWQuadraticPreimageParameters

/-!
# Two-row quadratic certificates expose a bit of their target pair

If an off-diagonal certificate uses only its two target rows, those rows are
linear preimages with weights summing to the target weight. A strict noise
margin permits a public observer to select and recover at least one endpoint.
Covering every pair leaves at most one coordinate unobserved. This statement
allows arbitrary alternating freedom between the two rows, at even moduli.
It does not exclude builders supported on more rows, and does not assert a
negligible builder-failure rate or a complete asymptotic LWE attack reduction.
An additional lemma handles dense matrices whose rows are scalar multiples
of one target row; that row is itself a linear preimage of the full weight.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWQuadraticPreimageTwoRows

open GSWQuadraticPreimageRowSupport
open TFHE.BootstrappingCorrectness

theorem certificate_symmetric_entry {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (target u : Matrix (Fin n) (Fin n) R)
    (hc : b * a.transpose = target + u - u.transpose) (first second : Fin n) :
    (b * a.transpose) first second + (b * a.transpose) second first =
      target first second + target second first := by
  have hi := congrArg (fun matrix ↦ matrix first second) hc
  have hj := congrArg (fun matrix ↦ matrix second first) hc
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply] at hi hj
  linear_combination hi + hj

/-- Dense outer-product freedom does not help when all rows are proportional
to a target row. No field or division-by-two hypothesis is used. -/
theorem linear_preimage_of_proportional_rows {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (first second : Fin n)
    (hne : first ≠ second) (u : Matrix (Fin n) (Fin n) R)
    (hc : b * a.transpose = coordinateTarget weight first second + u - u.transpose)
    (factors : Fin n → R)
    (hproportional : ∀ row column, b row column = factors row * b first column) :
    a.mulVec (b first) = fun row ↦ if row = second then weight else 0 := by
  have hdiag : (b * a.transpose) first first = 0 := by
    have hh := congrArg (fun matrix ↦ matrix first first) hc
    simpa [coordinateTarget, hne] using hh
  have hz (row : Fin n) : (b * a.transpose) row first = 0 := by
    calc
      _ = factors row * (b * a.transpose) first first := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, hproportional row]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro column _
        ring
      _ = 0 := by rw [hdiag, mul_zero]
  funext row
  change dotProduct (a row) (b first) = _
  rw [dotProduct_comm]
  change (b * a.transpose) first row = _
  have hh := certificate_symmetric_entry a b (coordinateTarget weight first second) u hc first row
  rw [hz row, add_zero] at hh
  simpa [coordinateTarget, hne] using hh

theorem linear_row_of_two_supported_certificate {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (target u : Matrix (Fin n) (Fin n) R)
    (index other : Fin n)
    (hc : b * a.transpose = target + u - u.transpose)
    (hsupport : ∀ row, row ≠ index → row ≠ other → ∀ column, b row column = 0)
    (hdiag : target index index = 0)
    (hoff : ∀ row, row ≠ index → row ≠ other → target index row + target row index = 0) :
    a.mulVec (b index) = fun row ↦
      if row = other then (b * a.transpose) index other else 0 := by
  funext row
  change dotProduct (a row) (b index) = _
  rw [dotProduct_comm]
  change (b * a.transpose) index row = _
  by_cases hr : row = other
  · subst row
    simp
  · rw [if_neg hr]
    by_cases hi : row = index
    · subst row
      have hh := congrArg (fun matrix ↦ matrix index index) hc
      simpa [hdiag] using hh
    · have hz : (b * a.transpose) row index = 0 := by
        simp [Matrix.mul_apply, hsupport row hi hr]
      have hh := certificate_symmetric_entry a b target u hc index row
      rw [hz, add_zero, hoff row hi hr] at hh
      exact hh

theorem first_linear_preimage {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (first second : Fin n)
    (hne : first ≠ second) (u : Matrix (Fin n) (Fin n) R)
    (hc : b * a.transpose = coordinateTarget weight first second + u - u.transpose)
    (hsupport : ∀ row, row ≠ first → row ≠ second → ∀ column, b row column = 0) :
    a.mulVec (b first) = fun row ↦
      if row = second then (b * a.transpose) first second else 0 := by
  apply linear_row_of_two_supported_certificate a b (coordinateTarget weight first second)
    u first second hc hsupport
  · simp [coordinateTarget, hne]
  · intro row hfirst hsecond
    simp [coordinateTarget, hfirst, hsecond]

theorem second_linear_preimage {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (first second : Fin n)
    (hne : first ≠ second) (u : Matrix (Fin n) (Fin n) R)
    (hc : b * a.transpose = coordinateTarget weight first second + u - u.transpose)
    (hsupport : ∀ row, row ≠ first → row ≠ second → ∀ column, b row column = 0) :
    a.mulVec (b second) = fun row ↦
      if row = first then (b * a.transpose) second first else 0 := by
  apply linear_row_of_two_supported_certificate a b (coordinateTarget weight first second)
    u second first hc
      (fun row hsecond hfirst ↦ hsupport row hfirst hsecond)
  · simp [coordinateTarget, Ne.symm hne]
  · intro row hsecond hfirst
    simp [coordinateTarget, Ne.symm hne, hfirst]

theorem weights_add {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (first second : Fin n)
    (hne : first ≠ second) (u : Matrix (Fin n) (Fin n) R)
    (hc : b * a.transpose = coordinateTarget weight first second + u - u.transpose) :
    (b * a.transpose) first second + (b * a.transpose) second first = weight := by
  simpa [coordinateTarget, Ne.symm hne] using
    certificate_symmetric_entry a b (coordinateTarget weight first second) u hc first second

theorem one_decoding_margin {q : ℕ} [NeZero q] (first second weight : ZMod q)
    (hsum : first + second = weight) (bound : ℕ)
    (hmargin : 4 * bound < centeredDistance 0 weight) :
    2 * bound < centeredDistance 0 first ∨ 2 * bound < centeredDistance 0 second := by
  have hh : centeredDistance 0 weight ≤ centeredDistance 0 first + centeredDistance 0 second := by
    have ht := TFHE.NoiseBounds.centeredRepr_add_natAbs_le (-first) (-second)
    simpa [centeredDistance, ← hsum, neg_add, add_comm] using ht
  omega

noncomputable section

abbrev Pair (n : ℕ) := {pair : Fin n × Fin n // pair.1 ≠ pair.2}

/-- Finite public readings; a computational implementation can scan them.
This proof-facing definition selects any reading of a coordinate. -/
def collect {I : Type} {n : ℕ} (readings : I → Fin n × Bool) (row : Fin n) : Option Bool := by
  classical
  exact if h : ∃ item, (readings item).1 = row then some (readings (Classical.choose h)).2 else none

theorem collect_sound {I : Type} {n : ℕ} (readings : I → Fin n × Bool) (bits : Fin n → Bool)
    (hsound : ∀ item, (readings item).2 = bits (readings item).1)
    (row : Fin n) (value : Bool) (hvalue : collect readings row = some value) : value = bits row := by
  classical
  unfold collect at hvalue
  split_ifs at hvalue with h
  · have hv := Option.some.inj hvalue
    rw [← hv, hsound, Classical.choose_spec h]

theorem collect_contains {I : Type} {n : ℕ} (readings : I → Fin n × Bool) (item : I) :
    collect readings (readings item).1 ≠ none := by
  classical
  simp [collect, show ∃ candidate, (readings candidate).1 = (readings item).1 from ⟨item, rfl⟩]

theorem collect_pair_cover {n : ℕ} (readings : Pair n → Fin n × Bool)
    (hindex : ∀ pair, (readings pair).1 = pair.1.1 ∨ (readings pair).1 = pair.1.2)
    (first second : Fin n) (hne : first ≠ second) :
    collect readings first ≠ none ∨ collect readings second ≠ none := by
  let pair : Pair n := ⟨(first, second), hne⟩
  have hh := collect_contains readings pair
  rcases hindex pair with h | h
  · left
    simpa only [h] using hh
  · right
    simpa only [h] using hh

/-- All choices and decoding use only the public source matrix, builder output
and body. The noise bound is a public parameter. -/
def readPair {q n m : ℕ} [NeZero q] (a b : Matrix (Fin n) (Fin m) (ZMod q))
    (first second : Fin n) (body : Fin m → ZMod q) (bound : ℕ) : Fin n × Bool :=
  if 2 * bound < centeredDistance 0 ((b * a.transpose) first second) then
    (second, decodeNearest 0 ((b * a.transpose) first second) (dotProduct (b first) body))
  else
    (first, decodeNearest 0 ((b * a.transpose) second first) (dotProduct (b second) body))

theorem readPair_index {q n m : ℕ} [NeZero q]
    (a b : Matrix (Fin n) (Fin m) (ZMod q)) (first second : Fin n)
    (body : Fin m → ZMod q) (bound : ℕ) :
    (readPair a b first second body bound).1 = first ∨
      (readPair a b first second body bound).1 = second := by
  unfold readPair
  split_ifs <;> simp

theorem readPair_real {q n m : ℕ} [NeZero q]
    (a b : Matrix (Fin n) (Fin m) (ZMod q)) (weight : ZMod q) (first second : Fin n)
    (hne : first ≠ second) (u : Matrix (Fin n) (Fin n) (ZMod q))
    (hc : b * a.transpose = coordinateTarget weight first second + u - u.transpose)
    (hsupport : ∀ row, row ≠ first → row ≠ second → ∀ column, b row column = 0)
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (bound : ℕ)
    (hfirst : (LatticeCrypto.centeredRepr (dotProduct (b first) error)).natAbs ≤ bound)
    (hsecond : (LatticeCrypto.centeredRepr (dotProduct (b second) error)).natAbs ≤ bound)
    (hmargin : 4 * bound < centeredDistance 0 weight) :
    let observed := readPair a b first second (vecMul (GSWSelfKey.binaryEmbed bits) a + error) bound
    observed.2 = bits observed.1 := by
  have hm := one_decoding_margin _ _ weight (weights_add a b weight first second hne u hc) bound hmargin
  unfold readPair
  split_ifs with h
  · exact decode_projection a (b first) _ second
      (first_linear_preimage a b weight first second hne u hc hsupport) bits error bound hfirst h
  · exact decode_projection a (b second) _ first
      (second_linear_preimage a b weight first second hne u hc hsupport) bits error bound hsecond
      (hm.resolve_left h)

/-- If each pair contributes an observed endpoint, two distinct coordinates
cannot both be missing. -/
theorem missing_unique {n : ℕ} (known : Finset (Fin n))
    (hcover : ∀ first second : Fin n, first ≠ second → first ∈ known ∨ second ∈ known)
    (first second : Fin n) (hfirst : first ∉ known) (hsecond : second ∉ known) :
    first = second := by
  by_contra hne
  exact (hcover first second hne).elim hfirst hsecond

def complete {n : ℕ} (observations : Fin n → Option Bool) (fallback : Bool) : Fin n → Bool :=
  fun row ↦ (observations row).getD fallback

/-- With sound observations covering an endpoint of every pair, the entire
secret lies in the two public completions. -/
theorem eq_one_of_two_completions {n : ℕ} (observations : Fin n → Option Bool) (bits : Fin n → Bool)
    (hsound : ∀ row value, observations row = some value → value = bits row)
    (hcover : ∀ first second : Fin n, first ≠ second → observations first ≠ none ∨ observations second ≠ none) :
    complete observations false = bits ∨ complete observations true = bits := by
  by_cases hmissing : ∃ row, observations row = none
  · obtain ⟨missing, hm⟩ := hmissing
    have heq : complete observations (bits missing) = bits := by
      funext row
      cases hr : observations row with
      | none =>
        have hrow : row = missing := by
          by_contra hne
          exact (hcover row missing hne).elim (fun h ↦ h hr) (fun h ↦ h hm)
        simp [complete, hrow, hm]
      | some value => simp [complete, hr, hsound row value hr]
    cases hb : bits missing
    · exact Or.inl (by simpa [hb] using heq)
    · exact Or.inr (by simpa [hb] using heq)
  · left
    funext row
    cases hr : observations row with
    | none => exact (hmissing ⟨row, hr⟩).elim
    | some value => simp [complete, hr, hsound row value hr]

/-- Concrete all-pairs public observer. Correctness premises are on the
actual source matrix and errors, with no secret supplied to the observer. -/
theorem allPairs_two_completions {q n m : ℕ} [NeZero q]
    (a : Matrix (Fin n) (Fin m) (ZMod q)) (builder : Pair n → Matrix (Fin n) (Fin m) (ZMod q))
    (weight : ZMod q) (witness : Pair n → Matrix (Fin n) (Fin n) (ZMod q))
    (hc : ∀ pair, builder pair * a.transpose =
      coordinateTarget weight pair.1.1 pair.1.2 + witness pair - (witness pair).transpose)
    (hsupport : ∀ pair row, row ≠ pair.1.1 → row ≠ pair.1.2 → ∀ column, builder pair row column = 0)
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (bound : ℕ)
    (hfirst : ∀ pair, (LatticeCrypto.centeredRepr (dotProduct (builder pair pair.1.1) error)).natAbs ≤ bound)
    (hsecond : ∀ pair, (LatticeCrypto.centeredRepr (dotProduct (builder pair pair.1.2) error)).natAbs ≤ bound)
    (hmargin : 4 * bound < centeredDistance 0 weight) :
    let readings := fun pair : Pair n ↦ readPair a (builder pair) pair.1.1 pair.1.2
      (vecMul (GSWSelfKey.binaryEmbed bits) a + error) bound
    complete (collect readings) false = bits ∨ complete (collect readings) true = bits := by
  apply eq_one_of_two_completions
  · apply collect_sound
    intro pair
    exact readPair_real a (builder pair) weight pair.1.1 pair.1.2 pair.2 (witness pair)
      (hc pair) (hsupport pair) bits error bound (hfirst pair) (hsecond pair) hmargin
  · apply collect_pair_cover
    intro pair
    exact readPair_index a (builder pair) pair.1.1 pair.1.2 _ bound

def acceptsCompletions {q n : ℕ} [NeZero q] (observations : Fin n → Option Bool)
    (mask : Fin n → ZMod q) (body : ZMod q) (E : ℕ) : Prop :=
  (LatticeCrypto.centeredRepr (body - dotProduct (GSWSelfKey.binaryEmbed (complete observations false)) mask)).natAbs ≤ E ∨
    (LatticeCrypto.centeredRepr (body - dotProduct (GSWSelfKey.binaryEmbed (complete observations true)) mask)).natAbs ≤ E

theorem acceptsCompletions_real {q n : ℕ} [NeZero q]
    (observations : Fin n → Option Bool) (bits : Fin n → Bool)
    (hsound : ∀ row value, observations row = some value → value = bits row)
    (hcover : ∀ first second : Fin n, first ≠ second → observations first ≠ none ∨ observations second ≠ none)
    (mask : Fin n → ZMod q) (error : ZMod q) (E : ℕ)
    (herror : (LatticeCrypto.centeredRepr error).natAbs ≤ E) :
    acceptsCompletions observations mask (dotProduct (GSWSelfKey.binaryEmbed bits) mask + error) E := by
  rcases eq_one_of_two_completions observations bits hsound hcover with h | h
  · left
    simpa [h] using herror
  · right
    simpa [h] using herror

theorem uniform_acceptsCompletions_le {q n : ℕ} [NeZero q]
    (observations : Fin n → Option Bool) (mask : Fin n → ZMod q) (E : ℕ) :
    Pr[fun body : ZMod q ↦ acceptsCompletions observations mask body E | $ᵗ ZMod q] ≤
      2 * ((2 * E + 1 : ℝ≥0∞) / q) := by
  unfold acceptsCompletions
  calc
    _ ≤ _ + _ := probEvent_or_le ..
    _ ≤ ((2 * E + 1 : ℝ≥0∞) / q) + ((2 * E + 1 : ℝ≥0∞) / q) :=
      add_le_add (uniform_verification_acceptance_le E _) (uniform_verification_acceptance_le E _)
    _ = _ := (two_mul ((2 * E + 1 : ℝ≥0∞) / q)).symm

/-- The uniform verification bound retains an arbitrary earlier correlated
view and arbitrary public choice of the verification mask. Only the fresh
verification body is sampled independently. -/
def uniformVerification {q n : ℕ} [NeZero q]
    (earlierView : ProbComp ((Fin n → Option Bool) × (Fin n → ZMod q))) (E : ℕ) : ProbComp Bool := by
  classical
  exact do
    let observed ← earlierView
    (fun body : ZMod q ↦ decide (acceptsCompletions observed.1 observed.2 body E)) <$> ($ᵗ ZMod q)

theorem uniformVerification_le {q n : ℕ} [NeZero q]
    (earlierView : ProbComp ((Fin n → Option Bool) × (Fin n → ZMod q))) (E : ℕ) :
    Pr[= true | uniformVerification earlierView E] ≤ 2 * ((2 * E + 1 : ℝ≥0∞) / q) := by
  classical
  rw [← probEvent_true_eq_probOutput]
  unfold uniformVerification
  apply probEvent_bind_le_of_forall_le
  intro observed _
  rw [probEvent_map]
  simpa using uniform_acceptsCompletions_le observed.1 observed.2 E

/-- The SAME budget used for reusable native refresh already gives the
two-row attack's separation margin. Merely increasing the modulus within
that family does not protect a target-pair-supported builder. -/
theorem projected_error_le_keyBound {q m : ℕ} [NeZero q]
    (P : Polynomial ℕ) (parameter : ℕ) (pi error : Fin m → ZMod q)
    (hpi : ∑ column, (LatticeCrypto.centeredRepr (pi column)).natAbs ≤ P.eval parameter)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤
      RecursiveQuadraticParameters.radius parameter) :
    (LatticeCrypto.centeredRepr (dotProduct pi error)).natAbs ≤
      GSWQuadraticPreimageParameters.keyBound P parameter := by
  exact (projection_noise_bound pi error (P.eval parameter) (RecursiveQuadraticParameters.radius parameter)
    hpi herror).trans (Nat.mul_le_mul_right _ (by omega : P.eval parameter ≤ 1 + P.eval parameter))

/-- The refresh margin also separates the public two-row projections. -/
theorem compatible_budget_pair_margin (P : Polynomial ℕ) (parameter : ℕ)
    (hbudget : GSWQuadraticPreimageParameters.lookupModulus parameter *
      GSWQuadraticPreimageParameters.postNandBound P parameter < RecursiveQuadraticParameters.modulus parameter) :
    4 * GSWQuadraticPreimageParameters.keyBound P parameter <
      centeredDistance 0 (TFHE.Gadget.Base.gadget
        (GSWQuadraticPreimageParameters.params parameter
          (GSWQuadraticPreimageParameters.capacity_of_budget P parameter hbudget))
        (GSWQuadraticPreimageParameters.level parameter
          (GSWQuadraticPreimageParameters.capacity_of_budget P parameter hbudget))) := by
  have hd := GSWQuadraticPreimageParameters.dimension_ge parameter
  have hl := NeZero.pos (GSWQuadraticPreimageParameters.lookupModulus parameter)
  have hg : 0 < GSWQuadraticPreimageParameters.growth parameter := by
    unfold GSWQuadraticPreimageParameters.growth
    have hs := RecursiveQuadraticParameters.scale_pos parameter
    positivity
  have hfactor : 2 ≤ GSWQuadraticPreimageParameters.lookupModulus parameter *
      GSWQuadraticPreimageParameters.dimension parameter * GSWQuadraticPreimageParameters.growth parameter :=
    hd.trans ((Nat.le_mul_of_pos_left _ hl).trans (Nat.le_mul_of_pos_right _ hg))
  have houtput : 2 * GSWQuadraticPreimageParameters.keyBound P parameter ≤
      GSWQuadraticPreimageParameters.outputBound P parameter :=
    Nat.mul_le_mul_right _ hfactor
  rw [RecursiveFeatureBootstrapParameters.gadget_distance]
  change 4 * GSWQuadraticPreimageParameters.keyBound P parameter <
    GSWQuadraticPreimageParameters.factor parameter * (GSWQuadraticPreimageParameters.lookupModulus parameter / 2)
  have hm := GSWQuadraticPreimageParameters.output_margin P parameter hbudget
  omega

end

end FormalProof4FHE.LWE.GSWQuadraticPreimageTwoRows
