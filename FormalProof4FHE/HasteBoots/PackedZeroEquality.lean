module

public import FormalProof4FHE.HasteBoots.PackedZeroMixing
public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.Degrees
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

@[expose] public section

/-!
# Independent equality-point detection for packed ZeroCheck

For any fixed nonzero Boolean constraint slice, the equality-weighted sum is
its nonzero multilinear extension of total degree at most n. All k independent
equality points miss that slice with probability at most (n/card(F))^k. The
first-message family is still allowed to depend on these points afterwards.
The native flat-table adapter is supplied by `PackedEqualityCube` and
`NativeEqualityTable`; production transcript/Rust refinement remains open.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.PackedZeroEquality

noncomputable section

variable {F : Type} [Field F] {n k : ℕ}

abbrev Cell (n : ℕ) := Fin n → Fin 2

/-- Equality-table weight for one Boolean suffix cell. -/
def equality (point : Fin n → F) (cell : Cell n) : F :=
  MvPolynomial.eqTilde (fun index => (cell index : F)) point

/-- The literal multiplicative weights used to construct the native EQ table. -/
theorem equality_prod (point : Fin n → F) (cell : Cell n) :
    equality point cell = ∏ index, if cell index = 0 then 1 - point index else point index := by
  simp only [equality, MvPolynomial.eqTilde, MvPolynomial.eqPolynomial_zeroOne, MvPolynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro index _
  by_cases zero : cell index = 0 <;> simp [zero]

/-- The equality-weighted table sum is precisely its multilinear extension. -/
theorem weighted_sum (point : Fin n → F) (values : Cell n → F) :
    (∑ cell, equality point cell * values cell) = MvPolynomial.eval point (MvPolynomial.MLE values) :=
  (MvPolynomial.MLE_eval point values).symm

theorem mle_degree (values : Cell n → F) : (MvPolynomial.MLE values).totalDegree ≤ n := by
  simpa only [Fintype.card_fin] using
    MvPolynomial.totalDegree_le_card_of_degreeOf_le_one (MvPolynomial.MLE values)
      (MvPolynomial.MLE_degreeOf values)

/-- One independent equality point detects a fixed nonzero constraint slice
except with the ordinary multilinear degree-over-field-size probability. -/
theorem point_bound [Fintype F] [SampleableType F] [SampleableType (Fin n → F)]
    (values : Cell n → F) (nonzero : ∃ cell, values cell ≠ 0) :
    Pr{let point ← $ᵗ (Fin n → F)}[(∑ cell, equality point cell * values cell) = 0] ≤
      (n : ENNReal) / Fintype.card F := by
  classical
  have polynomialNonzero : MvPolynomial.MLE values ≠ 0 := by
    intro equal
    obtain ⟨cell, nonzero⟩ := nonzero
    exact nonzero ((MvPolynomial.MLE_eq_zero_iff values).mp equal cell)
  rw [SampleableType.prEvent_uniformSample]
  apply ENNReal.div_le_div_of_mul_le Fintype.card_pos Fintype.card_pos
  have count := schwartz_zippel_counting (MvPolynomial.MLE values) polynomialNonzero
    (fun _ => Finset.univ) n (Fintype.card F) (mle_degree values) Fintype.card_pos
      (fun _ => by simp)
  simpa only [weighted_sum, Fintype.piFinset_univ, Finset.card_univ, Finset.prod_const,
    Fintype.card_fin, Fintype.card_fun] using count

/-- Repeated equality points remain k independent draws; no distinctness of
the sampled points is required. -/
theorem points_bound [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType (Fin n → F)] [SampleableType (Fin k → (Fin n → F))]
    (values : Cell n → F) (nonzero : ∃ cell, values cell ≠ 0) :
    Pr{let points ← $ᵗ (Fin k → (Fin n → F))}[
      ∀ lane, (∑ cell, equality (points lane) cell * values cell) = 0] ≤
      (((n : ENNReal) / Fintype.card F) ^ k) := by
  rw [PackedZeroMixing.all_rows_probability (k := k)
    (fun point : Fin n → F => (∑ cell, equality point cell * values cell) = 0)]
  exact pow_le_pow_left₀ zero_le (point_bound values nonzero) k

/-- A false relation has a fixed Boolean/lane slice. If every honest first
polynomial satisfies the boundary check, all equality points missed that slice. -/
theorem boundary_miss_bound [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType (Fin n → F)] [SampleableType (Fin k → (Fin n → F))]
    {Factor Term : Type} [Fintype Term]
    (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Cell n → Fin k → F)
    (falseRelation : ¬PackedZeroFirst.Vanishes arity coefficient indices tables) :
    Pr{let points ← $ᵗ (Fin k → (Fin n → F))}[
      PackedZeroFirst.Boundary nodes (PackedZeroFirst.polynomial nodes arity coefficient indices tables
        (fun lane => equality (points lane)))] ≤ (((n : ENNReal) / Fintype.card F) ^ k) := by
  classical
  change ¬∀ bit suffix lane, _ = 0 at falseRelation
  push Not at falseRelation
  obtain ⟨bit, suffix, lane, nonzero⟩ := falseRelation
  apply le_trans (prEvent_mono _ _ _ ?_)
    (points_bound (fun cell => PackedSumcheckRound.expression arity coefficient indices
      (fun factor => tables factor bit cell lane)) ⟨suffix, nonzero⟩)
  intro points checked point
  simpa only [PackedZeroFirst.polynomial_node] using checked point bit lane

end

end FormalProof4FHE.HasteBoots.PackedZeroEquality
