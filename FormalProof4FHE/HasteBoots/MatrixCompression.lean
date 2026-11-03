module

public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

@[expose] public section

/-!
# Detection by fresh packed coefficient-compression queries

A nonzero fixed packed polynomial table becomes zero under c sequential fresh
matrix folds with probability at most c*((2*b-1)/card(F))^b. A whole family of
fixed polynomial pairs shares one compression query: if any pair differs,
all compressed pairs agree only within that same bound, without a family-size
loss. Queries are source-independent and use the native ordered Lagrange
challenge matrices. Production transcript freshness remains a separate claim.
-/

open OracleSpec OracleComp
open scoped BigOperators
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.MatrixCompression

noncomputable section

variable {F : Type} [Field F] {b c : ℕ}

/-- Fresh private lane vectors in coefficient-variable order. -/
def sample [SampleableType (Fin b → F)] (nodes : PackedSumcheckRound.Node b ↪ F) :
    (c : ℕ) → ProbComp (Query F b c)
  | 0 => pure .nil
  | c + 1 => do
      let challenge ← $ᵗ (Fin b → F)
      let tail ← sample nodes c
      pure (.cons (PackedSumcheckRound.challengePair nodes challenge) tail)

/-- Any selected nonzero Boolean/lane entry forces a nonzero interpolation
polynomial for its suffix, before the new independent lane vector is sampled. -/
theorem factor_nonzero (nodes : PackedSumcheckRound.Node b ↪ F)
    (values : Bool → Fin b → F) (nonzero : ∃ bit lane, values bit lane ≠ 0) :
    PackedSumcheckRound.factorPolynomial nodes values ≠ 0 := by
  obtain ⟨bit, lane, different⟩ := nonzero
  intro equal
  have evaluated := PackedSumcheckRound.factorPolynomial_node nodes values bit lane
  rw [equal, Polynomial.eval_zero] at evaluated
  exact different evaluated.symm

variable [Fintype F] [DecidableEq F] [SampleableType (Fin b → F)]

/-- One matrix fold can kill the entire nonzero table only if all b output
lanes hit roots of one fixed nonzero degree-(2*b-1) polynomial. -/
theorem first_zero_bound (nodes : PackedSumcheckRound.Node b ↪ F)
    (table : MatrixFold.Cube (c + 1) → Fin b → F) (nonzero : table ≠ 0) :
    Pr{let challenge ← $ᵗ (Fin b → F)}[
      MatrixFold.foldFirst (PackedSumcheckRound.challengePair nodes challenge) table = 0] ≤
      (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  classical
  obtain ⟨⟨bit, suffix⟩, different⟩ := Function.ne_iff.mp nonzero
  obtain ⟨lane, different⟩ := Function.ne_iff.mp different
  let values := fun bit lane => table (bit, suffix) lane
  have polynomialNonzero := factor_nonzero nodes values ⟨bit, lane, different⟩
  have roots := PackedSumcheckProbability.all_agree_bound
    (PackedSumcheckRound.factorPolynomial nodes values) 0 (2 * b - 1) b
    polynomialNonzero (PackedSumcheckRound.factorPolynomial_degree nodes values) (by simp)
  apply le_trans (prEvent_mono _ _ _ ?_) roots
  intro challenge folded outLane
  have zero := congrFun (congrFun folded suffix) outLane
  simpa only [MatrixFold.foldFirst, PackedSumcheckRound.challengePair_fold, Pi.zero_apply,
    Polynomial.eval_zero, values] using zero

/-- Full sequential compression, including zero variables and arbitrary
noncommuting ordered challenge matrices. -/
theorem zero_bound (nodes : PackedSumcheckRound.Node b ↪ F) (c : ℕ)
    (table : MatrixFold.Cube c → Fin b → F) (nonzero : table ≠ 0) :
    Pr{let query ← sample nodes c}[query.fold table = 0] ≤
      (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  classical
  induction c with
  | zero =>
    have atZero : table () ≠ 0 := by
      intro equal
      apply nonzero
      funext cell
      cases cell
      exact equal
    simp only [sample, prEvent_pure, Query.fold, atZero, ite_false, Nat.cast_zero, zero_mul, le_refl]
  | succ c ih =>
    rw [sample]
    let healed := fun challenge : Fin b → F =>
      MatrixFold.foldFirst (PackedSumcheckRound.challengePair nodes challenge) table = 0
    have tailBound : ∀ challenge, ¬healed challenge →
        Pr{let query ← (do
          let tail ← sample nodes c
          pure (Query.cons (PackedSumcheckRound.challengePair nodes challenge) tail))}[query.fold table = 0] ≤
        (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
      intro challenge outside
      simpa only [prEvent_norm, Query.fold] using ih
        (MatrixFold.foldFirst (PackedSumcheckRound.challengePair nodes challenge) table) outside
    exact (prEvent_bind_le_prEvent_add ($ᵗ (Fin b → F)) _ healed _ tailBound).trans
      ((add_le_add (first_zero_bound nodes table nonzero) le_rfl).trans_eq (by
        simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]))

omit [Fintype F] [DecidableEq F] [SampleableType (Fin b → F)] in
/-- Compression is linear on source differences. -/
theorem fold_sub (query : Query F b c) (first second : MatrixFold.Cube c → Fin b → F) :
    query.fold (fun cell => first cell - second cell) = query.fold first - query.fold second := by
  simp only [Query.fold_eq_list, MatrixFold.foldAll_eq_weightedEvaluation,
    MatrixFold.weightedEvaluation, Matrix.mulVec_sub, Finset.sum_sub_distrib]

/-- Distinct fixed polynomial rows rarely have identical compressed vectors. -/
theorem agreement_bound (nodes : PackedSumcheckRound.Node b ↪ F)
    (first second : MatrixFold.Cube c → Fin b → F) (different : first ≠ second) :
    Pr{let query ← sample nodes c}[query.fold first = query.fold second] ≤
      (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  have nonzero : (fun cell => first cell - second cell) ≠ 0 := by
    intro equal
    apply different
    funext cell
    exact sub_eq_zero.mp (congrFun equal cell)
  simpa only [fold_sub, sub_eq_zero] using zero_bound nodes c (fun cell => first cell - second cell) nonzero

/-- All coefficient/evaluation rows may share this one query. Selecting one
fixed wrong row before compression incurs no union over the family size. -/
theorem family_agreement_bound {Row : Type} (nodes : PackedSumcheckRound.Node b ↪ F)
    (first second : Row → MatrixFold.Cube c → Fin b → F) (different : ∃ row, first row ≠ second row) :
    Pr{let query ← sample nodes c}[∀ row, query.fold (first row) = query.fold (second row)] ≤
      (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  obtain ⟨row, different⟩ := different
  exact (prEvent_mono _ _ _ (fun _ agrees => agrees row)).trans (agreement_bound nodes (first row) (second row) different)

end

end FormalProof4FHE.HasteBoots.MatrixCompression
