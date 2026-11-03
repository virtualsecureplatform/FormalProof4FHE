module

public import FormalProof4FHE.HasteBoots.LookupSourceFlattening
public import FormalProof4FHE.HasteBoots.PackedSumcheckSharedSoundness

@[expose] public section

/-!
# Ordinary scalar sumcheck points inside the checked shared verifier

The width-one consecutive Boolean interpolation nodes are zero and one.
Their challenge matrices are [1-x] and [x]. The returned ordered query thus
represents the ordinary low-coordinate-first MLE at its extracted point.
These semantic adapters retain the existing shared verifier and its work;
lookup authentication, transcript and Rust refinement remain separate.
-/

open scoped BigOperators Classical
open Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.ScalarSumcheckQuery

noncomputable section

variable {K : Type} [Field K] {n : ℕ}

private theorem node_univ : (Finset.univ : Finset (PackedSumcheckRound.Node 1)) = {(false, 0), (true, 0)} := by
  ext ⟨bit, lane⟩
  fin_cases lane
  cases bit <;> simp

/-- Exact native width-one interpolation weights, including Boolean points. -/
theorem native_pair (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p) (challenge : Fin 1 → K)
    (bit : Bool) (outLane inLane : Fin 1) :
    PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes p small) challenge bit outLane inLane =
      if bit then challenge 0 else 1 - challenge 0 := by
  rw [PackedSumcheckRound.challengePair, NativePackedInterpolation.basis_eval, node_univ]
  fin_cases outLane
  fin_cases inLane
  cases bit
  · simp [NativePackedInterpolation.nodes, NativePackedInterpolation.nodeIndex,
      NativePackedInterpolation.consecutive, div_neg, sub_eq_add_neg]
  · erw [show ({(false, 0), (true, 0)} : Finset (PackedSumcheckRound.Node 1)).erase (true, 0) = {(false, 0)} by decide]
    simp [NativePackedInterpolation.nodes, NativePackedInterpolation.nodeIndex, NativePackedInterpolation.consecutive]

def query : (n : ℕ) → (Fin n → K) → Query K 1 n
  | 0, _ => .nil
  | n + 1, point => .cons (fun bit _ _ => if bit then point 0 else 1 - point 0)
      (query n (fun i => point i.succ))

def point : {n : ℕ} → Query K 1 n → Fin n → K
  | _, .nil => Fin.elim0
  | _, .cons pair tail => Fin.cons (pair true 0 0) (point tail)

def Scalar (q : Query K 1 n) : Prop := q = query n (point q)

theorem point_query (coordinates : Fin n → K) : point (query n coordinates) = coordinates := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun j => coordinates j.succ)) j

theorem scalar_query (coordinates : Fin n → K) : Scalar (query n coordinates) := by
  unfold Scalar
  rw [point_query]

theorem scalar_nil : Scalar (Query.nil : Query K 1 0) := rfl

theorem scalar_prepend (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (challenge : Fin 1 → K) (tail : Query K 1 n) (valid : Scalar tail) :
    Scalar (.cons (PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes p small) challenge) tail) := by
  have pairEq : PackedSumcheckRound.challengePair (NativePackedInterpolation.nodes p small) challenge =
      fun bit (_ _ : Fin 1) => if bit then challenge 0 else 1 - challenge 0 := by
    funext bit outLane inLane
    exact native_pair p small challenge bit outLane inLane
  change Query.cons _ tail = query (n + 1) (Fin.cons _ (point tail))
  rw [pairEq]
  simp only [query, Fin.cons_zero, Fin.cons_succ, ite_true]
  exact congrArg (Query.cons _) valid

/-- Ordinary MLE evaluation of each scalar factor is exactly the existing
query-fold obligation returned by scalar sumcheck. -/
theorem fold_query (coordinates : Fin n → K) (table : MatrixFold.Cube n → K) :
    (query n coordinates).fold (fun cell (_ : Fin 1) => table cell) =
      fun _ => ExtensionQuery.evaluate n coordinates table := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (query n (fun i => coordinates i.succ)).fold
      (MatrixFold.foldFirst (fun bit (_ _ : Fin 1) => if bit then coordinates 0 else 1 - coordinates 0)
        (fun cell (_ : Fin 1) => table cell)) = _
    have first : MatrixFold.foldFirst (fun bit (_ _ : Fin 1) => if bit then coordinates 0 else 1 - coordinates 0)
        (fun cell (_ : Fin 1) => table cell) =
        fun suffix (_ : Fin 1) => (1 - coordinates 0) * table (false, suffix) + coordinates 0 * table (true, suffix) := by
      funext suffix lane
      simp only [MatrixFold.foldFirst, Fintype.sum_bool, Pi.add_apply]
      change (∑ j : Fin 1, coordinates 0 * table (true, suffix)) +
        (∑ j : Fin 1, (1 - coordinates 0) * table (false, suffix)) = _
      simp only [Fin.sum_univ_one]
      exact add_comm _ _
    rw [first, ih]
    rfl

theorem fold_scalar (q : Query K 1 n) (valid : Scalar q) (table : MatrixFold.Cube n → K) :
    q.fold (fun cell (_ : Fin 1) => table cell) = fun _ => ExtensionQuery.evaluate n (point q) table := by
  rw [valid, fold_query, point_query]

/-- No supplied terminal certificate: the existing Truthful predicate is
exactly the ordinary scalar factor expression at the extracted point. -/
theorem truthful_iff {Factor Term : Type} [Fintype Term] (arity : Term → ℕ) (coefficient : Term → K)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → MatrixFold.Cube n → K) (claim : Subclaim K 1 n) (valid : Scalar claim.query) :
    claim.Truthful arity coefficient indices (fun factor cell _ => tables factor cell) ↔
      claim.expected 0 = PackedSumcheckRound.expression arity coefficient indices
        (fun factor => ExtensionQuery.evaluate n (point claim.query) (tables factor)) := by
  unfold Subclaim.Truthful
  simp only [fold_scalar claim.query valid]
  constructor
  · intro equal
    exact congrFun equal 0
  · intro equal
    funext lane
    fin_cases lane
    exact equal

end

end FormalProof4FHE.HasteBoots.ScalarSumcheckQuery
