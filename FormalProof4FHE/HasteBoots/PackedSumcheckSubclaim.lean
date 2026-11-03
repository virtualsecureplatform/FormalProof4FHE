module

public import FormalProof4FHE.HasteBoots.PackedSumcheckExecution
public import FormalProof4FHE.HasteBoots.FlatMatrixFold

@[expose] public section

/-!
# Source-independent packed-sumcheck subclaims

The verifier returns an ordered matrix query and expected terminal value. It
does not inspect factor tables. Query dimension is indexed in the type; the
list projection preserves native variable order and low-bit source addresses.
Truthfulness is an analysis predicate on this returned obligation, to be
discharged later by authenticated factor openings.
-/

namespace FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

inductive Query (F : Type) (k : ℕ) : ℕ → Type
  | nil : Query F k 0
  | cons {n : ℕ} (pair : Bool → Matrix (Fin k) (Fin k) F) (tail : Query F k n) : Query F k (n + 1)

namespace Query

variable {F : Type} {k n : ℕ}

def toList : {n : ℕ} → Query F k n → List (Bool → Matrix (Fin k) (Fin k) F)
  | _, .nil => []
  | _, .cons pair tail => pair :: tail.toList

theorem length_toList (query : Query F k n) : query.toList.length = n := by
  induction query with
  | nil => rfl
  | cons pair tail ih => simp only [toList, List.length_cons, ih]

/-- The list conversion changes dimension bookkeeping, not Boolean coordinates. -/
def cubeEquiv : {n : ℕ} → (query : Query F k n) → MatrixFold.Cube n ≃ MatrixFold.Cube query.toList.length
  | _, .nil => Equiv.refl _
  | _, .cons _ tail => Equiv.prodCongr (Equiv.refl Bool) tail.cubeEquiv

theorem index_cubeEquiv (query : Query F k n) (cell : MatrixFold.Cube n) :
    (FlatMatrixFold.index query.toList.length (query.cubeEquiv cell)).val =
      (FlatMatrixFold.index n cell).val := by
  induction query with
  | nil => rfl
  | cons pair tail ih =>
    rcases cell with ⟨bit, suffix⟩
    change (FlatMatrixFold.index (tail.toList.length + 1) (bit, tail.cubeEquiv suffix)).val =
      (FlatMatrixFold.index (_ + 1) (bit, suffix)).val
    rw [FlatMatrixFold.index_succ_val, FlatMatrixFold.index_succ_val, ih suffix]

variable [Field F]

def fold : {n : ℕ} → Query F k n → (MatrixFold.Cube n → Fin k → F) → Fin k → F
  | _, .nil, table => table ()
  | _, .cons pair tail, table => tail.fold (MatrixFold.foldFirst pair table)

/-- Returned query matrices have exactly the already-proved native list-fold
semantics, with no source-dependent query construction. -/
theorem fold_eq_list (query : Query F k n) (table : MatrixFold.Cube n → Fin k → F) :
    query.fold table = MatrixFold.foldAll query.toList (fun cell => table (query.cubeEquiv.symm cell)) := by
  induction query with
  | nil => rfl
  | cons pair tail ih =>
    change tail.fold (MatrixFold.foldFirst pair table) = MatrixFold.foldAll (pair :: tail.toList)
      (fun cell => table ((Equiv.prodCongr (Equiv.refl Bool) tail.cubeEquiv).symm cell))
    rw [ih, MatrixFold.foldAll]
    congr 1

end Query

structure Subclaim (F : Type) (k n : ℕ) where
  query : Query F k n
  expected : Fin k → F

namespace Subclaim

variable {F Factor Term : Type} [Field F] [Fintype Term] {k n : ℕ}

def prepend (pair : MatrixFold.Pair (F := F) (Lane := Fin k)) (claim : Subclaim F k n) : Subclaim F k (n + 1) :=
  ⟨.cons pair claim.query, claim.expected⟩

def Truthful (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (claim : Subclaim F k n) : Prop :=
  claim.expected = fun lane => PackedSumcheckRound.expression arity coefficient indices
    (fun factor => claim.query.fold (tables factor) lane)

theorem truthful_zero_iff (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor 0 k) (expected : Fin k → F) :
    Truthful arity coefficient indices tables ⟨.nil, expected⟩ ↔
      expected = PackedSumcheckExecution.sum arity coefficient indices tables := by
  have same : (fun lane => PackedSumcheckRound.expression arity coefficient indices
      (fun factor => tables factor () lane)) = PackedSumcheckExecution.sum arity coefficient indices tables := by
    funext lane
    change (PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor () lane)) =
      ∑ cell : Unit, PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor cell lane)
    exact (Fintype.sum_subsingleton
      (fun cell : Unit => PackedSumcheckRound.expression arity coefficient indices (fun factor => tables factor cell lane)) ()).symm
  constructor
  · intro truthful
    exact truthful.trans same
  · intro equal
    exact equal.trans same.symm

/-- Consuming the first returned matrix pair folds the same original factor
sources once; it never chooses a new source for the remaining query. -/
theorem truthful_prepend_iff (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (pair : MatrixFold.Pair (F := F) (Lane := Fin k)) (claim : Subclaim F k n) :
    Truthful arity coefficient indices tables (prepend pair claim) ↔
      Truthful arity coefficient indices (fun factor => MatrixFold.foldFirst pair (tables factor)) claim := Iff.rfl

end Subclaim

end FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
