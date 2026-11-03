module

public import FormalProof4FHE.HasteBoots.MatrixFold
public import FormalProof4FHE.HasteBoots.MatrixResponse
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Flat, least-significant-bit-first matrix folding

The first Boolean variable is the low address bit. Each native fold therefore
reads cell 2*i and cell 2*i+1, then writes cell i. The zero-variable case keeps
the only remaining vector. These definitions describe the validated native
array loop mathematically; Rust memory/word-size refinement remains separate.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.FlatMatrixFold

/-- Explicit bijection from the semantic Boolean cube to native cell addresses. -/
def index : (n : ℕ) → MatrixFold.Cube n ≃ Fin (2 ^ n)
  | 0 => show Unit ≃ Fin 1 from Equiv.ofUnique _ _
  | n + 1 =>
    (Equiv.prodCongr finTwoEquiv.symm (index n)).trans
      ((Equiv.prodComm (Fin 2) (Fin (2 ^ n))).trans
        (finProdFinEquiv.trans (finCongr (Nat.pow_succ 2 n).symm)))

/-- The child addresses read by a fold, before the output prefix is shortened. -/
def child {n : ℕ} (bit : Bool) (suffix : Fin (2 ^ n)) : Fin (2 ^ (n + 1)) :=
  ⟨2 * suffix.val + (if bit then 1 else 0), by
    have bound := suffix.isLt
    rw [Nat.pow_succ]
    split <;> omega⟩

/-- The first cube coordinate is exactly the low bit of the native address. -/
theorem index_succ_val {n : ℕ} (bit : Bool) (suffix : MatrixFold.Cube n) :
    (index (n + 1) (bit, suffix)).val =
      2 * (index n suffix).val + (if bit then 1 else 0) := by
  change (finTwoEquiv.symm bit).val + 2 * (index n suffix).val = _
  cases bit <;> simp [finTwoEquiv, Nat.add_comm]

theorem index_succ {n : ℕ} (bit : Bool) (suffix : MatrixFold.Cube n) :
    index (n + 1) (bit, suffix) = child bit (index n suffix) := by
  apply Fin.ext
  exact index_succ_val bit suffix

variable {F Lane : Type} [Semiring F] [Fintype Lane] [DecidableEq Lane]

/-- One validated native fold: multiply zero and one slices, then add them. -/
def foldFirst {n : ℕ} (pair : MatrixFold.Pair (F := F) (Lane := Lane))
    (table : Fin (2 ^ (n + 1)) → Lane → F) : Fin (2 ^ n) → Lane → F :=
  fun suffix => pair false *ᵥ table (child false suffix) + pair true *ᵥ table (child true suffix)

omit [DecidableEq Lane] in
/-- The constant-lane optimization computes the same vector as the general loop. -/
theorem foldFirst_constant {n : ℕ} (pair : MatrixFold.Pair (F := F) (Lane := Lane))
    (vector : Lane → F) :
    foldFirst (n := n) pair (fun _ => vector) =
      fun _ => pair false *ᵥ vector + pair true *ᵥ vector := rfl

omit [DecidableEq Lane] in
/-- Native adjacent-cell folding agrees with semantic Boolean-variable folding. -/
theorem foldFirst_index {n : ℕ} (pair : MatrixFold.Pair (F := F) (Lane := Lane))
    (table : Fin (2 ^ (n + 1)) → Lane → F) :
    MatrixFold.foldFirst pair (fun cell => table (index (n + 1) cell)) =
      fun suffix => foldFirst pair table (index n suffix) := by
  classical
  funext suffix
  simp only [MatrixFold.foldFirst, Fintype.sum_bool, index_succ, foldFirst]
  exact add_comm _ _

/-- Execute the validated flat array fold in native variable order. -/
def foldAll : (query : List (MatrixFold.Pair (F := F) (Lane := Lane))) →
    (Fin (2 ^ query.length) → Lane → F) → Lane → F
  | [], table => table 0
  | pair :: tail, table => foldAll tail (foldFirst pair table)

omit [DecidableEq Lane] in
/-- Complete flat and Boolean-cube fold executions are equal, including zero rounds. -/
theorem foldAll_eq_cube (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (table : Fin (2 ^ query.length) → Lane → F) :
    foldAll query table = MatrixFold.foldAll query (fun cell => table (index query.length cell)) := by
  induction query with
  | nil =>
    change table 0 = table (index 0 ())
    exact congrArg table (show (0 : Fin 1) = index 0 () from Subsingleton.elim _ _)
  | cons pair tail ih =>
    rw [foldAll, ih, MatrixFold.foldAll]
    congr 1
    exact (foldFirst_index (n := tail.length) pair table).symm

/-- Tensor weights indexed by the same flat addresses as the native table. -/
def weights (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (cell : Fin (2 ^ query.length)) : Matrix Lane Lane F :=
  MatrixFold.weight query ((index query.length).symm cell)

/-- The flat loop computes the ordered tensor evaluation at native addresses. -/
theorem foldAll_eq_weighted (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (table : Fin (2 ^ query.length) → Lane → F) :
    foldAll query table = ∑ cell, weights query cell *ᵥ table cell := by
  rw [foldAll_eq_cube, MatrixFold.foldAll_eq_weightedEvaluation]
  unfold MatrixFold.weightedEvaluation
  simpa only [weights, Equiv.symm_apply_apply] using
    (index query.length).sum_comp (fun cell => weights query cell *ᵥ table cell)

/-- Native lane-major response finishing executes precisely the same flat fold. -/
theorem finishMessage_eq_fold {K : Type} [Field K] {b : ℕ}
    (query : List (MatrixFold.Pair (F := K) (Lane := Fin b)))
    (messages : Fin b → Fin (2 ^ query.length) → K) :
    MatrixResponse.finishMessage (weights query) messages =
      foldAll query (fun cell lane => messages lane cell) := by
  rw [foldAll_eq_weighted]
  rfl

end FormalProof4FHE.HasteBoots.FlatMatrixFold
