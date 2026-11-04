module

public import FormalProof4FHE.HasteBoots.NativeGoldArithmetic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Native raw Goldilocks matrix shape and accumulation

Matrix payloads stay row-major raw words. Validation retains the native
nonzero width, trusted-width equality, checked usize square and full length.
Matrix-vector output uses the literal ascending-column multiply/add fold.
This is an arithmetic model; instruction/scheduler refinement remains open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMatrix

open NativeFields NativeFieldRepresentation

structure Matrix where
  width : ℕ
  values : List GoldWord
  deriving DecidableEq

def validate (matrix : Matrix) (width : ℕ) : Bool :=
  decide (width ≠ 0) && decide (matrix.width = width) &&
    decide (width * width < 2 ^ 64) && decide (matrix.values.length = width * width)

def checked (width : ℕ) (values : List GoldWord) : Option Matrix :=
  if validate ⟨width, values⟩ width then some ⟨width, values⟩ else none

def dotFrom (pairs : List (GoldWord × GoldWord)) (out : GoldWord) : GoldWord :=
  pairs.foldl (fun current pair =>
    NativeGoldArithmetic.add current (NativeGoldArithmetic.mul pair.1 pair.2)) out

def dot (row vector : List GoldWord) : GoldWord := dotFrom (row.zip vector) 0

def row (matrix : Matrix) (index : ℕ) : List GoldWord :=
  (matrix.values.drop (index * matrix.width)).take matrix.width

/-- Native `BroadcastQuery::apply`'s checked post-matrix application, with
zero-initialized output and every column accumulated in original order. -/
def apply (width : ℕ) (matrix : Matrix) (vector : List GoldWord) : Option (List GoldWord) :=
  if width = 0 ∨ vector.length ≠ width then none else
    if validate matrix width then some ((List.range width).map (fun index => dot (row matrix index) vector)) else none

theorem validate_iff (matrix : Matrix) (width : ℕ) : validate matrix width = true ↔
    width ≠ 0 ∧ matrix.width = width ∧ width * width < 2 ^ 64 ∧ matrix.values.length = width * width := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem checked_iff (width : ℕ) (values : List GoldWord) (matrix : Matrix) :
    checked width values = some matrix ↔ width ≠ 0 ∧ width * width < 2 ^ 64 ∧
      values.length = width * width ∧ matrix = ⟨width, values⟩ := by
  by_cases valid : validate ⟨width, values⟩ width = true
  · rw [checked, ite_eq_left valid, Option.some.injEq]
    have shape := (validate_iff _ _).mp valid
    exact ⟨fun equal => ⟨shape.1, shape.2.2.1, shape.2.2.2, equal.symm⟩,
      fun accepted => accepted.2.2.2.symm⟩
  · rw [checked, ite_eq_right valid]
    constructor
    · intro impossible; contradiction
    · rintro ⟨nonzero, fits, length, same⟩
      exact False.elim (valid ((validate_iff _ _).mpr ⟨nonzero, rfl, fits, length⟩))

theorem dotFrom_value (pairs : List (GoldWord × GoldWord)) (out : GoldWord) :
    goldValue (dotFrom pairs out) = goldValue out +
      (pairs.map (fun pair => goldValue pair.1 * goldValue pair.2)).sum := by
  have grouped : dotFrom pairs out =
      (pairs.map (fun pair => NativeGoldArithmetic.mul pair.1 pair.2)).foldl NativeGoldArithmetic.add out := by
    rw [dotFrom, List.foldl_map]
  rw [grouped, NativeGoldArithmetic.fold_add_value]
  simp only [List.map_map, Function.comp_def, NativeGoldArithmetic.mul_value]

theorem dot_value (row vector : List GoldWord) : goldValue (dot row vector) =
    ((row.zip vector).map (fun pair => goldValue pair.1 * goldValue pair.2)).sum := by
  rw [dot, dotFrom_value]
  simp only [goldValue, Fin.val_zero, Nat.cast_zero, zero_add]

theorem apply_length (width : ℕ) (matrix : Matrix) (vector output : List GoldWord)
    (success : apply width matrix vector = some output) : output.length = width := by
  unfold apply at success
  split at success
  · contradiction
  · split at success
    · have same := Option.some.inj success
      rw [← same, List.length_map, List.length_range]
    · contradiction

end FormalProof4FHE.HasteBoots.NativeGoldMatrix
