module

public import FormalProof4FHE.HasteBoots.NativeGoldMultiplicationMatrix
public import FormalProof4FHE.HasteBoots.ExtensionQuery

@[expose] public section

/-!
# Checked raw native helper-query construction

The ordered raw pairs are M(1-x), M(x). Only the empty point carries the
M(1) post-matrix. The semantic reader validates the actual raw matrices and
pair count, deriving their field coefficients from their stored payloads.
No query-correctness certificate or extension-field commitment is an input.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldCoefficientsQuery

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldMultiplicationMatrix (matrix multiplication)

structure Pair where
  zero : NativeGoldMatrix.Matrix
  one : NativeGoldMatrix.Matrix
  deriving DecidableEq

structure Query where
  pairs : List Pair
  post : Option NativeGoldMatrix.Matrix
  deriving DecidableEq

def constructPairs (width : ℕ) : List Word → Option (List Pair)
  | [] => some []
  | value :: tail => (multiplication width (NativeGoldExtensionArithmetic.sub NativeGoldLookup.one value)).bind
      (fun zero => (multiplication width value).bind (fun one =>
        (constructPairs width tail).map (fun rest => ⟨zero, one⟩ :: rest)))

def coefficientsQuery (width : ℕ) (point : List Word) : Option Query :=
  if NativeGoldProjection.dimensions width then
    (constructPairs width point).bind (fun pairs =>
      if point.isEmpty then (multiplication width NativeGoldLookup.one).map (fun post => ⟨pairs, some post⟩)
      else some ⟨pairs, none⟩)
  else none

/-- This closed payload is derived below from all actual constructor checks. -/
def built (width : ℕ) (point : List Word) : Query :=
  ⟨point.map (fun value => ⟨matrix width (NativeGoldExtensionArithmetic.sub NativeGoldLookup.one value),
    matrix width value⟩), if point.isEmpty then some (matrix width NativeGoldLookup.one) else none⟩

theorem constructPairs_success (width : ℕ) (point : List Word)
    (shape : NativeGoldProjection.dimensions width = true) :
    constructPairs width point = some (built width point).pairs := by
  induction point with
  | nil => rfl
  | cons value tail ih =>
    simp only [constructPairs, NativeGoldMultiplicationMatrix.multiplication_success _ _ shape,
      Option.bind_some, ih, Option.map_some, built, List.map_cons]

theorem coefficientsQuery_success (width : ℕ) (point : List Word)
    (shape : NativeGoldProjection.dimensions width = true) :
    coefficientsQuery width point = some (built width point) := by
  rw [coefficientsQuery, ite_eq_left shape, constructPairs_success width point shape, Option.bind_some]
  cases point with
  | nil => simp only [List.isEmpty_nil, ite_true, NativeGoldMultiplicationMatrix.multiplication_success _ _ shape,
      Option.map_some, built, List.map_nil]
  | cons value tail => simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, built, List.map_cons]

theorem coefficientsQuery_invalid (width : ℕ) (point : List Word)
    (invalid : NativeGoldProjection.dimensions width ≠ true) : coefficientsQuery width point = none := by
  rw [coefficientsQuery, ite_eq_right invalid]

theorem built_length (width : ℕ) (point : List Word) : (built width point).pairs.length = point.length := by
  simp only [built, List.length_map]

noncomputable section

/-- Interpret the actual validated payload, retaining malformed shape as failure. -/
def readMatrix (width : ℕ) (raw : NativeGoldMatrix.Matrix) :
    Option (_root_.Matrix (Fin width) (Fin width) Goldilocks) :=
  if valid : NativeGoldMatrix.validate raw width = true then
    some (NativeGoldMatrixMeaning.semantic width raw valid) else none

def readPairs (width : ℕ) : (n : ℕ) → List Pair → Option (PackedSumcheckSubclaim.Query Goldilocks width n)
  | 0, [] => some .nil
  | n + 1, pair :: tail => (readMatrix width pair.zero).bind (fun zero =>
      (readMatrix width pair.one).bind (fun one =>
        (readPairs width n tail).map (fun rest => .cons (fun bit => if bit then one else zero) rest)))
  | _, _ => none

/-- A reader cannot silently truncate extra or missing query pairs. -/
theorem readPairs_wrong_length (width n : ℕ) (raw : List Pair) (wrong : raw.length ≠ n) :
    readPairs width n raw = none := by
  induction n generalizing raw with
  | zero =>
    cases raw with
    | nil => exact False.elim (wrong rfl)
    | cons pair tail => rfl
  | succ n ih =>
    cases raw with
    | nil => rfl
    | cons pair tail =>
      have tailWrong : tail.length ≠ n := by
        intro same
        exact wrong (by rw [List.length_cons, same])
      cases first : readMatrix width pair.zero <;> cases second : readMatrix width pair.one <;>
        simp only [readPairs, first, second, Option.bind_none, Option.bind_some, ih tail tailWrong, Option.map_none]

def readPost (width : ℕ) : Option NativeGoldMatrix.Matrix →
    Option (Option (_root_.Matrix (Fin width) (Fin width) Goldilocks))
  | none => some none
  | some raw => (readMatrix width raw).map some

def interpret (width n : ℕ) (raw : Query) : Option (ExtensionQuery.Broadcast Goldilocks width n) :=
  (readPairs width n raw.pairs).bind (fun pairs => (readPost width raw.post).map (fun post => ⟨pairs, post⟩))

theorem readMatrix_constructed {padding : ℕ} (value : Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    readMatrix (3 + padding) (matrix (3 + padding) value) = some
      (PaddedExtension.multiplication (padding := padding) goldilocksBasis (goldExtensionValue value)) := by
  rw [readMatrix, dite_eq_left (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape),
    NativeGoldMultiplicationMatrix.semantic_eq value shape]

theorem readPairs_built {padding n : ℕ} (point : Fin n → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    readPairs (3 + padding) n (built (3 + padding) (List.ofFn point)).pairs =
      some (ExtensionQuery.coefficients (padding := padding) goldilocksBasis n (fun i => goldExtensionValue (point i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, built, List.map_cons, readPairs, readMatrix_constructed _ shape,
      Option.bind_some, NativeGoldExtensionArithmetic.sub_value, NativeGoldLookup.one_value]
    have rest := ih (fun i => point i.succ)
    change readPairs (3 + padding) n
      ((List.ofFn (fun i => point i.succ)).map (fun value =>
        ⟨matrix (3 + padding) (NativeGoldExtensionArithmetic.sub NativeGoldLookup.one value), matrix (3 + padding) value⟩)) = _ at rest
    rw [rest, Option.map_some, ExtensionQuery.coefficients]
    congr 2
    funext bit
    cases bit <;> rfl

/-- Successful raw construction reads as exactly the existing helper query,
including the checked projection for an empty point. -/
theorem interpret_built {padding n : ℕ} (point : Fin n → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    interpret (3 + padding) n (built (3 + padding) (List.ofFn point)) =
      some (ExtensionQuery.coefficientsQuery (padding := padding) goldilocksBasis (fun i => goldExtensionValue (point i))) := by
  rw [interpret, readPairs_built point shape, Option.bind_some]
  cases n with
  | zero =>
    simp only [List.ofFn_zero, built, List.isEmpty_nil, ite_true, readPost,
      readMatrix_constructed _ shape, NativeGoldLookup.one_value, Option.map_some,
      ExtensionQuery.coefficientsQuery, ExtensionQuery.coefficients]
  | succ n =>
    simp only [List.ofFn_succ, built, List.isEmpty_cons, Bool.false_eq_true, ite_false,
      readPost, Option.map_some, ExtensionQuery.coefficientsQuery, Nat.succ_ne_zero]

theorem coefficientsQuery_value {padding n : ℕ} (point : Fin n → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    (coefficientsQuery (3 + padding) (List.ofFn point)).bind (interpret (3 + padding) n) =
      some (ExtensionQuery.coefficientsQuery (padding := padding) goldilocksBasis (fun i => goldExtensionValue (point i))) := by
  rw [coefficientsQuery_success _ _ shape, Option.bind_some, interpret_built point shape]

/-- The generic helper-MLE evaluation now consumes the interpreted query
constructed from these actual raw point words and coefficient payloads. -/
theorem coefficientsQuery_evaluate {padding n : ℕ} (point : Fin n → Word)
    (table : MatrixFold.Cube n → Fin (3 + padding) → Goldilocks)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    ((coefficientsQuery (3 + padding) (List.ofFn point)).bind (interpret (3 + padding) n)).map
      (fun query => query.evaluate table) = some (PaddedExtension.encode (padding := padding) goldilocksBasis
        (ExtensionQuery.evaluate n (fun i => goldExtensionValue (point i))
          (fun cell => PaddedExtension.decode goldilocksBasis (table cell)))) := by
  rw [coefficientsQuery_value point shape, Option.map_some, ExtensionQuery.coefficients_evaluate]

end

end FormalProof4FHE.HasteBoots.NativeGoldCoefficientsQuery
