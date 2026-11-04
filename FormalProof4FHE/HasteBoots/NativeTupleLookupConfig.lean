module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupValues
public import FormalProof4FHE.HasteBoots.NativeGoldInverse

@[expose] public section

/-!
# Native tuple configuration rebuilding and backend normalization

Width is derived from the first public row, never from proof metadata.
Uniqueness uses native Goldilocks semantic equality/hash keys, including
lazy representatives. Normalization preserves every row and its position;
legacy Brakedown retains raw words, while canonicalizing backends reduce
them. Native usize vector domains and Rust/HashSet refinement are separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeTupleLookupConfig

open NativeFields NativeFieldRepresentation NativeFieldWire
open NativeSharedLookupValues (Policy)
open NativeSharedLookupStatement (Request)
open NativeUsizeMessage (Usize)

def normalizeWord : Policy → GoldWord → GoldWord
  | .retain, value => value
  | .canonical, value => NativeGoldInverse.canonical value

def normalizeRow (policy : Policy) (row : List GoldWord) : List GoldWord := row.map (normalizeWord policy)
def normalizeTable (policy : Policy) (table : List (List GoldWord)) : List (List GoldWord) := table.map (normalizeRow policy)

def rowKey (row : List GoldWord) : List ℕ := row.map goldCanonical

def columns (table : List (List GoldWord)) : ℕ := table.head?.map List.length |>.getD 0

def valid (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord)) : Bool :=
  decide (logicalLength.val ≠ 0) && decide (columns table ≠ 0) && decide (repetitions ≠ 0) &&
    table.all (fun row => decide (row.length = columns table)) &&
    decide ((table.map rowKey).Nodup) &&
    decide (logicalLength.val + table.length - 1 < goldilocksModulus) &&
    decide (table.length + 1 < goldilocksModulus)

def rebuild (policy : Policy) (request : Request) : Option Request :=
  let table := normalizeTable policy request.table
  if valid request.terminal.logicalLength request.repetitions table then
    some {request with columns := columns table, table := table}
  else none

theorem normalizeWord_value (policy : Policy) (value : GoldWord) :
    goldValue (normalizeWord policy value) = goldValue value := by
  cases policy with
  | retain => rfl
  | canonical => exact NativeGoldInverse.canonical_value value

theorem normalizeRow_value (policy : Policy) (row : List GoldWord) :
    (normalizeRow policy row).map goldValue = row.map goldValue := by
  simp only [normalizeRow,List.map_map,Function.comp_def,normalizeWord_value]

theorem normalizeRow_length (policy : Policy) (row : List GoldWord) : (normalizeRow policy row).length = row.length := by
  rw [normalizeRow,List.length_map]

theorem normalizeTable_value (policy : Policy) (table : List (List GoldWord)) :
    (normalizeTable policy table).map (List.map goldValue) = table.map (List.map goldValue) := by
  simp only [normalizeTable,List.map_map,Function.comp_def,normalizeRow_value]

theorem rowKey_eq_iff (left right : List GoldWord) : rowKey left = rowKey right ↔ left.map goldValue = right.map goldValue := by
  have reconstruct (row : List GoldWord) : (rowKey row).map (fun value : ℕ => (value : Goldilocks)) = row.map goldValue := by
    simp only [rowKey,List.map_map,Function.comp_def,goldCanonical_cast]
  have observe (row : List GoldWord) : (row.map goldValue).map (fun value => value.val) = rowKey row := by
    simp only [List.map_map,Function.comp_def,goldValue_val,rowKey]
  constructor
  · intro same
    rw [← reconstruct left,← reconstruct right,same]
  · intro same
    rw [← observe left,← observe right,same]

theorem rowKey_normalize (policy : Policy) (row : List GoldWord) : rowKey (normalizeRow policy row) = rowKey row :=
  (rowKey_eq_iff _ _).mpr (normalizeRow_value policy row)

theorem columns_normalize (policy : Policy) (table : List (List GoldWord)) : columns (normalizeTable policy table) = columns table := by
  cases table with
  | nil => rfl
  | cons row tail => exact normalizeRow_length policy row

theorem nodup_values (table : List (List GoldWord)) :
    (table.map rowKey).Nodup ↔ (table.map (List.map goldValue)).Nodup := by
  induction table with
  | nil => simp
  | cons row tail ih =>
    have member : rowKey row ∈ tail.map rowKey ↔ row.map goldValue ∈ tail.map (List.map goldValue) := by
      simp only [List.mem_map,rowKey_eq_iff]
    simp only [List.map_cons,List.nodup_cons,member,ih]

theorem valid_normalize (policy : Policy) (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord)) :
    valid logicalLength repetitions (normalizeTable policy table) = valid logicalLength repetitions table := by
  unfold valid
  simp only [columns_normalize]
  simp only [normalizeTable,List.length_map,List.all_map,Function.comp_def,
    normalizeRow_length,List.map_map,rowKey_normalize]

structure Spec (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord)) : Prop where
  positiveLength : logicalLength.val ≠ 0
  positiveWidth : columns table ≠ 0
  positiveRepetitions : repetitions ≠ 0
  rectangular : ∀ row ∈ table, row.length = columns table
  distinct : (table.map (List.map goldValue)).Nodup
  rational : logicalLength.val + table.length - 1 < goldilocksModulus
  reciprocal : table.length + 1 < goldilocksModulus

theorem valid_iff (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord)) :
    valid logicalLength repetitions table = true ↔ Spec logicalLength repetitions table := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,nodup_values,and_assoc]
  constructor
  · rintro ⟨length,width,repetitions,rectangular,distinct,rational,reciprocal⟩
    exact ⟨length,width,repetitions,rectangular,distinct,rational,reciprocal⟩
  · intro spec
    exact ⟨spec.positiveLength,spec.positiveWidth,spec.positiveRepetitions,spec.rectangular,spec.distinct,spec.rational,spec.reciprocal⟩

/-- Successful rebuilding preserves original slots, logical length and
repetitions, while deriving width from the normalized first row. -/
theorem rebuild_spec (policy : Policy) (request output : Request) (success : rebuild policy request = some output) :
    output.table = normalizeTable policy request.table ∧ output.columns = columns request.table ∧
      output.repetitions = request.repetitions ∧ output.terminal = request.terminal ∧
      Spec output.terminal.logicalLength output.repetitions output.table := by
  unfold rebuild at success
  dsimp only at success
  split at success
  next accepted =>
    have same := Option.some.inj success
    subst output
    exact ⟨rfl,columns_normalize policy request.table,rfl,rfl,(valid_iff _ _ _).mp accepted⟩
  next rejected => contradiction

theorem rebuild_domain (policy : Policy) (request : Request) :
    (rebuild policy request).isSome = true ↔ valid request.terminal.logicalLength request.repetitions request.table = true := by
  unfold rebuild
  dsimp only
  rw [valid_normalize]
  cases valid request.terminal.logicalLength request.repetitions request.table <;> rfl

/-- Constructor positivity supplies an actual first row and safe num_columns. -/
theorem first_row (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord))
    (spec : Spec logicalLength repetitions table) :
    ∃ first, table.head? = some first ∧ first.length = columns table ∧ first ≠ [] := by
  cases table with
  | nil => exact (spec.positiveWidth rfl).elim
  | cons row tail =>
    refine ⟨row,rfl,rfl,?_⟩
    intro empty
    subst row
    exact spec.positiveWidth rfl

/-- The native rational-domain guard also prevents a positive witness count
from vanishing modulo the base-field characteristic. -/
theorem logical_lt_characteristic (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord))
    (spec : Spec logicalLength repetitions table) : logicalLength.val < goldilocksModulus := by
  cases table with
  | nil => exact (spec.positiveWidth rfl).elim
  | cons row tail =>
    have bound := spec.rational
    simp only [List.length_cons] at bound
    omega

theorem reciprocal_domain_positive (logicalLength : Usize) (repetitions : ℕ) (table : List (List GoldWord))
    (spec : Spec logicalLength repetitions table) : 0 < goldilocksModulus - table.length - 1 := by
  have bound := spec.reciprocal
  omega

end FormalProof4FHE.HasteBoots.NativeTupleLookupConfig
