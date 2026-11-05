module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate
public import FormalProof4FHE.HasteBoots.NativeGoldMatrixWeights

@[expose] public section

/-! Checked packed-table folding with the native constant-lane shortcut.
Equality for that shortcut is field equality, while the first cell's raw words
are retained. Functional output construction describes the final payload;
Rust's in-place writes and memory safety remain a separate refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPackedFold

open NativeFieldRepresentation NativeFields
open NativeGoldCoefficientsQuery (Pair)
open scoped Matrix

structure Table where
  numVars : ℕ
  width : ℕ
  values : List GoldWord
  deriving DecidableEq, Repr

def validate (table : Table) : Bool :=
  if table.numVars < 64 then decide (table.width ≠ 0 ∧
    2^table.numVars*table.width < 2^64 ∧ table.values.length = 2^table.numVars*table.width)
  else false

/-- Getters are bounded on validated tables; no field normalization occurs. -/
def cell (table : Table) (index : ℕ) : List GoldWord :=
  List.ofFn (fun lane : Fin table.width => table.values[index*table.width+lane.val]?.getD 0)

def constant (table : Table) : Bool :=
  (List.range (2^table.numVars)).all (fun index => decide
    ((cell table index).map goldCanonical = (cell table 0).map goldCanonical))

/-- Both matrix products share the same ascending-column accumulator. -/
def combine (width : ℕ) (pair : Pair) (left right : List GoldWord) : List GoldWord :=
  NativeGoldMatrixAccumulate.payload width pair.one right
    (NativeGoldMatrixAccumulate.payload width pair.zero left (List.replicate width 0))

def foldedValues (table : Table) (pair : Pair) : List GoldWord :=
  let isConstant := constant table
  (List.ofFn (fun index : Fin (2^(table.numVars-1)) =>
    if isConstant then combine table.width pair (cell table 0) (cell table 0)
    else combine table.width pair (cell table (2*index.val)) (cell table (2*index.val+1)))).flatten

def fold (table : Table) (pair : Pair) : Option Table :=
  if validate table && NativeGoldMatrix.validate pair.zero table.width &&
      NativeGoldMatrix.validate pair.one table.width && decide (table.numVars ≠ 0) then
    some ⟨table.numVars-1,table.width,foldedValues table pair⟩
  else none

def loop : Table → List Pair → Option Table
  | table,[] => some table
  | table,pair :: tail => (fold table pair).bind (fun next => loop next tail)

def evaluate (table : Table) (query : List Pair) : Option (List GoldWord) :=
  if validate table && decide (query.length = table.numVars) then
    (loop table query).map Table.values
  else none

theorem validate_iff (table : Table) : validate table = true ↔
    table.numVars < 64 ∧ table.width ≠ 0 ∧ 2^table.numVars*table.width < 2^64 ∧
      table.values.length = 2^table.numVars*table.width := by
  simp only [validate]
  split <;> simp_all

theorem at_length (table : Table) (index : ℕ) : (cell table index).length = table.width := List.length_ofFn

theorem address_bound (table : Table) (valid : validate table = true)
    (index : Fin (2^table.numVars)) (lane : Fin table.width) :
    index.val*table.width+lane.val < table.values.length := by
  rw [(validate_iff table).mp valid |>.2.2.2]
  have := index.isLt
  have := lane.isLt
  nlinarith

theorem constant_iff (table : Table) : constant table = true ↔
    ∀ index < 2^table.numVars, (cell table index).map goldCanonical = (cell table 0).map goldCanonical := by
  simp only [constant,List.all_eq_true,List.mem_range,decide_eq_true_eq]

theorem combine_length (width : ℕ) (pair : Pair) (left right : List GoldWord) :
    (combine width pair left right).length = width := NativeGoldMatrixAccumulate.payload_length _ _ _ _

theorem foldedValues_length (table : Table) (pair : Pair) :
    (foldedValues table pair).length = 2^(table.numVars-1)*table.width := by
  simp [foldedValues,List.length_flatten,List.map_ofFn,Function.comp_def,
    apply_ite List.length,combine_length]

theorem fold_success (table : Table) (pair : Pair) (valid : validate table = true)
    (zero : NativeGoldMatrix.validate pair.zero table.width = true)
    (one : NativeGoldMatrix.validate pair.one table.width = true) (positive : table.numVars ≠ 0) :
    fold table pair = some ⟨table.numVars-1,table.width,foldedValues table pair⟩ := by
  simp only [fold,valid,zero,one,positive,ne_eq,not_false_eq_true,decide_true,Bool.true_and,ite_true]

/-- Every successful fold preserves a valid table and removes exactly one variable. -/
theorem fold_spec (table next : Table) (pair : Pair) (success : fold table pair = some next) :
    validate next = true ∧ next.numVars+1 = table.numVars ∧ next.width = table.width := by
  unfold fold at success
  split at success
  · rename_i guards
    have facts := Bool.and_eq_true_iff.mp guards
    have positive : table.numVars ≠ 0 := of_decide_eq_true facts.2
    have valid := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp facts.1).1).1
    have shape := (validate_iff table).mp valid
    have same := Option.some.inj success
    subst next
    refine ⟨(validate_iff _).mpr ⟨by dsimp; omega,shape.2.1,?_,foldedValues_length _ _⟩,by dsimp; omega,rfl⟩
    have power : 2^(table.numVars-1) ≤ 2^table.numVars := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    exact lt_of_le_of_lt (Nat.mul_le_mul_right table.width power) shape.2.2.1
  · contradiction

/-- The completed loop retains validity and its exact remaining variable count. -/
theorem loop_spec (table next : Table) (query : List Pair) (valid : validate table = true)
    (success : loop table query = some next) :
    validate next = true ∧ next.numVars+query.length = table.numVars ∧ next.width = table.width := by
  induction query generalizing table with
  | nil => have same := Option.some.inj success; subst next; exact ⟨valid,by simp,rfl⟩
  | cons pair tail ih =>
    obtain ⟨middle,advanced,rest⟩ := Option.bind_eq_some_iff.mp success
    have first := fold_spec table middle pair advanced
    have last := ih middle first.1 rest
    refine ⟨last.1,?_,last.2.2.trans first.2.2⟩
    simp only [List.length_cons]
    omega

theorem evaluate_length (table : Table) (query : List Pair) (result : List GoldWord)
    (success : evaluate table query = some result) : result.length = table.width := by
  unfold evaluate at success
  split at success
  · rename_i guards
    have facts := Bool.and_eq_true_iff.mp guards
    have querySize : query.length = table.numVars := of_decide_eq_true facts.2
    obtain ⟨next,read,same⟩ := Option.map_eq_some_iff.mp success
    subst result
    have spec := loop_spec table next query facts.1 read
    have last : next.numVars = 0 := by omega
    rw [(validate_iff next).mp spec.1 |>.2.2.2,last,pow_zero,one_mul,spec.2.2]
  · contradiction

noncomputable section

theorem canonical_map_eq_iff (left right : List GoldWord) :
    left.map goldCanonical = right.map goldCanonical ↔ left.map goldValue = right.map goldValue := by
  induction left generalizing right with
  | nil => cases right <;> simp
  | cons head tail ih =>
    cases right with
    | nil => simp
    | cons other rest => simp only [List.map_cons,List.cons.injEq,← goldValue_eq_iff,ih]

/-- A width-sized raw list is recovered without canonicalizing its entries. -/
theorem ofFn_words (width : ℕ) (values : List GoldWord) (size : values.length = width) :
    List.ofFn (fun lane : Fin width => values[lane.val]?.getD 0) = values := by
  apply List.ext_getElem (by simp only [List.length_ofFn,size])
  intro index inside other
  simp only [List.getElem_ofFn,List.getElem?_eq_getElem other,Option.getD_some]

/-- Field semantics of the shared accumulator in a native zero/one fold. -/
theorem combine_value (width : ℕ) (pair : Pair)
    (zero : NativeGoldMatrix.validate pair.zero width = true)
    (one : NativeGoldMatrix.validate pair.one width = true)
    (left right : Fin width → GoldWord) :
    (combine width pair (List.ofFn left) (List.ofFn right)).map goldValue =
      List.ofFn (NativeGoldMatrixMeaning.semantic width pair.zero zero *ᵥ (fun lane => goldValue (left lane)) +
        NativeGoldMatrixMeaning.semantic width pair.one one *ᵥ (fun lane => goldValue (right lane))) := by
  let middle := NativeGoldMatrixAccumulate.payload width pair.zero (List.ofFn left) (List.replicate width 0)
  have size : middle.length = width := NativeGoldMatrixAccumulate.payload_length _ _ _ _
  have zeros : List.replicate width (0 : GoldWord) = List.ofFn (fun _ : Fin width => 0) := by simp
  have first := NativeGoldMatrixAccumulate.payload_value width pair.zero zero left (fun _ => 0)
  rw [← zeros] at first
  have projected (lane : Fin width) : goldValue (middle[lane.val]?.getD 0) =
      (NativeGoldMatrixMeaning.semantic width pair.zero zero *ᵥ (fun i => goldValue (left i))) lane := by
    have bound : lane.val < middle.length := by rw [size]; exact lane.isLt
    have same := congrArg (fun values => values[lane.val]?.getD 0) first
    simpa only [List.getElem?_map,List.getElem?_ofFn,dite_eq_left lane.isLt,Option.map_some,
      Option.getD_some,List.getElem?_eq_getElem bound,middle,goldValue,Fin.val_zero,Nat.cast_zero,zero_add] using same
  change (NativeGoldMatrixAccumulate.payload width pair.one (List.ofFn right) middle).map goldValue = _
  rw [← ofFn_words width middle size,NativeGoldMatrixAccumulate.payload_value width pair.one one]
  simp only [projected]
  rfl

/-- Equal field cells may have different raw bytes. The shortcut retains cell zero. -/
theorem constant_value (table : Table) (constantCells : constant table = true)
    (index : Fin (2^table.numVars)) :
    (cell table index.val).map goldValue = (cell table 0).map goldValue :=
  (canonical_map_eq_iff _ _).mp ((constant_iff table).mp constantCells index.val index.isLt)

end
end FormalProof4FHE.HasteBoots.NativeGoldPackedFold
