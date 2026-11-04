module

public import FormalProof4FHE.HasteBoots.NativeGoldCubicInverse
public import FormalProof4FHE.HasteBoots.NativeLookupArithmetic

@[expose] public section

/-!
# Raw Goldilocks lookup challenge arithmetic

The producer retains the native ordered powers, tuple zip/fold, additive
denominators, and individual `one / denominator` policy. The final power
update is retained even when no later table column uses it. This is word
arithmetic; transcript chronology and Rust/work refinement are separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldLookup

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

def zero : Word := fun _ => 0
def one : Word := ![1, 0, 0]

def powerStep (y : Word) (state : List Word × Word) : List Word × Word :=
  (state.1 ++ [state.2], NativeGoldCubic.mul state.2 y)

def powerRun (y : Word) (count : ℕ) : List Word × Word := (powerStep y)^[count] ([], one)
def powers (y : Word) (count : ℕ) : List Word := (powerRun y count).1

def compress (weights : List Word) (row : List GoldWord) : Word :=
  (row.zip weights).foldl (fun out pair =>
    NativeGoldExtensionArithmetic.add out (NativeGoldExtensionArithmetic.scale pair.2 pair.1)) zero

def tableAt (rows : List (List GoldWord)) (width : ℕ) (y : Word) : List Word :=
  rows.map (compress (powers y width))

def isZero (value : Word) : Bool := decide (∀ i, goldCanonical (value i) = 0)

def allowed (table : List Word) (r : Word) : Bool :=
  !isZero r && !(table.any (fun value => isZero (NativeGoldExtensionArithmetic.add r value)))

def denominators (r : Word) (table : List Word) : List Word :=
  table.map (NativeGoldExtensionArithmetic.add r)

/-- Failed inversion is an explicit arithmetic-domain failure in this model;
native unchecked inversion panics there. Accepted sampler draws avoid it. -/
def reciprocals : List Word → Option (List Word)
  | [] => some []
  | value :: tail => (NativeGoldCubicInverse.divResult one value).bind (fun inverse =>
      (reciprocals tail).map (fun rest => inverse :: rest))

noncomputable section

theorem zero_value : goldExtensionValue zero = 0 := NativeGoldExtensionArithmetic.zero_value

theorem one_value : goldExtensionValue one = 1 := by
  rw [NativeGoldCubic.value_expansion]
  simp [one, goldValue]

private theorem powersFrom_snoc (y start : Goldilocks3) (n : ℕ) :
    NativeLookupChallenge.powersFrom y (n + 1) start =
      NativeLookupChallenge.powersFrom y n start ++ [start * y ^ n] := by
  induction n generalizing start with
  | zero => simp [NativeLookupChallenge.powersFrom]
  | succ n ih =>
    change start :: NativeLookupChallenge.powersFrom y (n + 1) (start * y) =
      (start :: NativeLookupChallenge.powersFrom y n (start * y)) ++ [start * y ^ (n + 1)]
    have term : (start * y) * y ^ n = start * y ^ (n + 1) := by rw [pow_succ]; ring
    rw [ih, List.cons_append, term]

/-- Both the emitted powers and the otherwise unused last update are retained. -/
theorem powerRun_value (y : Word) (n : ℕ) :
    ((powerRun y n).1.map goldExtensionValue, goldExtensionValue (powerRun y n).2) =
      (NativeLookupChallenge.powers (goldExtensionValue y) n, goldExtensionValue y ^ n) := by
  induction n with
  | zero => simp [powerRun, one_value, NativeLookupChallenge.powers, NativeLookupChallenge.powersFrom]
  | succ n ih =>
    have first := congrArg Prod.fst ih
    have last := congrArg Prod.snd ih
    change (powerRun y n).1.map goldExtensionValue = NativeLookupChallenge.powers (goldExtensionValue y) n at first
    change goldExtensionValue (powerRun y n).2 = goldExtensionValue y ^ n at last
    change (((powerStep y)^[n + 1] ([], one)).1.map goldExtensionValue,
      goldExtensionValue ((powerStep y)^[n + 1] ([], one)).2) = _
    rw [Function.iterate_succ_apply']
    simp only [powerStep, List.map_append, List.map_cons, List.map_nil]
    change ((powerRun y n).1.map goldExtensionValue ++ [goldExtensionValue (powerRun y n).2],
      goldExtensionValue (NativeGoldCubic.mul (powerRun y n).2 y)) = _
    rw [first, NativeGoldCubic.mul_value, last]
    simp only [NativeLookupChallenge.powers, powersFrom_snoc, one_mul, pow_succ]

theorem powers_value (y : Word) (n : ℕ) :
    (powers y n).map goldExtensionValue = NativeLookupChallenge.powers (goldExtensionValue y) n :=
  congrArg Prod.fst (powerRun_value y n)

private theorem compressFold_value (pairs : List (GoldWord × Word)) (initial : Word) :
    goldExtensionValue (pairs.foldl (fun out pair => NativeGoldExtensionArithmetic.add out
      (NativeGoldExtensionArithmetic.scale pair.2 pair.1)) initial) =
    (pairs.map (fun pair => (goldValue pair.1, goldExtensionValue pair.2))).foldl
      (fun out pair => out + pair.2 * algebraMap Goldilocks Goldilocks3 pair.1)
      (goldExtensionValue initial) := by
  induction pairs generalizing initial with
  | nil => rfl
  | cons pair tail ih =>
    simp only [List.foldl_cons, List.map_cons, ih, NativeGoldExtensionArithmetic.add_value,
      NativeGoldExtensionArithmetic.scale_value, Algebra.smul_def]
    rw [mul_comm (algebraMap Goldilocks Goldilocks3 (goldValue pair.1))]

private theorem zipFold_swap (row : List GoldWord) (weights : List Word) (initial : Word) :
    (row.zip weights).foldl (fun out pair => NativeGoldExtensionArithmetic.add out
      (NativeGoldExtensionArithmetic.scale pair.2 pair.1)) initial =
    (weights.zip row).foldl (fun out pair => NativeGoldExtensionArithmetic.add out
      (NativeGoldExtensionArithmetic.scale pair.1 pair.2)) initial := by
  induction row generalizing weights initial with
  | nil => cases weights <;> rfl
  | cons value tail ih =>
    cases weights with
    | nil => rfl
    | cons weight rest =>
      exact ih rest (NativeGoldExtensionArithmetic.add initial (NativeGoldExtensionArithmetic.scale weight value))

/-- Swapping the pair orientation changes neither the sequence of raw
arithmetic operations nor the zip truncation. -/
theorem compress_tableSum (weights : List Word) (row : List GoldWord) :
    compress weights row = NativeGoldExtensionArithmetic.tableSum weights row :=
  zipFold_swap row weights zero

theorem compress_value (weights : List Word) (row : List GoldWord) :
    goldExtensionValue (compress weights row) =
      NativeLookupChallenge.compress (weights.map goldExtensionValue) (row.map goldValue) := by
  rw [compress, compressFold_value, zero_value, NativeLookupChallenge.compress]
  rw [List.zip_map]
  rfl

theorem tableAt_value (rows : List (List GoldWord)) (width : ℕ) (y : Word) :
    (tableAt rows width y).map goldExtensionValue =
      NativeLookupChallenge.tableAt (rows.map (List.map goldValue)) width (goldExtensionValue y) := by
  simp only [tableAt, NativeLookupChallenge.tableAt, List.map_map, Function.comp_def,
    compress_value, powers_value]

theorem isZero_iff (value : Word) : isZero value = true ↔ goldExtensionValue value = 0 := by
  rw [isZero, decide_eq_true_eq]
  change NativeGoldExtensionArithmetic.Equal value zero ↔ goldExtensionValue value = 0
  rw [NativeGoldExtensionArithmetic.equal_iff, zero_value]

theorem allowed_value (table : List Word) (r : Word) :
    allowed table r = NativeLookupChallenge.allowed (table.map goldExtensionValue) (goldExtensionValue r) := by
  have false_iff (value : Word) : isZero value = false ↔ goldExtensionValue value ≠ 0 := by
    change isZero value = false ↔ ¬(goldExtensionValue value = 0)
    rw [← isZero_iff]
    cases isZero value <;> decide
  apply Bool.eq_iff_iff.mpr
  simp [allowed, NativeLookupChallenge.allowed_iff, isZero_iff, false_iff,
    NativeGoldExtensionArithmetic.add_value]

theorem denominators_value (r : Word) (table : List Word) :
    (denominators r table).map goldExtensionValue =
      NativeLookupReciprocals.denominators (goldExtensionValue r) (table.map goldExtensionValue) := by
  simp only [denominators, NativeLookupReciprocals.denominators, List.map_map,
    Function.comp_def, NativeGoldExtensionArithmetic.add_value]

/-- Every accepted denominator is inverted by the literal raw division
policy. The output vector remains ordered and retains its native words. -/
theorem reciprocals_success (values : List Word)
    (nonzero : ∀ value ∈ values, goldExtensionValue value ≠ 0) :
    ∃ output, reciprocals values = some output ∧
      output.map goldExtensionValue = values.map (fun value => (goldExtensionValue value)⁻¹) := by
  induction values with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons value tail ih =>
    have headValue := NativeGoldCubicInverse.divResult_value one value (nonzero value (by simp))
    rw [one_value, one_div] at headValue
    cases head : NativeGoldCubicInverse.divResult one value with
    | none => simp only [head, Option.map_none, reduceCtorEq] at headValue
    | some inverse =>
      have inverseValue : goldExtensionValue inverse = (goldExtensionValue value)⁻¹ := by
        simpa only [head, Option.map_some, Option.some.injEq] using headValue
      obtain ⟨rest, found, related⟩ := ih (fun other member => nonzero other (by simp [member]))
      refine ⟨inverse :: rest, ?_, ?_⟩
      · simp only [reciprocals, head, Option.bind_some, found, Option.map_some]
      · simp only [List.map_cons, inverseValue, related]

theorem reciprocals_length (values output : List Word)
    (finished : reciprocals values = some output) : output.length = values.length := by
  induction values generalizing output with
  | nil =>
    have equal := Option.some.inj finished
    subst output
    rfl
  | cons value tail ih =>
    cases head : NativeGoldCubicInverse.divResult one value with
    | none => simp only [reciprocals, head, Option.bind_none] at finished; cases finished
    | some inverse =>
      cases rest : reciprocals tail with
      | none => simp only [reciprocals, head, Option.bind_some, rest, Option.map_none] at finished; cases finished
      | some values =>
        simp only [reciprocals, head, Option.bind_some, rest, Option.map_some, Option.some.injEq] at finished
        subst output
        simp only [List.length_cons, ih values rest]

theorem accepted_reciprocals (table : List Word) (r : Word) (accepted : allowed table r = true) :
    ∃ output, reciprocals (denominators r table) = some output ∧
      output.map goldExtensionValue = NativeLookupReciprocals.inverses .individual
        (goldExtensionValue r) (table.map goldExtensionValue) := by
  have semanticAccepted : NativeLookupChallenge.allowed (table.map goldExtensionValue)
      (goldExtensionValue r) = true := by rw [← allowed_value]; exact accepted
  have nonzero : ∀ value ∈ denominators r table, goldExtensionValue value ≠ 0 := by
    intro value member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    rw [NativeGoldExtensionArithmetic.add_value]
    exact ((NativeLookupChallenge.allowed_iff _ _).mp semanticAccepted).2
      (goldExtensionValue entry) (List.mem_map.mpr ⟨entry, present, rfl⟩)
  obtain ⟨output, finished, related⟩ := reciprocals_success _ nonzero
  refine ⟨output, finished, ?_⟩
  rw [NativeLookupReciprocals.inverses_correct .individual _ _ semanticAccepted]
  simpa only [denominators, List.map_map, Function.comp_def,
    NativeGoldExtensionArithmetic.add_value] using related

/-- Raw reciprocal words feed exactly the existing mathematical public sum,
without canonicalizing either their coordinates or the accumulated result. -/
theorem tableSum_value (r : Goldilocks3) (table : List Goldilocks3)
    (inverses : List Word) (multiplicities : List GoldWord)
    (related : inverses.map goldExtensionValue = NativeLookupReciprocals.inverses .individual r table) :
    goldExtensionValue (NativeGoldExtensionArithmetic.tableSum inverses multiplicities) =
      NativeLookupArithmetic.tableSum .individual r table (multiplicities.map goldValue) := by
  rw [← compress_tableSum, compress_value, related]
  rfl

end

end FormalProof4FHE.HasteBoots.NativeGoldLookup
