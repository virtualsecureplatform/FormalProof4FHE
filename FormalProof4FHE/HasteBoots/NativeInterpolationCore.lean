module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.SplitIfs
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Literal operation-order interpolation core

This is the scan, factorial and reverse accumulator of native
`interpolate_uni_poly`. Raw and mathematical arithmetic instantiate the
same control. Failed array/division preconditions are explicit `none`;
native unchecked accesses/inversion panic there. There are no defaults or
runtime iteration caps in this model.
-/

namespace FormalProof4FHE.HasteBoots.NativeInterpolationCore

structure Arithmetic (A : Type) where
  zero : A
  one : A
  add : A → A → A
  sub : A → A → A
  mul : A → A → A
  neg : A → A
  equal : A → A → Bool
  divide : A → A → Option A

structure ScanState (A : Type) where
  check : A
  product : A
  differences : List A

inductive ScanResult (A : Type) where
  | atNode (index : ℕ)
  | offNodes (state : ScanState A)

structure ReverseState (A : Type) where
  result : A
  up : A
  down : A
  indexField : A
  remainingField : A

def extend {A : Type} (ops : Arithmetic A) (point : A) (state : ScanState A) : ScanState A :=
  let next := ops.add state.check ops.one
  let difference := ops.sub point next
  ⟨next, ops.mul state.product difference, state.differences ++ [difference]⟩

def scan {A : Type} (ops : Arithmetic A) (point : A) : ℕ → ℕ → ScanState A → ScanResult A
  | 0, index, state => if ops.equal point state.check then .atNode index else .offNodes state
  | remaining + 1, index, state =>
      if ops.equal point state.check then .atNode index else scan ops point remaining (index + 1) (extend ops point state)

def factorialStep {A : Type} (ops : Arithmetic A) (state : A × A) : A × A :=
  (ops.mul state.1 state.2, ops.add state.2 ops.one)

def factorial {A : Type} (ops : Arithmetic A) (count : ℕ) : A × A :=
  (factorialStep ops)^[count] (ops.one, ops.one)

def advance {A : Type} (ops : Arithmetic A) (term : A) (state : ReverseState A) : ReverseState A :=
  ⟨ops.add state.result term, ops.mul state.up (ops.neg state.remainingField),
    ops.mul state.down state.indexField, ops.sub state.indexField ops.one, ops.add state.remainingField ops.one⟩

def reverse {A : Type} (ops : Arithmetic A) (values differences : List A) (product : A) :
    ℕ → ReverseState A → Option (ReverseState A)
  | 0, state => some state
  | index + 1, state => (values[index]?).bind (fun value =>
      (differences[index]?).bind (fun difference =>
        (ops.divide (ops.mul (ops.mul value product) state.down) (ops.mul state.up difference)).bind (fun term =>
          if index = 0 then some { state with result := ops.add state.result term }
          else reverse ops values differences product index (advance ops term state))))

def interpolate {A : Type} (ops : Arithmetic A) (values : List A) (point : A) : Option A :=
  match values with
  | [] => none
  | _ :: _ =>
      match scan ops point (values.length - 1) 0 ⟨ops.zero, point, [point]⟩ with
      | .atNode index => values[index]?
      | .offNodes scanned =>
          (reverse ops values scanned.differences scanned.product values.length
            ⟨ops.zero, (factorial ops (values.length - 1)).1, ops.one, scanned.check, ops.one⟩).map ReverseState.result

def mapScan {A B : Type} (f : A → B) (state : ScanState A) : ScanState B :=
  ⟨f state.check, f state.product, state.differences.map f⟩

def mapResult {A B : Type} (f : A → B) : ScanResult A → ScanResult B
  | .atNode index => .atNode index
  | .offNodes state => .offNodes (mapScan f state)

def mapReverse {A B : Type} (f : A → B) (state : ReverseState A) : ReverseState B :=
  ⟨f state.result, f state.up, f state.down, f state.indexField, f state.remainingField⟩

structure Hom {A B : Type} (source : Arithmetic A) (target : Arithmetic B) (f : A → B) : Prop where
  map_zero : f source.zero = target.zero
  map_one : f source.one = target.one
  map_add : ∀ a b, f (source.add a b) = target.add (f a) (f b)
  map_sub : ∀ a b, f (source.sub a b) = target.sub (f a) (f b)
  map_mul : ∀ a b, f (source.mul a b) = target.mul (f a) (f b)
  map_neg : ∀ a, f (source.neg a) = target.neg (f a)
  map_equal : ∀ a b, source.equal a b = target.equal (f a) (f b)
  map_divide : ∀ a b, (source.divide a b).map f = target.divide (f a) (f b)

variable {A B : Type} {source : Arithmetic A} {target : Arithmetic B} {f : A → B}

theorem extend_map (hom : Hom source target f) (point : A) (state : ScanState A) :
    mapScan f (extend source point state) = extend target (f point) (mapScan f state) := by
  simp only [extend, mapScan, hom.map_add, hom.map_one, hom.map_sub, hom.map_mul,
    List.map_append, List.map_cons, List.map_nil]

theorem advance_map (hom : Hom source target f) (term : A) (state : ReverseState A) :
    mapReverse f (advance source term state) = advance target (f term) (mapReverse f state) := by
  simp only [advance, mapReverse, hom.map_add, hom.map_mul, hom.map_neg, hom.map_sub, hom.map_one]

theorem factorial_map (hom : Hom source target f) (count : ℕ) :
    (f (factorial source count).1, f (factorial source count).2) = factorial target count := by
  induction count with
  | zero => simp only [factorial, Function.iterate_zero_apply, hom.map_one]
  | succ count ih =>
    change (f ((factorialStep source)^[count + 1] (source.one, source.one)).1,
      f ((factorialStep source)^[count + 1] (source.one, source.one)).2) = _
    rw [Function.iterate_succ_apply', factorial]
    rw [Function.iterate_succ_apply']
    change (f (source.mul (factorial source count).1 (factorial source count).2),
      f (source.add (factorial source count).2 source.one)) = factorialStep target (factorial target count)
    rw [hom.map_mul, hom.map_add, hom.map_one, ← ih]
    rfl

theorem scan_map (hom : Hom source target f) (point : A) (remaining index : ℕ) (state : ScanState A) :
    mapResult f (scan source point remaining index state) =
      scan target (f point) remaining index (mapScan f state) := by
  induction remaining generalizing index state with
  | zero =>
    simp only [scan, mapScan, hom.map_equal]
    by_cases branch : target.equal (f point) (f state.check) = true
    · simp [branch, mapResult]
    · simp [branch, mapResult, mapScan]
  | succ remaining ih =>
    simp only [scan, hom.map_equal]
    change mapResult f (if target.equal (f point) (f state.check) then .atNode index
      else scan source point remaining (index + 1) (extend source point state)) =
      if target.equal (f point) (f state.check) then .atNode index
      else scan target (f point) remaining (index + 1) (extend target (f point) (mapScan f state))
    split_ifs
    · rfl
    · rw [ih, extend_map hom]

theorem reverse_map (hom : Hom source target f) (values differences : List A) (product : A)
    (count : ℕ) (state : ReverseState A) :
    (reverse source values differences product count state).map (mapReverse f) =
      reverse target (values.map f) (differences.map f) (f product) count (mapReverse f state) := by
  induction count generalizing state with
  | zero => rfl
  | succ index ih =>
    simp only [reverse, List.getElem?_map]
    cases valueFound : values[index]? with
    | none => simp only [Option.map_none, Option.bind_none]
    | some value =>
      simp only [Option.map_some, Option.bind_some]
      cases differenceFound : differences[index]? with
      | none => simp only [Option.map_none, Option.bind_none]
      | some difference =>
        simp only [Option.map_some, Option.bind_some]
        change _ = (target.divide (target.mul (target.mul (f value) (f product)) (f state.down))
          (target.mul (f state.up) (f difference))).bind _
        have division := hom.map_divide (source.mul (source.mul value product) state.down)
          (source.mul state.up difference)
        simp only [hom.map_mul] at division
        cases termFound : source.divide (source.mul (source.mul value product) state.down)
            (source.mul state.up difference) with
        | none =>
          rw [termFound, Option.map_none] at division
          rw [← division]
          rfl
        | some term =>
          rw [termFound, Option.map_some] at division
          rw [← division]
          simp only [Option.bind_some]
          by_cases final : index = 0
          · simp only [final, ite_true, Option.map_some, mapReverse, hom.map_add]
          · simp only [final, ite_false]
            rw [ih, advance_map hom]

theorem interpolate_map (hom : Hom source target f) (values : List A) (point : A) :
    (interpolate source values point).map f = interpolate target (values.map f) (f point) := by
  cases values with
  | nil => rfl
  | cons first rest =>
    let initial : ScanState A := ⟨source.zero, point, [point]⟩
    have initialMap : mapScan f initial = ⟨target.zero, f point, [f point]⟩ := by
      simp only [mapScan, initial, hom.map_zero, List.map_cons, List.map_nil]
    have scans := scan_map hom point rest.length 0 initial
    rw [initialMap] at scans
    simp only [interpolate, List.map_cons, List.length_cons, List.length_map, Nat.add_sub_cancel]
    change (match scan source point rest.length 0 initial with
      | .atNode index => (first :: rest)[index]?
      | .offNodes scanned => (reverse source (first :: rest) scanned.differences scanned.product (rest.length + 1)
          ⟨source.zero, (factorial source rest.length).1, source.one, scanned.check, source.one⟩).map ReverseState.result).map f = _
    cases scanned : scan source point rest.length 0 initial with
    | atNode index =>
      rw [scanned, mapResult] at scans
      rw [← scans]
      change ((first :: rest)[index]?).map f = ((first :: rest).map f)[index]?
      rw [List.getElem?_map]
    | offNodes state =>
      rw [scanned, mapResult] at scans
      rw [← scans]
      have fact := congrArg Prod.fst (factorial_map hom rest.length)
      change f (factorial source rest.length).1 = (factorial target rest.length).1 at fact
      let start : ReverseState A :=
        ⟨source.zero, (factorial source rest.length).1, source.one, state.check, source.one⟩
      have startMap : mapReverse f start =
          ⟨target.zero, (factorial target rest.length).1, target.one, f state.check, target.one⟩ := by
        simp only [mapReverse, start, hom.map_zero, hom.map_one, fact]
      have reversed := reverse_map hom (first :: rest) state.differences state.product (rest.length + 1) start
      rw [startMap] at reversed
      have projected := congrArg (Option.map ReverseState.result) reversed
      simpa only [Option.map_map, Function.comp_def, mapReverse, start, mapScan, List.map_cons,
        List.length_map] using projected

theorem scan_equal (ops : Arithmetic A) (point : A) (remaining index : ℕ) (state : ScanState A)
    (matched : ops.equal point state.check = true) : scan ops point remaining index state = .atNode index := by
  cases remaining <;> simp only [scan, matched, ite_true]

/-- The known-zero-node branch returns the original stored message word. -/
theorem interpolate_at_zero (ops : Arithmetic A) (first : A) (rest : List A) (point : A)
    (matched : ops.equal point ops.zero = true) : interpolate ops (first :: rest) point = some first := by
  rw [interpolate, scan_equal ops point _ 0 _ matched]
  rfl

/-- A hit stays inside the tested range; an off-node scan appends exactly
one difference for each loop iteration. -/
theorem scan_bounds (ops : Arithmetic A) (point : A) (remaining index : ℕ) (state : ScanState A) :
    match scan ops point remaining index state with
    | .atNode found => index ≤ found ∧ found ≤ index + remaining
    | .offNodes last => last.differences.length = state.differences.length + remaining := by
  induction remaining generalizing index state with
  | zero =>
    by_cases matched : ops.equal point state.check = true <;> simp [scan, matched]
  | succ remaining ih =>
    by_cases matched : ops.equal point state.check = true
    · simp [scan, matched]
    · rw [scan, ite_eq_right matched]
      have bounds := ih (index + 1) (extend ops point state)
      cases found : scan ops point remaining (index + 1) (extend ops point state) with
      | atNode value =>
        rw [found] at bounds
        exact ⟨by omega, by omega⟩
      | offNodes last =>
        rw [found] at bounds
        simp only [extend, List.length_append, List.length_singleton] at bounds
        simpa only [Nat.add_assoc, Nat.add_comm 1 remaining] using bounds

theorem offNodes_length (ops : Arithmetic A) (values : List A) (point : A) (positive : 0 < values.length)
    (state : ScanState A)
    (finished : scan ops point (values.length - 1) 0 ⟨ops.zero, point, [point]⟩ = .offNodes state) :
    state.differences.length = values.length := by
  have bounds := scan_bounds ops point (values.length - 1) 0 ⟨ops.zero, point, [point]⟩
  rw [finished] at bounds
  simp only [List.length_singleton] at bounds
  omega

end FormalProof4FHE.HasteBoots.NativeInterpolationCore
