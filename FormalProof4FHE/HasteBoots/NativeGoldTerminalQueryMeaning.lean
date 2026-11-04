module

public import FormalProof4FHE.HasteBoots.NativeGoldTerminalQuery

@[expose] public section

/-!
# Complete partial field meaning of the terminal source fold

Each field source decoder uses the actual original vector length and bounded
getters, then finishes the interpreted query and checks output padding.
The full partial fold and terminal guard retain all failures and zip tails.
No separately supplied decoded-source list or always-success premise is used.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldTerminalQueryMeaning

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldCoefficientsQuery (Query)
open NativeUsizeMessage (Usize)
open scoped BigOperators

noncomputable section

def source {padding n : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (input : List GoldWord) : Option Goldilocks3 :=
  if length : input.length = 3 + padding then
    PaddedExtension.element goldilocksBasis (query.finish (fun lane => goldValue
      (input[lane.val]'(by rw [length]; exact lane.isLt))))
  else none

def compressFrom {padding n : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n) :
    List (List GoldWord × Word) → Goldilocks3 → Option Goldilocks3
  | [], out => some out
  | (input, weight) :: tail, out => (source query input).bind (fun decoded =>
      compressFrom query tail (out + goldExtensionValue weight * decoded))

def compress {padding n : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (sources : List (List GoldWord)) (powers : List Word) : Option Goldilocks3 :=
  compressFrom query (sources.zip powers) 0

def value {padding queryVars pointVars : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) queryVars)
    (eqPoint point : Fin pointVars → Word) (count : Usize) (enough : count.val ≤ 2 ^ pointVars)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper : Word) : Option Goldilocks3 :=
  (compress query sources powers).map (fun decoded => ExtensionLookupIdentity.terminal
    (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
    (goldExtensionValue r) decoded (goldExtensionValue helper) count.val enough)

theorem project_wrong_length (width : ℕ) (query : Query) (input : List GoldWord) (wrong : input.length ≠ width) :
    NativeGoldPostMap.project width query.post input = none := by
  cases post : query.post with
  | none => rw [NativeGoldPostMap.project, NativeGoldPostMap.apply, ite_eq_left (Or.inr wrong), Option.bind_none]
  | some matrix => rw [NativeGoldPostMap.project, NativeGoldPostMap.apply, NativeGoldMatrix.apply,
      ite_eq_left (Or.inr wrong), Option.bind_none]

/-- Original list length and every stored coordinate are retained, including
failed shape and failed output padding. -/
theorem source_value {padding n : ℕ} (raw : Query)
    (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (interpreted : NativeGoldCoefficientsQuery.interpret (3 + padding) n raw = some query)
    (input : List GoldWord) (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (NativeGoldPostMap.project (3 + padding) raw.post input).map goldExtensionValue = source query input := by
  by_cases length : input.length = 3 + padding
  · let cells : Fin (3 + padding) → GoldWord := fun i => input[i.val]'(by rw [length]; exact i.isLt)
    have rebuilt : List.ofFn cells = input := by
      apply List.ext_getElem (by rw [List.length_ofFn, length])
      intro index leftPresent rightPresent
      simp only [List.getElem_ofFn, cells]
    have related := NativeGoldQueryProjection.query_project_value raw query interpreted cells fits
    rw [rebuilt] at related
    simpa only [source, dite_eq_left length, cells] using related
  · rw [project_wrong_length _ _ _ length, Option.map_none, source, dite_eq_right length]

/-- The entire ordered raw fold has its partial field interpretation. -/
theorem compressFrom_value {padding n : ℕ} (raw : Query)
    (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (interpreted : NativeGoldCoefficientsQuery.interpret (3 + padding) n raw = some query)
    (pairs : List (List GoldWord × Word)) (out : Word) (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (NativeGoldTerminalQuery.compressFrom (3 + padding) raw pairs out).map goldExtensionValue =
      compressFrom query pairs (goldExtensionValue out) := by
  induction pairs generalizing out with
  | nil => rfl
  | cons pair tail ih =>
    have projected := source_value raw query interpreted pair.1 fits
    cases executed : NativeGoldPostMap.project (3 + padding) raw.post pair.1 with
    | none =>
      rw [executed, Option.map_none] at projected
      simp only [NativeGoldTerminalQuery.compressFrom, executed, Option.bind_none, Option.map_none,
        compressFrom, ← projected]
    | some decoded =>
      rw [executed, Option.map_some] at projected
      simp only [NativeGoldTerminalQuery.compressFrom, executed, Option.bind_some]
      rw [ih]
      simp only [compressFrom, ← projected, Option.bind_some,
        NativeGoldExtensionArithmetic.add_value, NativeGoldCubic.mul_value]

theorem compress_value {padding n : ℕ} (raw : Query)
    (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (interpreted : NativeGoldCoefficientsQuery.interpret (3 + padding) n raw = some query)
    (sources : List (List GoldWord)) (powers : List Word) (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (NativeGoldTerminalQuery.compress (3 + padding) raw sources powers).map goldExtensionValue = compress query sources powers := by
  rw [NativeGoldTerminalQuery.compress, compressFrom_value raw query interpreted _ _ fits, NativeGoldLookup.zero_value]
  rfl

/-- A typed original vector has exactly the field finish/decode meaning. -/
theorem source_ofFn {padding n : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (input : Fin (3 + padding) → GoldWord) :
    source query (List.ofFn input) = PaddedExtension.element goldilocksBasis (query.finish (fun i => goldValue (input i))) := by
  rw [source, dite_eq_left List.length_ofFn]
  simp only [List.getElem_ofFn]

private theorem zip_ofFn {a b : Type} {count : ℕ} (first : Fin count → a) (second : Fin count → b) :
    (List.ofFn first).zip (List.ofFn second) = List.ofFn (fun i => (first i, second i)) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [List.ofFn_succ, List.zip_cons_cons]; rw [ih]

/-- Complete matched typed inputs yield their ordered weighted decoded sum.
Every decoder premise is about that actual vector and query. -/
theorem compressFrom_ofFn {padding n count : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (inputs : Fin count → Fin (3 + padding) → GoldWord) (powers : Fin count → Word)
    (decoded : Fin count → Goldilocks3) (projected : ∀ i, source query (List.ofFn (inputs i)) = some (decoded i)) (out : Goldilocks3) :
    compressFrom query (List.ofFn (fun i => (List.ofFn (inputs i), powers i))) out =
      some (out + ∑ i : Fin count, goldExtensionValue (powers i) * decoded i) := by
  induction count generalizing out with
  | zero => simp only [List.ofFn_zero, compressFrom, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ count ih =>
    rw [List.ofFn_succ, compressFrom, projected 0, Option.bind_some,
      ih (fun i => inputs i.succ) (fun i => powers i.succ) (fun i => decoded i.succ) (fun i => projected i.succ)]
    simp only [Fin.sum_univ_succ, add_assoc]

theorem compress_ofFn {padding n count : ℕ} (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) n)
    (inputs : Fin count → Fin (3 + padding) → GoldWord) (powers : Fin count → Word)
    (decoded : Fin count → Goldilocks3) (projected : ∀ i, source query (List.ofFn (inputs i)) = some (decoded i)) :
    compress query (List.ofFn (fun i => List.ofFn (inputs i))) (List.ofFn powers) =
      some (∑ i : Fin count, goldExtensionValue (powers i) * decoded i) := by
  rw [compress, zip_ofFn, compressFrom_ofFn query inputs powers decoded projected, zero_add]

/-- The actual source-vector decoder/fold is used before the literal raw
prefix and residual; all projection failures remain present in the field model. -/
theorem value_value {padding queryVars pointVars : ℕ} (raw : Query)
    (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) queryVars)
    (interpreted : NativeGoldCoefficientsQuery.interpret (3 + padding) queryVars raw = some query)
    (eqPoint point : Fin pointVars → Word) (count : Usize) (shift : pointVars < 64) (enough : count.val ≤ 2 ^ pointVars)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper : Word)
    (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (NativeGoldTerminalQuery.value (3 + padding) raw (List.ofFn eqPoint) (List.ofFn point) count r sources powers helper).map
      goldExtensionValue = value query eqPoint point count enough r sources powers helper := by
  have folded := compress_value raw query interpreted sources powers fits
  cases executed : NativeGoldTerminalQuery.compress (3 + padding) raw sources powers with
  | none =>
    rw [executed, Option.map_none] at folded
    simp only [NativeGoldTerminalQuery.value, executed, Option.bind_none, Option.map_none, value, ← folded]
  | some decoded =>
    rw [executed, Option.map_some] at folded
    have mask := NativeGoldTerminalArithmetic.prefixValue_value point count shift enough
    cases masked : NativeGoldTerminalArithmetic.prefixValue (List.ofFn point) count with
    | none => rw [masked, Option.map_none] at mask; contradiction
    | some rawMask =>
      rw [masked, Option.map_some] at mask
      have sameMask := Option.some.inj mask
      simp only [NativeGoldTerminalQuery.value, executed, Option.bind_some, masked, Option.map_some,
        value, ← folded]
      rw [NativeGoldCubic.mul_value, NativeGoldTerminalArithmetic.equality_value,
        NativeGoldTerminalArithmetic.residual_value, sameMask]
      rfl

/-- Canonical raw equality accepts exactly the same partial field terminal
value. A failed used-vector decoder cannot be hidden by a zero coefficient. -/
theorem check_iff {padding queryVars pointVars : ℕ} (raw : Query)
    (query : ExtensionQuery.Broadcast Goldilocks (3 + padding) queryVars)
    (interpreted : NativeGoldCoefficientsQuery.interpret (3 + padding) queryVars raw = some query)
    (eqPoint point : Fin pointVars → Word) (count : Usize) (shift : pointVars < 64) (enough : count.val ≤ 2 ^ pointVars)
    (r : Word) (sources : List (List GoldWord)) (powers : List Word) (helper expected : Word)
    (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    NativeGoldTerminalQuery.check (3 + padding) raw (List.ofFn eqPoint) (List.ofFn point) count r sources powers helper expected = some true ↔
      value query eqPoint point count enough r sources powers helper = some (goldExtensionValue expected) := by
  have related := value_value raw query interpreted eqPoint point count shift enough r sources powers helper fits
  cases executed : NativeGoldTerminalQuery.value (3 + padding) raw (List.ofFn eqPoint) (List.ofFn point) count r sources powers helper with
  | none =>
    rw [executed, Option.map_none] at related
    simp [NativeGoldTerminalQuery.check, executed, ← related]
  | some out =>
    rw [executed, Option.map_some] at related
    rw [NativeGoldTerminalQuery.check, executed, Option.map_some, Option.some.injEq, NativeGoldInterpolation.equal_value,
      ← related, Option.some.injEq]
    simp only [NativeInterpolationField.arithmetic, decide_eq_true_eq]

end

end FormalProof4FHE.HasteBoots.NativeGoldTerminalQueryMeaning
