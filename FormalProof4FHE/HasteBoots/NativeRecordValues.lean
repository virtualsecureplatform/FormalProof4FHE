module
public import FormalProof4FHE.HasteBoots.NativeSliceLLBC
@[expose] public section

/-! Nominal aggregate locals with explicit partial moves. These values are
logical locals; their native struct layout/ABI correspondence is unproved. -/
namespace FormalProof4FHE.HasteBoots.NativeRecordValues
open NativeWord64Memory (Word)

inductive Ty where
  | boolean
  | scalar (type : NativeSliceLLBC.Ty)
  | nonnull
  | choice (left right : Ty)
  | pair (left right : Ty)
  | record (tag : Nat) (fields : Ty)
  | enumeration (tag : Nat) (discriminants : List Word)
  deriving DecidableEq

inductive Value where
  | boolean (value : Bool)
  | scalar (value : NativeSliceLLBC.Value)
  | choice (right : Bool) (fields : Value)
  | pair (left right : Value)
  | record (tag : Nat) (fields : Value)
  | enumeration (tag : Nat) (discriminant : Word)
  | uninit
  deriving DecidableEq

def complete : Value → Bool
  | .boolean _ | .scalar _ | .enumeration _ _ => true
  | .pair left right => complete left && complete right
  | .record _ fields | .choice _ fields => complete fields
  | .uninit => false

/-- Compatibility permits holes in storage; reading requires completeness. -/
def compatible : Ty → Value → Bool
  | _, .uninit => true
  | .boolean, .boolean _ => true
  | .scalar type, .scalar value => NativeSliceLLBC.fits type value
  | .nonnull, .scalar (.raw pointer) => pointer.length.isNone && pointer.storage.address.val != 0
  | .choice left right, .choice side fields => compatible (if side then right else left) fields
  | .pair left right, .pair first second => compatible left first && compatible right second
  | .record tag fields, .record actual values => tag == actual && compatible fields values
  | .enumeration tag variants, .enumeration actual value => tag == actual && variants.contains value
  | _, _ => false

def fits (type : Ty) (value : Value) : Bool := complete value && compatible type value

inductive Step where
  | left
  | right
  | active (right : Bool)
  | unwrap (tag : Nat)
  deriving DecidableEq

abbrev Path := List Step

def typeAt (type : Ty) : Path → Option Ty
  | [] => some type
  | .left :: tail => match type with | .pair left _ => typeAt left tail | _ => none
  | .right :: tail => match type with | .pair _ right => typeAt right tail | _ => none
  | .active side :: tail => match type with
    | .choice left right => typeAt (if side then right else left) tail
    | _ => none
  | .unwrap tag :: tail => match type with
    | .record actual fields => if tag = actual then typeAt fields tail else none
    | _ => none

def copyable : Ty → Bool
  | .scalar (.reference true) => false
  | .pair left right | .choice left right => copyable left && copyable right
  | .record _ fields => copyable fields
  | _ => true

def get (value : Value) : Path → Option Value
  | [] => if complete value then some value else none
  | .left :: tail => match value with | .pair left _ => get left tail | _ => none
  | .right :: tail => match value with | .pair _ right => get right tail | _ => none
  | .active side :: tail => match value with
    | .choice actual fields => if side = actual then get fields tail else none
    | _ => none
  | .unwrap tag :: tail => match value with
    | .record actual fields => if tag = actual then get fields tail else none
    | _ => none

def replace (value : Value) : Path → Value → Option Value
  | [], replacement => some replacement
  | .left :: tail, replacement => match value with
    | .pair left right => (replace left tail replacement).map (fun changed => .pair changed right)
    | _ => none
  | .right :: tail, replacement => match value with
    | .pair left right => (replace right tail replacement).map (fun changed => .pair left changed)
    | _ => none
  | .active side :: tail, replacement => match value with
    | .choice actual fields => if side = actual then (replace fields tail replacement).map (.choice actual) else none
    | _ => none
  | .unwrap tag :: tail, replacement => match value with
    | .record actual fields => if tag = actual then (replace fields tail replacement).map (.record actual) else none
    | _ => none

/-- Read an enum's active variant without reading its possibly moved fields. -/
def sideAt (value : Value) (path : Path) (tag : Nat) : Option Bool :=
  match path with
  | [] => match value with
    | .record actual (.choice side _) => if tag = actual then some side else none
    | _ => none
  | .left :: tail => match value with | .pair left _ => sideAt left tail tag | _ => none
  | .right :: tail => match value with | .pair _ right => sideAt right tail tag | _ => none
  | .unwrap wanted :: tail => match value with
    | .record actual fields => if wanted = actual then sideAt fields tail tag else none
    | _ => none
  | .active wanted :: tail => match value with
    | .choice actual fields => if wanted = actual then sideAt fields tail tag else none
    | _ => none

def take (value : Value) (path : Path) : Option (Value × Value) := do
  let selected ← get value path
  let changed ← replace value path .uninit
  pure (selected, changed)

def leaves : Value → List NativeSliceLLBC.Value
  | .scalar value => [value]
  | .pair left right => leaves left ++ leaves right
  | .record _ fields | .choice _ fields => leaves fields
  | .boolean _ | .enumeration _ _ | .uninit => []

theorem get_complete (value selected : Value) (path : Path) (read : get value path = some selected) :
    complete selected = true := by
  induction path generalizing value with
  | nil =>
    simp only [get] at read
    split at read
    next full => cases read; exact full
    next => cases read
  | cons step tail ih =>
    cases step with
    | left =>
      cases value <;> simp only [get] at read <;> first | cases read | exact ih _ read
    | right =>
      cases value <;> simp only [get] at read <;> first | cases read | exact ih _ read
    | active side =>
      cases value <;> simp only [get] at read <;> try cases read
      split at read
      · exact ih _ read
      · cases read
    | unwrap tag =>
      cases value <;> simp only [get] at read <;> try cases read
      split at read
      · exact ih _ read
      · cases read

theorem get_leaves (value selected : Value) (path : Path) (read : get value path = some selected)
    (leaf : NativeSliceLLBC.Value) (member : leaf ∈ leaves selected) : leaf ∈ leaves value := by
  induction path generalizing value with
  | nil =>
    simp only [get] at read
    split at read
    next => cases read; exact member
    next => cases read
  | cons step tail ih =>
    cases step with
    | left =>
      cases value <;> simp only [get] at read <;> first
        | cases read
        | exact List.mem_append_left _ (ih _ read)
    | right =>
      cases value <;> simp only [get] at read <;> first
        | cases read
        | exact List.mem_append_right _ (ih _ read)
    | active side =>
      cases value <;> simp only [get] at read <;> try cases read
      rename_i actual fields
      change leaf ∈ leaves fields
      split at read
      · exact ih fields read
      · cases read
    | unwrap tag =>
      cases value <;> simp only [get] at read <;> try cases read
      rename_i actual fields
      change leaf ∈ leaves fields
      split at read
      · exact ih fields read
      · cases read

theorem get_replace (value replacement changed : Value) (path : Path)
    (written : replace value path replacement = some changed) :
    get changed path = if complete replacement then some replacement else none := by
  induction path generalizing value changed with
  | nil =>
    simp only [replace, Option.some.injEq] at written
    subst changed
    simp only [get]
  | cons step tail ih =>
    cases step with
    | left =>
      cases value <;> simp only [replace] at written <;> try cases written
      obtain ⟨middle, actual, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      exact ih _ _ actual
    | right =>
      cases value <;> simp only [replace] at written <;> try cases written
      obtain ⟨middle, actual, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      exact ih _ _ actual
    | active side =>
      cases value <;> simp only [replace] at written <;> try cases written
      split at written
      · rename_i sameTag
        obtain ⟨middle, actual, same⟩ := Option.map_eq_some_iff.mp written
        cases same
        simpa only [get, sameTag, ite_true] using ih _ _ actual
      · cases written
    | unwrap tag =>
      cases value <;> simp only [replace] at written <;> try cases written
      split at written
      · rename_i sameTag
        obtain ⟨middle, actual, same⟩ := Option.map_eq_some_iff.mp written
        cases same
        simpa only [get, sameTag, ite_true] using ih _ _ actual
      · cases written

theorem take_spec (value selected changed : Value) (path : Path)
    (moved : take value path = some (selected, changed)) :
    get value path = some selected ∧ replace value path .uninit = some changed := by
  simp only [take, Option.bind_eq_bind', Option.bind_eq_some_iff, pure, Option.some.injEq] at moved
  obtain ⟨first, read, next, written, same⟩ := moved
  cases same
  exact ⟨read, written⟩

theorem take_consumes (value selected changed : Value) (path : Path)
    (moved : take value path = some (selected, changed)) : get changed path = none := by
  have written := (take_spec value selected changed path moved).2
  exact get_replace value .uninit changed path written

theorem take_leaves (value selected changed : Value) (path : Path)
    (moved : take value path = some (selected, changed))
    (leaf : NativeSliceLLBC.Value) (member : leaf ∈ leaves selected) : leaf ∈ leaves value :=
  get_leaves value selected path (take_spec value selected changed path moved).1 leaf member

end FormalProof4FHE.HasteBoots.NativeRecordValues
