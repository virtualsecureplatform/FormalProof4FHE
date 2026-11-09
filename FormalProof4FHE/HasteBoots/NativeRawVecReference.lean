module
public import FormalProof4FHE.HasteBoots.NativeRawVecFields
@[expose] public section

/-! Stable reference operands for checked RawVec field reads. The logical
extents are two or three aligned words; it is not a native slice/fat-pointer ABI claim. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecReference
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)
open NativeRawVecFields (Result)

inductive Object where
  | inner
  | vector
  deriving DecidableEq

def Object.count : Object → NativeWord64Memory.Word
  | .inner => 2
  | .vector => 3

def Object.layout : Object → NativeByteMemory.Layout
  | .inner => ⟨16,8⟩
  | .vector => ⟨24,8⟩

def select (object : Object) (world : State) (index : Nat) : Option Reference := do
  let reference ← world.references[index]?
  let lease ← NativeByteBorrow.lookup world.leases reference.tag
  if lease.mode = .shared ∧ lease.layout = object.layout then some reference else none

/-- The caller selects a resident register, supplying neither tag nor extent. -/
def decode (world : State) (index : Nat) (object : Object := .inner) : Option Value :=
  (select object world index).map (fun reference => .reference false reference object.count)

/-- Register positions may shift after borrows; the value retains a stable tag. -/
def resolve (world : State) (reference : Reference) (object : Object := .inner) : Option Nat :=
  let index := world.references.idxOf reference
  if world.references[index]? = some reference ∧ select object world index = some reference then
    some index
  else none

def objectOfCount (count : NativeWord64Memory.Word) : Option Object :=
  if count = 2 then some .inner else if count = 3 then some .vector else none

inductive Action where
  | capacity
  | pointer
  | marker
  deriving DecidableEq

/-- A complete shared-object operand is checked again against the live ledger. -/
def eval (world : State) (value : Value) (action : Action) : Result Value :=
  match value with
  | .reference false reference count =>
    match objectOfCount count with
    | none => .invalid world
    | some object => match resolve world reference object with
      | none => .invalid world
      | some index => match action with
        | .capacity => match NativeRawVecFields.capacityAccess world index with
          | .invalid next => .invalid next
          | .value value next => .value (.usize value) next
        | .marker => match NativeRawVecFields.markerAccess world index with
          | .invalid next => .invalid next
          | .value _ next => .value .unit next
        | .pointer => match NativeRawVecFields.pointerAccess world index with
          | .invalid next => .invalid next
          | .value value next => .value (.raw ⟨value,none⟩) next
  | _ => .invalid world

theorem select_success (object : Object) (world : State) (index : Nat) (reference : Reference)
    (selected : select object world index = some reference) :
    ∃ lease, world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.mode = .shared ∧ lease.layout = object.layout := by
  simp only [select, Option.bind_eq_bind', Option.bind_eq_some_iff] at selected
  obtain ⟨reference, found, lease, registered, selected⟩ := selected
  split at selected
  next valid => cases selected; exact ⟨lease,found,registered,valid⟩
  next => cases selected

theorem select_complete (object : Object) (world : State) (index : Nat) (reference : Reference) (lease : NativeByteBorrow.Lease)
    (found : world.references[index]? = some reference)
    (registered : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (shared : lease.mode = .shared) (layout : lease.layout = object.layout) :
    select object world index = some reference := by
  simp only [select, found, Option.bind_eq_bind', Option.bind_some, registered, shared, layout, and_self, ite_true]

theorem decode_success (world : State) (index : Nat) (object : Object) (value : Value)
    (decoded : decode world index object = some value) :
    ∃ reference lease, world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.mode = .shared ∧ lease.layout = object.layout ∧ value = .reference false reference object.count := by
  obtain ⟨reference, selected, same⟩ := Option.map_eq_some_iff.mp decoded
  obtain ⟨lease,found,registered,shared,layout⟩ := select_success object world index reference selected
  exact ⟨reference,lease,found,registered,shared,layout,same.symm⟩

theorem resolve_success (world : State) (reference : Reference) (object : Object) (index : Nat)
    (resolved : resolve world reference object = some index) :
    index = world.references.idxOf reference ∧ world.references[index]? = some reference ∧
      select object world index = some reference := by
  simp only [resolve] at resolved
  split at resolved
  next valid => cases resolved; exact ⟨rfl,valid⟩
  next => cases resolved

theorem resolve_complete (world : State) (reference : Reference) (object : Object) (lease : NativeByteBorrow.Lease)
    (member : reference ∈ world.references)
    (registered : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (shared : lease.mode = .shared) (layout : lease.layout = object.layout) :
    resolve world reference object = some (world.references.idxOf reference) := by
  have found := List.getElem?_idxOf member
  have selected := select_complete object world _ reference lease found registered shared layout
  simp only [resolve, found, selected, and_self, ite_true]

theorem decode_resolve (world : State) (index : Nat) (object : Object) (value : Value)
    (decoded : decode world index object = some value) :
    ∃ reference, value = .reference false reference object.count ∧
      resolve world reference object = some (world.references.idxOf reference) := by
  obtain ⟨reference,lease,found,registered,shared,layout,same⟩ := decode_success world index object value decoded
  exact ⟨reference,same,resolve_complete world reference object lease (List.mem_of_getElem? found) registered shared layout⟩

theorem eval_projects (world : State) (value : Value) (action : Action) :
    NativeReferenceMachine.Runs world (eval world value action).world := by
  cases value with
  | unit => exact .refl _
  | usize word => exact .refl _
  | raw pointer => exact .refl _
  | reference mutable reference count =>
    cases mutable with
    | true => exact .refl _
    | false =>
      cases chosen : objectOfCount count with
      | none => simp only [eval, chosen, Result.world]; exact .refl _
      | some object =>
        simp only [eval, chosen]
        cases found : resolve world reference object with
        | none => exact .refl _
        | some index =>
          cases action with
          | capacity =>
            have first := NativeRawVecFields.capacityAccess_projects world index
            cases loaded : NativeRawVecFields.capacityAccess world index <;> simpa only [loaded, Result.world] using first
          | marker =>
            have first := NativeRawVecFields.markerAccess_projects world index
            cases loaded : NativeRawVecFields.markerAccess world index <;> simpa only [loaded, Result.world] using first
          | pointer =>
            have first := NativeRawVecFields.pointerAccess_projects world index
            cases loaded : NativeRawVecFields.pointerAccess world index <;> simpa only [loaded, Result.world] using first

theorem eval_reachable (world : State) (value : Value) (action : Action)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (eval world value action).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (eval_projects world value action)

end FormalProof4FHE.HasteBoots.NativeRawVecReference
