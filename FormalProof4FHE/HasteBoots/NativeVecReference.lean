module
public import FormalProof4FHE.HasteBoots.NativeRawVecReference
@[expose] public section

/-! Resident exclusive Vec access and mutable whole/subobject borrows over the
checked heap. Logical word extents do not establish a native reference ABI. -/
namespace FormalProof4FHE.HasteBoots.NativeVecReference
open NativeReferenceMachine (State Reference)
open NativeRawVecFields (Result)
open NativeSliceLLBC (Value)

inductive Target where
  | whole
  | rawVec
  deriving DecidableEq

def Target.offset : Target → Nat
  | .whole => 0
  | .rawVec => 0

def Target.layout : Target → NativeByteMemory.Layout
  | .whole => ⟨24,8⟩
  | .rawVec => ⟨16,8⟩

def Target.count : Target → NativeWord64Memory.Word
  | .whole => 3
  | .rawVec => 2

def decodeExclusive (world : State) (index : Nat) : Option Value := do
  let reference ← world.references[index]?
  let lease ← NativeByteBorrow.lookup world.leases reference.tag
  if lease.mode = .exclusive ∧ lease.layout = ⟨24,8⟩ then some (.reference true reference 3) else none

/-- Resolve both identities before deriving the subobject's address. -/
def parent (world : State) : Value → Option (Nat × Nat × NativeByteBorrow.Lease)
  | .reference true reference count => do
    if count ≠ 3 then none else do
      let lease ← NativeByteBorrow.lookup world.leases reference.tag
      let index := world.references.idxOf reference
      let register := world.pointers.registers.idxOf lease.pointer
      if lease.mode = .exclusive ∧ lease.layout = ⟨24,8⟩ ∧
          world.references[index]? = some reference ∧ world.pointers.registers[register]? = some lease.pointer then
        some (index,register,lease)
      else none
  | _ => none

/-- Address derivation and loan issuance are separate actual machine steps;
failed issuance keeps the already executed address step. -/
def reborrow (world : State) (value : Value) (target : Target) : Result Value :=
  match parent world value with
  | none => .invalid world
  | some (index,register,lease) => match NativeByteRange.pointerAt lease.pointer target.offset with
    | none => .invalid world
    | some pointer => match NativeReferenceMachine.execute world (.raw (.withAddress register pointer.address)) with
      | none => .invalid world
      | some prepared => match NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) with
        | none => .invalid prepared
        | some next => .value (.reference true ⟨prepared.nextTag⟩ target.count) next

theorem decodeExclusive_success (world : State) (index : Nat) (value : Value)
    (decoded : decodeExclusive world index = some value) :
    ∃ reference lease, world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.mode = .exclusive ∧ lease.layout = ⟨24,8⟩ ∧ value = .reference true reference 3 := by
  simp only [decodeExclusive, Option.bind_eq_bind', Option.bind_eq_some_iff] at decoded
  obtain ⟨reference, selected, lease, found, decoded⟩ := decoded
  split at decoded
  next valid => cases decoded; exact ⟨reference,lease,selected,found,valid.1,valid.2,rfl⟩
  next => cases decoded

theorem reborrow_projects (world : State) (value : Value) (target : Target) :
    NativeReferenceMachine.Runs world (reborrow world value target).world := by
  cases selected : parent world value with
  | none => simp only [reborrow, selected, Result.world]; exact .refl _
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases shifted : NativeByteRange.pointerAt lease.pointer target.offset with
    | none => simp only [reborrow, selected, shifted, Result.world]; exact .refl _
    | some pointer =>
      cases preparedEq : NativeReferenceMachine.execute world (.raw (.withAddress register pointer.address)) with
      | none => simp only [reborrow, selected, shifted, preparedEq, Result.world]; exact .refl _
      | some prepared =>
        have first := NativeReferenceMachine.Runs.step (.refl world) _ preparedEq
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) with
        | none => simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using first
        | some next =>
          have later := NativeReferenceMachine.Runs.step (.refl prepared) _ issued
          simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using
            NativeReferenceMachine.runs_trans _ _ _ first later

theorem reborrow_success (world next : State) (value output : Value) (target : Target)
    (borrowed : reborrow world value target = .value output next) :
    ∃ index register lease pointer prepared,
      parent world value = some (index,register,lease) ∧
      NativeByteRange.pointerAt lease.pointer target.offset = some pointer ∧
      NativeReferenceMachine.execute world (.raw (.withAddress register pointer.address)) = some prepared ∧
      NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) = some next ∧
      output = .reference true ⟨prepared.nextTag⟩ target.count := by
  cases selected : parent world value with
  | none => simp only [reborrow, selected] at borrowed; cases borrowed
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases shifted : NativeByteRange.pointerAt lease.pointer target.offset with
    | none => simp only [reborrow, selected, shifted] at borrowed; cases borrowed
    | some pointer =>
      cases preparedEq : NativeReferenceMachine.execute world (.raw (.withAddress register pointer.address)) with
      | none => simp only [reborrow, selected, shifted, preparedEq] at borrowed; cases borrowed
      | some prepared =>
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) with
        | none => simp only [reborrow, selected, shifted, preparedEq, issued] at borrowed; cases borrowed
        | some final =>
          simp only [reborrow, selected, shifted, preparedEq, issued] at borrowed
          cases borrowed
          exact ⟨index,register,lease,pointer,prepared,rfl,shifted,preparedEq,issued,rfl⟩

theorem reborrow_preserves_heap (world next : State) (value output : Value) (target : Target)
    (borrowed : reborrow world value target = .value output next) :
    next.pointers.heap = world.pointers.heap := by
  obtain ⟨index,register,lease,pointer,prepared,_,_,preparedEq,issued,_⟩ := reborrow_success world next value output target borrowed
  have addressFrame : prepared.pointers.heap = world.pointers.heap := by
    simp [NativeReferenceMachine.execute, NativeReferenceMachine.rawPermissions,
      NativePointerMachine.execute, Option.map_map] at preparedEq
    obtain ⟨stored, _, same⟩ := preparedEq
    cases same
    rfl
  simp only [NativeReferenceMachine.execute, Option.bind_eq_some_iff] at issued
  obtain ⟨reference,_,stored,_,granted⟩ := issued
  obtain ⟨_,_,_,pointersEq,_⟩ := NativeReferenceMachine.grant_success prepared next (some reference.tag) .exclusive stored target.layout granted
  exact (congrArg NativePointerMachine.State.heap pointersEq).trans addressFrame

theorem reborrow_issued_reference (world next : State) (value output : Value) (target : Target)
    (borrowed : reborrow world value target = .value output next) :
    ∃ reference, output = .reference true reference target.count ∧ reference ∈ next.references := by
  obtain ⟨index,register,lease,pointer,prepared,_,_,_,issued,outputEq⟩ := reborrow_success world next value output target borrowed
  simp only [NativeReferenceMachine.execute, Option.bind_eq_some_iff] at issued
  obtain ⟨parent,_,stored,_,granted⟩ := issued
  obtain ⟨tag,ledger,executed,_,_,_,referencesEq,_⟩ :=
    NativeReferenceMachine.grant_success prepared next (some parent.tag) .exclusive stored target.layout granted
  have fresh := (NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger prepared) (some parent.tag)
    .exclusive stored target.layout tag ledger executed).1
  refine ⟨⟨prepared.nextTag⟩,outputEq,?_⟩
  rw [referencesEq, fresh]
  exact List.mem_cons_self

theorem reborrow_reachable (world : State) (value : Value) (target : Target)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (reborrow world value target).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (reborrow_projects world value target)

inductive Action where
  | pointer
  | length
  deriving DecidableEq

/-- Length is read as an aligned word at offset sixteen. A failed decode keeps
its actual read prefix; no constrained-capacity conversion is applied. -/
def lengthAccess (world : State) (index : Nat) : Result NativeWord64Memory.Word :=
  match NativeReferenceMachine.execute world (.access index 16 (.read 8 8)) with
  | none => .invalid world
  | some next => match next.outputs[0]? >>= NativeWord64Memory.decode with
    | none => .invalid next
    | some value => .value value next

/-- The source's field copy reads through its exclusive parent. It does not
copy or retag the parent's exclusive reference value. -/
def readField (world : State) (value : Value) (action : Action) : Result Value :=
  match parent world value with
  | none => .invalid world
  | some (index,_,_) => match action with
    | .pointer => match NativeRawVecFields.pointerAccess world index with
      | .invalid next => .invalid next
      | .value pointer next => .value (.raw ⟨pointer,none⟩) next
    | .length => match lengthAccess world index with
      | .invalid next => .invalid next
      | .value length next => .value (.usize length) next

theorem lengthAccess_projects (world : State) (index : Nat) :
    NativeReferenceMachine.Runs world (lengthAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 16 (.read 8 8)) with
  | none => simp only [lengthAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode <;>
      simpa only [lengthAccess, actual, decoded, Result.world] using first

theorem readField_projects (world : State) (value : Value) (action : Action) :
    NativeReferenceMachine.Runs world (readField world value action).world := by
  cases selected : parent world value with
  | none => simp only [readField, selected, Result.world]; exact .refl _
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases action with
    | pointer =>
      have first := NativeRawVecFields.pointerAccess_projects world index
      cases actual : NativeRawVecFields.pointerAccess world index <;>
        simpa only [readField, selected, actual, Result.world] using first
    | length =>
      have first := lengthAccess_projects world index
      cases actual : lengthAccess world index <;>
        simpa only [readField, selected, actual, Result.world] using first

inductive Operation where
  | borrow (target : Target)
  | field (action : Action)
  deriving DecidableEq

def eval (world : State) (value : Value) : Operation → Result Value
  | .borrow target => reborrow world value target
  | .field action => readField world value action

theorem eval_projects (world : State) (value : Value) (operation : Operation) :
    NativeReferenceMachine.Runs world (eval world value operation).world := by
  cases operation with
  | borrow target => exact reborrow_projects world value target
  | field action => exact readField_projects world value action

end FormalProof4FHE.HasteBoots.NativeVecReference
