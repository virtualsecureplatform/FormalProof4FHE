module
public import FormalProof4FHE.HasteBoots.NativeRawVecReference
@[expose] public section

/-! Checked shared reborrows from resident RawVecInner places. Reference values
retain stable tags. Native Rust reference construction and lifetime refinement
remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecBorrow
open NativeReferenceMachine (State Reference)
open NativeRawVecFields (Result)
open NativeSliceLLBC (Value)

inductive Target where
  | whole
  | allocator
  deriving DecidableEq

def Target.offset : Target → Nat
  | .whole => 0
  | .allocator => 16

def Target.layout : Target → NativeByteMemory.Layout
  | .whole => ⟨16,8⟩
  | .allocator => ⟨0,1⟩

def Target.count : Target → NativeWord64Memory.Word
  | .whole => 2
  | .allocator => 0

def decodeExclusive (world : State) (index : Nat) : Option Value := do
  let reference ← world.references[index]?
  let lease ← NativeByteBorrow.lookup world.leases reference.tag
  if lease.mode = .exclusive ∧ lease.layout = ⟨16,8⟩ then some (.reference true reference 2) else none

/-- Resolve both identities before deriving the subobject's address. -/
def parent (world : State) : Value → Option (Nat × Nat × NativeByteBorrow.Lease)
  | .reference mutable reference count => do
    if count ≠ 2 then none else do
      let lease ← NativeByteBorrow.lookup world.leases reference.tag
      let index := world.references.idxOf reference
      let register := world.pointers.registers.idxOf lease.pointer
      if lease.mode = NativeSliceLLBC.mode mutable ∧ lease.layout = ⟨16,8⟩ ∧
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
      | some prepared => match NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) with
        | none => .invalid prepared
        | some next => .value (.reference false ⟨prepared.nextTag⟩ target.count) next

theorem decodeExclusive_success (world : State) (index : Nat) (value : Value)
    (decoded : decodeExclusive world index = some value) :
    ∃ reference lease, world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.mode = .exclusive ∧ lease.layout = ⟨16,8⟩ ∧ value = .reference true reference 2 := by
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
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) with
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
      NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) = some next ∧
      output = .reference false ⟨prepared.nextTag⟩ target.count := by
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
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) with
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
  obtain ⟨_,_,_,pointersEq,_⟩ := NativeReferenceMachine.grant_success prepared next (some reference.tag) .shared stored target.layout granted
  exact (congrArg NativePointerMachine.State.heap pointersEq).trans addressFrame

theorem reborrow_issued_reference (world next : State) (value output : Value) (target : Target)
    (borrowed : reborrow world value target = .value output next) :
    ∃ reference, output = .reference false reference target.count ∧ reference ∈ next.references := by
  obtain ⟨index,register,lease,pointer,prepared,_,_,_,issued,outputEq⟩ := reborrow_success world next value output target borrowed
  simp only [NativeReferenceMachine.execute, Option.bind_eq_some_iff] at issued
  obtain ⟨parent,_,stored,_,granted⟩ := issued
  obtain ⟨tag,ledger,executed,_,_,_,referencesEq,_⟩ :=
    NativeReferenceMachine.grant_success prepared next (some parent.tag) .shared stored target.layout granted
  have fresh := (NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger prepared) (some parent.tag)
    .shared stored target.layout tag ledger executed).1
  refine ⟨⟨prepared.nextTag⟩,outputEq,?_⟩
  rw [referencesEq, fresh]
  exact List.mem_cons_self

theorem reborrow_reachable (world : State) (value : Value) (target : Target)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (reborrow world value target).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (reborrow_projects world value target)

end FormalProof4FHE.HasteBoots.NativeRawVecBorrow
