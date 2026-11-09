module
public import FormalProof4FHE.HasteBoots.NativeRawVecBorrow
@[expose] public section

/-! Restricted whole-object mutable reservation/activation for adjacent source
borrow/call pairs. Intervening arguments must preserve the machine world. This
is not a general Rust two-phase-borrow or lifetime correspondence theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)
open NativeRawVecFields (Result)

structure Reservation where
  parent : Reference
  pointer : NativePointerStorage.Pointer
  deriving DecidableEq

/-- Derive the address and check shared reservation permission, without issuing
an exclusive reference value or adding a loan to the ledger. -/
def reserve (world : State) (value : Value) : Result Reservation :=
  match value with
  | .reference true reference _ =>
    match NativeRawVecBorrow.parent world value with
    | none => .invalid world
    | some (_,register,lease) =>
      match NativeReferenceMachine.execute world (.raw (.withAddress register lease.pointer.address)) with
      | none => .invalid world
      | some prepared =>
        if NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger prepared) (some reference.tag)
            .shared lease.pointer ⟨16,8⟩ then
          .value ⟨reference,lease.pointer⟩ prepared
        else .invalid prepared
  | _ => .invalid world

/-- Resolve the reserved identities again and issue the checked exclusive loan. -/
def activate (world : State) (reservation : Reservation) : Result Value :=
  let index := world.references.idxOf reservation.parent
  let register := world.pointers.registers.idxOf reservation.pointer
  if world.references[index]? = some reservation.parent ∧
      world.pointers.registers[register]? = some reservation.pointer then
    match NativeReferenceMachine.execute world (.reborrow index register .exclusive ⟨16,8⟩) with
    | none => .invalid world
    | some next => .value (.reference true ⟨world.nextTag⟩ 2) next
  else .invalid world

def immediate (world : State) (value : Value) : Result Value :=
  match reserve world value with
  | .invalid next => .invalid next
  | .value reservation next => activate next reservation

theorem reserve_projects (world : State) (value : Value) :
    NativeReferenceMachine.Runs world (reserve world value).world := by
  cases value with
  | unit => exact .refl _
  | usize word => exact .refl _
  | raw pointer => exact .refl _
  | reference mutable reference count =>
    cases mutable with
    | false => exact .refl _
    | true =>
      cases selected : NativeRawVecBorrow.parent world (.reference true reference count) with
      | none => simp only [reserve, selected, Result.world]; exact .refl _
      | some entry =>
        rcases entry with ⟨index,register,lease⟩
        cases actual : NativeReferenceMachine.execute world (.raw (.withAddress register lease.pointer.address)) with
        | none => simp only [reserve, selected, actual, Result.world]; exact .refl _
        | some prepared =>
          have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
          simp only [reserve, selected, actual]
          split <;> exact first

theorem activate_projects (world : State) (reservation : Reservation) :
    NativeReferenceMachine.Runs world (activate world reservation).world := by
  simp only [activate]
  split
  · cases actual : NativeReferenceMachine.execute world (.reborrow
        (world.references.idxOf reservation.parent) (world.pointers.registers.idxOf reservation.pointer) .exclusive ⟨16,8⟩) with
    | none => exact .refl _
    | some next => exact NativeReferenceMachine.Runs.step (.refl world) _ actual
  · exact .refl _

theorem immediate_projects (world : State) (value : Value) :
    NativeReferenceMachine.Runs world (immediate world value).world := by
  have first := reserve_projects world value
  cases actual : reserve world value with
  | invalid next => simpa only [immediate, actual, Result.world] using first
  | value reservation next =>
    rw [actual] at first
    simpa only [immediate, actual, Result.world] using
      NativeReferenceMachine.runs_trans _ _ _ first (activate_projects next reservation)

theorem reserve_success (world next : State) (value : Value) (reservation : Reservation)
    (reserved : reserve world value = .value reservation next) :
    ∃ index register lease reference count,
      value = .reference true reference count ∧
      NativeRawVecBorrow.parent world value = some (index,register,lease) ∧
      NativeReferenceMachine.execute world (.raw (.withAddress register lease.pointer.address)) = some next ∧
      NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger next) (some reference.tag) .shared lease.pointer ⟨16,8⟩ = true ∧
      reservation = ⟨reference,lease.pointer⟩ := by
  cases value with
  | unit => cases reserved
  | usize word => cases reserved
  | raw pointer => cases reserved
  | reference mutable reference count =>
    cases mutable with
    | false => cases reserved
    | true =>
      cases selected : NativeRawVecBorrow.parent world (.reference true reference count) with
      | none => simp only [reserve, selected] at reserved; cases reserved
      | some entry =>
        rcases entry with ⟨index,register,lease⟩
        cases actual : NativeReferenceMachine.execute world (.raw (.withAddress register lease.pointer.address)) with
        | none => simp only [reserve, selected, actual] at reserved; cases reserved
        | some prepared =>
          simp only [reserve, selected, actual] at reserved
          split at reserved
          next permitted => cases reserved; exact ⟨index,register,lease,reference,count,rfl,rfl,actual,permitted,rfl⟩
          next => cases reserved

theorem reserve_no_loan (world next : State) (value : Value) (reservation : Reservation)
    (reserved : reserve world value = .value reservation next) :
    next.nextTag = world.nextTag ∧ next.leases = world.leases ∧ next.references = world.references ∧
      next.births = world.births ∧ next.pointers.heap = world.pointers.heap := by
  obtain ⟨_,register,lease,_,_,_,_,actual,_,_⟩ := reserve_success world next value reservation reserved
  simp [NativeReferenceMachine.execute, NativeReferenceMachine.rawPermissions,
    NativePointerMachine.execute, Option.map_map] at actual
  obtain ⟨stored,_,same⟩ := actual
  cases same
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem activate_success (world next : State) (reservation : Reservation) (value : Value)
    (activated : activate world reservation = .value value next) :
    NativeReferenceMachine.execute world (.reborrow (world.references.idxOf reservation.parent)
      (world.pointers.registers.idxOf reservation.pointer) .exclusive ⟨16,8⟩) = some next ∧
      value = .reference true ⟨world.nextTag⟩ 2 := by
  simp only [activate] at activated
  split at activated
  · split at activated
    next => cases activated
    next actual => cases activated; exact ⟨actual,rfl⟩
  · cases activated

end FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow
