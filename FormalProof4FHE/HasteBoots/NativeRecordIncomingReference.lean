module
public import FormalProof4FHE.HasteBoots.NativeIncomingReference
@[expose] public section

/-! Incoming registers, birth records and older leases through aggregate
rvalue evaluation. These statements frame authority, not heap contents or native
Rust lifetimes. The evaluator's existing operational projections remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeIncomingReference
open NativeReferenceMachine (State Op)
theorem Preserves.step {start before after : State} (prior : Preserves start before) (op : Op)
    (executed : NativeReferenceMachine.execute before op = some after)
    (checked : keepsLoans op = true := by rfl) : Preserves start after :=
  prior.trans (NativeIncomingReference.step before after op executed checked)

theorem runs_trans (start middle finish : State) (first : Preserves start middle) (second : Preserves middle finish) :
    Preserves start finish := first.trans second
end FormalProof4FHE.HasteBoots.NativeIncomingReference

namespace FormalProof4FHE.HasteBoots.NativeSliceLLBC
open NativeReferenceMachine (State)

theorem issue_incoming_projects (world next : State) (mutable : Bool) (input output : Value) {element : Element}
    (issued : issue world mutable input element = some (output,next)) : NativeIncomingReference.Preserves world next := by
  cases input with
  | unit => cases issued
  | usize word => cases issued
  | raw raw =>
    rcases raw with ⟨pointer,length⟩
    cases length with
    | none => cases issued
    | some length =>
      simp only [issue] at issued
      split at issued
      · obtain ⟨final,actual,same⟩ := Option.map_eq_some_iff.mp issued
        cases same
        exact NativeIncomingReference.Preserves.step (.refl world) _ actual
      · cases issued
  | reference parent reference length =>
    simp only [issue, Option.bind_eq_some_iff] at issued
    obtain ⟨lease,_,issued⟩ := issued
    split at issued
    · obtain ⟨final,actual,same⟩ := Option.map_eq_some_iff.mp issued
      cases same
      exact NativeIncomingReference.Preserves.step (.refl world) _ actual
    · cases issued

end FormalProof4FHE.HasteBoots.NativeSliceLLBC

namespace FormalProof4FHE.HasteBoots.NativeSliceLLBC
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeReferenceMachine (State Reference)
theorem retagValue_incoming_projects (frame next : Frame) (input output : Value) (enabled : Bool) (element : Element)
    (tagged : retagValue frame input enabled element = some (output, next)) :
    NativeIncomingReference.Preserves frame.world next.world := by
  cases enabled with
  | false => cases tagged; exact .refl _
  | true =>
    cases input with
    | unit => cases tagged; exact .refl _
    | usize word => cases tagged; exact .refl _
    | raw pointer => cases tagged; exact .refl _
    | reference mutable reference length =>
      simp only [retagValue, ite_true, Option.map_eq_some_iff] at tagged
      obtain ⟨⟨value, world⟩, actual, same⟩ := tagged
      cases same
      exact issue_incoming_projects _ _ _ _ _ actual


end FormalProof4FHE.HasteBoots.NativeSliceLLBC

namespace FormalProof4FHE.HasteBoots.NativeRawVecFields
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
theorem capacityAccess_incoming_projects (world : State) (index : Nat) :
    NativeIncomingReference.Preserves world (capacityAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => simp only [capacityAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeIncomingReference.Preserves.step (.refl world) _ actual
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simpa only [capacityAccess, actual, decoded, Result.world] using first
    | some value =>
      simp only [capacityAccess, actual, decoded]
      split <;> exact first


theorem pointerAccess_incoming_projects (world : State) (index : Nat) :
    NativeIncomingReference.Preserves world (pointerAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => simp only [pointerAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeIncomingReference.Preserves.step (.refl world) _ actual
    cases found : next.pointers.registers[0]? with
    | none => simpa only [pointerAccess, actual, found, Result.world] using first
    | some value =>
      simp only [pointerAccess, actual, found]
      split <;> exact first


theorem markerAccess_incoming_projects (world : State) (index : Nat) :
    NativeIncomingReference.Preserves world (markerAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 16 (.read 0 1)) with
  | none => simp only [markerAccess, actual, Result.world]; exact .refl _
  | some next =>
    simpa only [markerAccess, actual, Result.world] using NativeIncomingReference.Preserves.step (.refl world) _ actual


end FormalProof4FHE.HasteBoots.NativeRawVecFields

namespace FormalProof4FHE.HasteBoots.NativeRawVecReference
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)
open NativeRawVecFields (Result)
theorem eval_incoming_projects (world : State) (value : Value) (action : Action) :
    NativeIncomingReference.Preserves world (eval world value action).world := by
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
            have first := NativeRawVecFields.capacityAccess_incoming_projects world index
            cases loaded : NativeRawVecFields.capacityAccess world index <;> simpa only [loaded, Result.world] using first
          | marker =>
            have first := NativeRawVecFields.markerAccess_incoming_projects world index
            cases loaded : NativeRawVecFields.markerAccess world index <;> simpa only [loaded, Result.world] using first
          | pointer =>
            have first := NativeRawVecFields.pointerAccess_incoming_projects world index
            cases loaded : NativeRawVecFields.pointerAccess world index <;> simpa only [loaded, Result.world] using first


end FormalProof4FHE.HasteBoots.NativeRawVecReference

namespace FormalProof4FHE.HasteBoots.NativeRawVecBorrow
open NativeReferenceMachine (State Reference)
open NativeRawVecFields (Result)
open NativeSliceLLBC (Value)
theorem reborrow_incoming_projects (world : State) (value : Value) (target : Target) :
    NativeIncomingReference.Preserves world (reborrow world value target).world := by
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
        have first := NativeIncomingReference.Preserves.step (.refl world) _ preparedEq
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) with
        | none => simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using first
        | some next =>
          have later := NativeIncomingReference.Preserves.step (.refl prepared) _ issued
          simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using
            NativeIncomingReference.runs_trans _ _ _ first later


end FormalProof4FHE.HasteBoots.NativeRawVecBorrow

namespace FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)
open NativeRawVecFields (Result)
theorem reserve_incoming_projects (world : State) (value : Value) :
    NativeIncomingReference.Preserves world (reserve world value).world := by
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
          have first := NativeIncomingReference.Preserves.step (.refl world) _ actual
          simp only [reserve, selected, actual]
          split <;> exact first


theorem activate_incoming_projects (world : State) (reservation : Reservation) :
    NativeIncomingReference.Preserves world (activate world reservation).world := by
  simp only [activate]
  split
  · cases actual : NativeReferenceMachine.execute world (.reborrow
        (world.references.idxOf reservation.parent) (world.pointers.registers.idxOf reservation.pointer) .exclusive ⟨16,8⟩) with
    | none => exact .refl _
    | some next => exact NativeIncomingReference.Preserves.step (.refl world) _ actual
  · exact .refl _


theorem immediate_incoming_projects (world : State) (value : Value) :
    NativeIncomingReference.Preserves world (immediate world value).world := by
  have first := reserve_incoming_projects world value
  cases actual : reserve world value with
  | invalid next => simpa only [immediate, actual, Result.world] using first
  | value reservation next =>
    rw [actual] at first
    simpa only [immediate, actual, Result.world] using
      NativeIncomingReference.runs_trans _ _ _ first (activate_incoming_projects next reservation)


end FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow

namespace FormalProof4FHE.HasteBoots.NativeVecReference
open NativeReferenceMachine (State Reference)
open NativeRawVecFields (Result)
open NativeSliceLLBC (Value)
theorem reborrow_incoming_projects (world : State) (value : Value) (target : Target) :
    NativeIncomingReference.Preserves world (reborrow world value target).world := by
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
        have first := NativeIncomingReference.Preserves.step (.refl world) _ preparedEq
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) with
        | none => simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using first
        | some next =>
          have later := NativeIncomingReference.Preserves.step (.refl prepared) _ issued
          simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using
            NativeIncomingReference.runs_trans _ _ _ first later


theorem lengthAccess_incoming_projects (world : State) (index : Nat) :
    NativeIncomingReference.Preserves world (lengthAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 16 (.read 8 8)) with
  | none => simp only [lengthAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeIncomingReference.Preserves.step (.refl world) _ actual
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode <;>
      simpa only [lengthAccess, actual, decoded, Result.world] using first


theorem readField_incoming_projects (world : State) (value : Value) (action : Action) :
    NativeIncomingReference.Preserves world (readField world value action).world := by
  cases selected : parent world value with
  | none => simp only [readField, selected, Result.world]; exact .refl _
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases action with
    | pointer =>
      have first := NativeRawVecFields.pointerAccess_incoming_projects world index
      cases actual : NativeRawVecFields.pointerAccess world index <;>
        simpa only [readField, selected, actual, Result.world] using first
    | length =>
      have first := lengthAccess_incoming_projects world index
      cases actual : lengthAccess world index <;>
        simpa only [readField, selected, actual, Result.world] using first


theorem eval_incoming_projects (world : State) (value : Value) (operation : Operation) :
    NativeIncomingReference.Preserves world (eval world value operation).world := by
  cases operation with
  | borrow target => exact reborrow_incoming_projects world value target
  | field action => exact readField_incoming_projects world value action


end FormalProof4FHE.HasteBoots.NativeVecReference

namespace FormalProof4FHE.HasteBoots.NativeRecordLLBC
open NativeRecordValues (Ty Value Path)
open NativeReferenceMachine (State)
open NativeSliceLLBC (Element)
open NativeWord64Memory (Word)
open NativeByteDropCalls (Classification)
theorem retag_incoming_projects (world : State) (value : Value) (enabled : Bool) (element : Element) :
    NativeIncomingReference.Preserves world (retag world value enabled element).world := by
  induction value generalizing world with
  | scalar value =>
    cases enabled with
    | false => exact .refl _
    | true =>
      cases actual : NativeSliceLLBC.retagValue ⟨[],[],world⟩ value true element with
      | none => simp only [retag, actual, Tagged.world]; exact .refl _
      | some result =>
        rcases result with ⟨output,frame⟩
        simpa only [retag, actual, Tagged.world] using
          NativeSliceLLBC.retagValue_incoming_projects ⟨[],[],world⟩ frame value output true element actual
  | pair left right leftIH rightIH =>
    cases enabled with
    | false => exact .refl _
    | true =>
      have first := leftIH world
      cases firstEq : retag world left true element with
      | invalid rejected => simpa only [retag, firstEq, Tagged.world] using first
      | value value middle =>
        have second := rightIH middle
        rw [firstEq] at first
        cases secondEq : retag middle right true element with
        | invalid rejected =>
          rw [secondEq] at second
          simp only [retag, firstEq, secondEq, Tagged.world]
          exact NativeIncomingReference.runs_trans _ _ _ first second
        | value output final =>
          rw [secondEq] at second
          simp only [retag, firstEq, secondEq, Tagged.world]
          exact NativeIncomingReference.runs_trans _ _ _ first second
  | choice side fields ih =>
    cases enabled with
    | false => exact .refl _
    | true =>
      have first := ih world
      cases actual : retag world fields true element with
      | invalid rejected => simpa only [retag, actual, Tagged.world] using first
      | value output final => simpa only [retag, actual, Tagged.world] using first
  | record tag fields ih =>
    cases enabled with
    | false => exact .refl _
    | true =>
      have first := ih world
      cases actual : retag world fields true element with
      | invalid rejected => simpa only [retag, actual, Tagged.world] using first
      | value output final => simpa only [retag, actual, Tagged.world] using first
  | enumeration tag value => cases enabled <;> exact .refl _
  | boolean value => cases enabled <;> exact .refl _
  | uninit => cases enabled <;> exact .refl _


theorem evalRawVecField_incoming_projects (frame : Frame) (operand : Operand) (action : NativeRawVecReference.Action) (enabled : Bool) :
    NativeIncomingReference.Preserves frame.world (evalRawVecField frame operand action enabled).world := by
  cases selected : evalOperand frame operand with
  | none => simp only [evalRawVecField, selected, Evaluated.world]; exact .refl _
  | some result =>
    rcases result with ⟨value,caller⟩
    have same := evalOperand_world frame caller operand value selected
    cases value with
    | scalar value =>
      have first := NativeRawVecReference.eval_incoming_projects caller.world value action
      cases actual : NativeRawVecReference.eval caller.world value action with
      | invalid rejected =>
        rw [actual] at first
        simp only [evalRawVecField, selected, actual, Evaluated.world]
        simpa only [NativeRawVecFields.Result.world, same] using first
      | value output next =>
        rw [actual] at first
        have readPrefix : NativeIncomingReference.Preserves frame.world next := by
          simpa only [NativeRawVecFields.Result.world, same] using first
        have second := retag_incoming_projects next (.scalar output) enabled .word
        cases tagged : retag next (.scalar output) enabled .word with
        | invalid final =>
          rw [tagged] at second
          simp only [evalRawVecField, selected, actual, tagged, Evaluated.world]
          exact NativeIncomingReference.runs_trans _ _ _ readPrefix second
        | value result final =>
          rw [tagged] at second
          simp only [evalRawVecField, selected, actual, tagged, Evaluated.world]
          exact NativeIncomingReference.runs_trans _ _ _ readPrefix second
    | choice side fields => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | pair left right => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | record tag fields => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | enumeration tag value => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | boolean value => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | uninit => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _


theorem evalRawVecBorrow_incoming_projects (frame : Frame) (index : Nat) (path : Path) (target : NativeRawVecBorrow.Target) :
    NativeIncomingReference.Preserves frame.world (evalRawVecBorrow frame index path target).world := by
  cases selected : read frame index path with
  | none => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value =>
      have first := NativeRawVecBorrow.reborrow_incoming_projects frame.world value target
      cases actual : NativeRawVecBorrow.reborrow frame.world value target <;>
        simpa only [evalRawVecBorrow, selected, actual, Evaluated.world, NativeRawVecFields.Result.world] using first
    | choice side fields => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | pair left right => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | record tag fields => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | enumeration tag value => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | boolean value => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | uninit => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _


theorem reserveRawVec_incoming_projects (frame : Frame) (index : Nat) (path : Path) :
    NativeIncomingReference.Preserves frame.world (reserveRawVec frame index path).world := by
  cases selected : read frame index path with
  | none => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value => simpa only [reserveRawVec, selected] using NativeRawVecMutBorrow.reserve_incoming_projects frame.world value
    | choice side fields => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | pair left right => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | record tag fields => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | enumeration tag value => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | boolean value => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | uninit => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _


theorem evalRawVecMutBorrow_incoming_projects (frame : Frame) (index : Nat) (path : Path) :
    NativeIncomingReference.Preserves frame.world (evalRawVecMutBorrow frame index path).world := by
  have first := reserveRawVec_incoming_projects frame index path
  cases selected : reserveRawVec frame index path with
  | invalid next => simpa only [evalRawVecMutBorrow, selected, Evaluated.world, NativeRawVecFields.Result.world] using first
  | value reservation prepared =>
    rw [selected] at first
    have second := NativeRawVecMutBorrow.activate_incoming_projects prepared reservation
    cases actual : NativeRawVecMutBorrow.activate prepared reservation <;>
      simpa only [evalRawVecMutBorrow, selected, actual, Evaluated.world, NativeRawVecFields.Result.world] using
        NativeIncomingReference.runs_trans _ _ _ first second


theorem evalVec_incoming_projects (frame : Frame) (index : Nat) (path : Path) (operation : NativeVecReference.Operation) :
    NativeIncomingReference.Preserves frame.world (evalVec frame index path operation).world := by
  cases selected : read frame index path with
  | none => simp only [evalVec, selected, Evaluated.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value =>
      have first := NativeVecReference.eval_incoming_projects frame.world value operation
      cases actual : NativeVecReference.eval frame.world value operation <;>
        simpa only [evalVec, selected, actual, Evaluated.world, NativeRawVecFields.Result.world] using first
    | choice side fields => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | pair left right => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | record tag fields => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | enumeration tag value => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | boolean value => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | uninit => simp only [evalVec, selected, Evaluated.world]; exact .refl _


theorem evalBorrowSlice_incoming_projects (frame : Frame) (index : Nat) (path : Path) :
    NativeIncomingReference.Preserves frame.world (evalBorrowSlice frame index path).world := by
  cases selected : read frame index path with
  | none => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value =>
      cases issued : NativeSliceLLBC.issue frame.world true value .byte with
      | none => simp only [evalBorrowSlice, selected, issued, Evaluated.world]; exact .refl _
      | some pair =>
        rcases pair with ⟨output,next⟩
        simpa only [evalBorrowSlice, selected, issued, Evaluated.world] using NativeSliceLLBC.issue_incoming_projects frame.world next true value output issued
    | choice side fields => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | pair left right => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | record tag fields => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | enumeration tag word => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | boolean value => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | uninit => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _


theorem evalZstBorrow_incoming_projects (frame : Frame) (index tag : Nat) (address : NativeWord64Memory.Word) :
    NativeIncomingReference.Preserves frame.world (evalZstBorrow frame index tag address).world := by
  have issued : NativeIncomingReference.Preserves frame.world (NativeZstBorrow.issue frame.world address).world := by
    cases preparedEq : NativeReferenceMachine.execute frame.world (.raw (.fromAddress address)) with
    | none => simp only [NativeZstBorrow.issue,preparedEq,NativeRawVecFields.Result.world]; exact .refl _
    | some prepared =>
      have first := NativeIncomingReference.Preserves.step (.refl frame.world) _ preparedEq
      cases actual : NativeReferenceMachine.execute prepared (.borrow 0 .shared ⟨0,1⟩) with
      | none => simpa only [NativeZstBorrow.issue,preparedEq,actual,NativeRawVecFields.Result.world] using first
      | some next =>
        have later := NativeIncomingReference.Preserves.step (.refl prepared) _ actual
        simpa only [NativeZstBorrow.issue,preparedEq,actual,NativeRawVecFields.Result.world] using first.trans later
  unfold evalZstBorrow
  split
  · cases actual : NativeZstBorrow.issue frame.world address <;>
      simpa only [actual,Evaluated.world,NativeRawVecFields.Result.world] using issued
  · exact .refl _

theorem evalZstMutBorrow_incoming_projects (frame : Frame) (index tag : Nat) (address : NativeWord64Memory.Word) :
    NativeIncomingReference.Preserves frame.world (evalZstMutBorrow frame index tag address).world := by
  have issued : NativeIncomingReference.Preserves frame.world (NativeZstBorrow.issueExclusive frame.world address).world := by
    cases preparedEq : NativeReferenceMachine.execute frame.world (.raw (.fromAddress address)) with
    | none => simp only [NativeZstBorrow.issueExclusive,preparedEq,NativeRawVecFields.Result.world]; exact .refl _
    | some prepared =>
      have first := NativeIncomingReference.Preserves.step (.refl frame.world) _ preparedEq
      cases actual : NativeReferenceMachine.execute prepared (.borrow 0 .exclusive ⟨0,1⟩) with
      | none => simpa only [NativeZstBorrow.issueExclusive,preparedEq,actual,NativeRawVecFields.Result.world] using first
      | some next =>
        have later := NativeIncomingReference.Preserves.step (.refl prepared) _ actual
        simpa only [NativeZstBorrow.issueExclusive,preparedEq,actual,NativeRawVecFields.Result.world] using first.trans later
  unfold evalZstMutBorrow
  split
  · cases actual : NativeZstBorrow.issueExclusive frame.world address <;>
      simpa only [actual,Evaluated.world,NativeRawVecFields.Result.world] using issued
  · exact .refl _

theorem evalRvalue_incoming_projects (frame : Frame) (rvalue : Rvalue) :
    NativeIncomingReference.Preserves frame.world (evalRvalue frame rvalue).world := by
  induction rvalue with
  | arithmetic operation args =>
    change NativeIncomingReference.Preserves frame.world (evalArithmetic frame operation args).world
    rw [evalArithmetic_world]; exact .refl _
  | vec operation index path => exact evalVec_incoming_projects frame index path operation
  | borrowSlice index path => exact evalBorrowSlice_incoming_projects frame index path
  | parts data length =>
    change NativeIncomingReference.Preserves frame.world (evalParts frame data length).world
    rw [evalParts_world]; exact .refl _
  | unit => exact .refl _
  | borrowRawVecMut index path => exact evalRawVecMutBorrow_incoming_projects frame index path
  | borrowZstLocal index tag address => exact evalZstBorrow_incoming_projects frame index tag address
  | borrowZstMutLocal index tag address => exact evalZstMutBorrow_incoming_projects frame index tag address
  | borrowRawVec target index path => exact evalRawVecBorrow_incoming_projects frame index path target
  | mulUsizeUB left right =>
    change NativeIncomingReference.Preserves frame.world (evalMultiply frame left right).world
    rw [evalMultiply_world]; exact .refl _
  | enumAddress operand enumTag recordTag =>
    change NativeIncomingReference.Preserves frame.world (evalEnumAddress frame operand enumTag recordTag).world
    rw [evalEnumAddress_world]; exact .refl _
  | enumWord operand tag =>
    change NativeIncomingReference.Preserves frame.world (evalEnumWord frame operand tag).world
    rw [evalEnumWord_world]; exact .refl _
  | recordResult tag singleton inner ih =>
    cases selected : evalRvalue frame inner with
    | invalid world => simpa only [evalRvalue, selected, Evaluated.world] using ih
    | value value caller =>
      cases actual : recordResultValue tag singleton value <;>
        simpa only [evalRvalue, selected, actual, Evaluated.world] using ih
  | rawVecField action operand enabled => exact evalRawVecField_incoming_projects frame operand action enabled
  | aggregate tag side fields =>
    cases selected : evalArgs frame fields with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      simp only [evalRvalue, selected, Evaluated.world]
      rw [evalArgs_world frame caller fields values selected]
      exact .refl _
  | use operand enabled element =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      have first := retag_incoming_projects caller.world value enabled element
      cases actual : retag caller.world value enabled element with
      | invalid rejected =>
        rw [actual] at first
        simp only [evalRvalue, selected, actual, Evaluated.world]
        simpa only [same, Tagged.world] using first
      | value output world =>
        rw [actual] at first
        simp only [evalRvalue, selected, actual, Evaluated.world]
        simpa only [same, Tagged.world] using first
  | choice side operand =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      simp only [evalRvalue, selected, Evaluated.world]
      rw [evalOperand_world frame caller operand value selected]
      exact .refl _
  | wrapOne tag operand =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      simp only [evalRvalue, selected, Evaluated.world]
      rw [evalOperand_world frame caller operand value selected]
      exact .refl _
  | knownDiscriminant index descriptor =>
    change NativeIncomingReference.Preserves frame.world (evalKnownDiscriminant frame index descriptor).world
    rw [evalKnownDiscriminant_world]; exact .refl _
  | rawThin operand =>
    change NativeIncomingReference.Preserves frame.world (evalRawThin frame operand).world
    rw [evalRawThin_world]; exact .refl _
  | rawAddress operand =>
    change NativeIncomingReference.Preserves frame.world (evalRawAddress frame operand).world
    rw [evalRawAddress_world]; exact .refl _
  | rawCast operand =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      cases value with
      | scalar value =>
        cases value with
        | raw pointer =>
          by_cases thin : pointer.length = none
          · simp only [evalRvalue, selected, thin, ite_true, Evaluated.world]
            rw [same]; exact .refl _
          · simp only [evalRvalue, selected, thin, ite_false, Evaluated.world]
            rw [same]; exact .refl _
        | unit => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
        | usize word => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
        | reference mutable reference length => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | pair left right => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | choice side fields => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | record tag fields => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | enumeration tag value => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | boolean value => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | uninit => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
  | pair left right =>
    cases selected : evalArgs frame [left,right] with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := evalArgs_world frame caller [left,right] values selected
      simp only [evalRvalue, selected]
      split
      · change NativeIncomingReference.Preserves frame.world caller.world
        rw [same]; exact .refl _
      · change NativeIncomingReference.Preserves frame.world caller.world
        rw [same]; exact .refl _



theorem settle_incoming_projects (entered : State) (flow : Flow)
    (prior : NativeIncomingReference.Preserves entered flow.world) :
    NativeIncomingReference.Preserves entered (settle entered flow).world := by
  cases flow with
  | normal frame => exact prior
  | unwind world => exact prior
  | invalid world => exact prior
  | unsupported source world => exact prior
  | returned value world =>
    cases value with
    | pair left right => exact prior
    | choice side fields => exact prior
    | record tag fields => exact prior
    | enumeration tag value => exact prior
    | boolean value => exact prior
    | uninit => exact prior
    | scalar value =>
      cases value with
      | usize value => exact prior
      | raw pointer => exact prior
      | reference mutable reference length => exact prior
      | unit =>
        have kept := NativeIncomingReference.closeScope entered world prior
        by_cases complete : (NativeReferenceCleanup.closeScope entered world).pending.isEmpty = true
        · simpa only [settle, NativeReferenceCleanup.settleUnit, complete, ite_true, Flow.world] using kept
        · simpa only [settle, NativeReferenceCleanup.settleUnit, complete, Bool.false_eq_true, ite_false, NativeSliceLLBC.Flow.world, Flow.world] using kept

theorem deallocate_incoming_projects (frame : Frame) (pointer size alignment : Operand) (tag : Nat) :
    NativeIncomingReference.Preserves frame.world (deallocate frame pointer size alignment tag).world := by
  cases selected : evalArgs frame [pointer,size,alignment] with
  | none => simp only [deallocate, selected, Flow.world]; exact .refl _
  | some result =>
    rcases result with ⟨values,caller⟩
    have same := evalArgs_world frame caller [pointer,size,alignment] values selected
    simp only [deallocate, selected]
    split
    next raw bytes actual align =>
      by_cases matched : actual = tag
      · simp only [matched, ite_true]
        cases freed : NativeByteDeallocation.execute caller.world raw bytes align with
        | none => simp only [Flow.world]; rw [same]; exact .refl _
        | some world =>
          have first := NativeIncomingReference.step caller.world world _
            (NativeByteDeallocation.execute_success caller.world world raw bytes align freed).2.2.2.2
          simpa only [Flow.world, same] using first
      · simp only [matched, ite_false, Flow.world]; rw [same]; exact .refl _
    next => change NativeIncomingReference.Preserves frame.world caller.world; rw [same]; exact .refl _

theorem eval_incoming_projects (body : Body) (frame : Frame) :
    NativeIncomingReference.Preserves frame.world (eval body frame).world := by
  induction body generalizing frame with
  | done => exact .refl _
  | ret =>
    cases selected : read frame 0 [] <;> simp only [eval, selected, Flow.world] <;> exact .refl _
  | resume => exact .refl _
  | abort => exact .refl _
  | unsupported source => exact .refl _
  | live index next ih =>
    cases changed : storageLive frame index with
    | none => simp only [eval, changed, Flow.world]; exact .refl _
    | some caller =>
      simp only [eval, changed]
      have first := ih caller
      simpa only [storageLive_world frame caller index changed] using first
  | dead index next ih =>
    cases changed : storageDead frame index with
    | none => simp only [eval, changed, Flow.world]; exact .refl _
    | some caller =>
      simp only [eval, changed]
      have first := ih caller
      simpa only [storageDead_world frame caller index changed] using first
  | assign index rvalue next ih =>
    have first := evalRvalue_incoming_projects frame rvalue
    cases actual : evalRvalue frame rvalue with
    | invalid world => simpa only [eval, actual, Evaluated.world, Flow.world] using first
    | value value caller =>
      rw [actual] at first
      cases written : write caller index value with
      | none => simpa only [eval, actual, written, Evaluated.world, Flow.world] using first
      | some changed =>
        simp only [eval, actual, written]
        have second := ih changed
        rw [write_world caller changed index value written] at second
        exact NativeIncomingReference.runs_trans _ _ _ first second
  | switchBoolean operand yes no next yesIH noIH nextIH =>
    cases selected : evalBooleanOperand frame operand with
    | none => simp only [eval,selected,Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨condition,caller⟩
      have same := evalBooleanOperand_world frame caller operand condition selected
      have first : NativeIncomingReference.Preserves frame.world
          (if condition then eval yes caller else eval no caller).world := by
        rw [← same]
        cases condition
        · exact noIH caller
        · exact yesIH caller
      simp only [eval,selected]
      generalize chosen : (if condition then eval yes caller else eval no caller) = branch at first ⊢
      cases branch with
      | normal changed => exact NativeIncomingReference.runs_trans _ _ _ first (nextIH changed)
      | returned value world => exact first
      | unwind world => exact first
      | invalid world => exact first
      | unsupported source world => exact first
  | constIf condition yes no next yesIH noIH nextIH =>
    have first : NativeIncomingReference.Preserves frame.world
        (if condition then eval yes frame else eval no frame).world := by
      cases condition
      · exact noIH frame
      · exact yesIH frame
    simp only [eval]
    generalize chosen : (if condition then eval yes frame else eval no frame) = branch at first ⊢
    cases branch with
    | normal changed => exact NativeIncomingReference.runs_trans _ _ _ first (nextIH changed)
    | returned value world => exact first
    | unwind world => exact first
    | invalid world => exact first
    | unsupported source world => exact first
  | matchChoice index path tag left right next leftIH rightIH nextIH =>
    cases selected : selectChoice frame index path tag with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some side =>
      have first : NativeIncomingReference.Preserves frame.world
          (if side then eval right frame else eval left frame).world := by
        cases side
        · exact leftIH frame
        · exact rightIH frame
      simp only [eval, selected]
      generalize chosen : (if side then eval right frame else eval left frame) = branch at first ⊢
      cases branch with
      | normal changed => exact NativeIncomingReference.runs_trans _ _ _ first (nextIH changed)
      | returned value world => exact first
      | unwind world => exact first
      | invalid world => exact first
      | unsupported source world => exact first
  | switchUsize operand expected yes no next yesIH noIH nextIH =>
    cases selected : evalOperand frame operand with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      cases value with
      | pair left right => simp only [eval, selected, Flow.world]; exact .refl _
      | choice side fields => simp only [eval, selected, Flow.world]; exact .refl _
      | record tag fields => simp only [eval, selected, Flow.world]; exact .refl _
      | enumeration tag value => simp only [eval, selected, Flow.world]; exact .refl _
      | boolean value => simp only [eval, selected, Flow.world]; exact .refl _
      | uninit => simp only [eval, selected, Flow.world]; exact .refl _
      | scalar value =>
        cases value with
        | unit => simp only [eval, selected, Flow.world]; exact .refl _
        | raw pointer => simp only [eval, selected, Flow.world]; exact .refl _
        | reference mutable reference length => simp only [eval, selected, Flow.world]; exact .refl _
        | usize word =>
          have first : NativeIncomingReference.Preserves frame.world
              (if word = expected then eval yes caller else eval no caller).world := by
            rw [← same]
            split
            · exact yesIH caller
            · exact noIH caller
          simp only [eval, selected]
          generalize chosen : (if word = expected then eval yes caller else eval no caller) = branch at first ⊢
          cases branch with
          | normal changed => exact NativeIncomingReference.runs_trans _ _ _ first (nextIH changed)
          | returned value world => exact first
          | unwind world => exact first
          | invalid world => exact first
          | unsupported source world => exact first
  | deallocate pointer size alignment tag => exact deallocate_incoming_projects frame pointer size alignment tag
  | twoPhaseRawVecCall parent path reserved name classification types argCount target rest callee unwind next calleeIH unwindIH nextIH =>
    by_cases pending : pendingMutableSlot frame reserved = true
    · have reservedRun := reserveRawVec_incoming_projects frame parent path
      cases reservationEq : reserveRawVec frame parent path with
      | invalid world => simpa only [eval, pending, ite_true, reservationEq, Flow.world, NativeRawVecFields.Result.world] using reservedRun
      | value reservation prepared =>
        rw [reservationEq] at reservedRun
        cases argsEq : evalArgs {frame with world := prepared} rest with
        | none => simpa only [eval, pending, ite_true, reservationEq, argsEq, Flow.world, NativeRawVecFields.Result.world] using reservedRun
        | some result =>
          rcases result with ⟨values,caller⟩
          have callerWorld := evalArgs_world {frame with world := prepared} caller rest values argsEq
          have activatedRun := NativeRawVecMutBorrow.activate_incoming_projects caller.world reservation
          have activationStart : NativeIncomingReference.Preserves frame.world caller.world := by
            simpa only [callerWorld, NativeRawVecFields.Result.world] using reservedRun
          cases activated : NativeRawVecMutBorrow.activate caller.world reservation with
          | invalid world =>
            rw [activated] at activatedRun
            simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, Flow.world, NativeRawVecFields.Result.world] using
              NativeIncomingReference.runs_trans _ _ _ activationStart activatedRun
          | value reference world =>
            rw [activated] at activatedRun
            have beforeWrite : NativeIncomingReference.Preserves frame.world world :=
              NativeIncomingReference.runs_trans _ _ _ activationStart activatedRun
            cases writtenEq : write {caller with world} reserved (.scalar reference) with
            | none => simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, Flow.world] using beforeWrite
            | some written =>
              have writtenWorld := write_world {caller with world} written reserved (.scalar reference) writtenEq
              cases movedEq : evalOperand written (.move reserved []) with
              | none => simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, Flow.world] using beforeWrite
              | some moved =>
                rcases moved with ⟨argument,consumed⟩
                have consumedWorld := evalOperand_world written consumed (.move reserved []) argument movedEq
                cases initialized : initial types argCount (argument :: values) consumed.world with
                | none =>
                  have consumedRun : NativeIncomingReference.Preserves frame.world consumed.world := by
                    simpa only [consumedWorld, writtenWorld] using beforeWrite
                  simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized,
                    Flow.world] using consumedRun
                | some entered =>
                  have entryWorld := initial_world types argCount (argument :: values) consumed.world entered initialized
                  have callStart : NativeIncomingReference.Preserves frame.world entered.world := by
                    simpa only [entryWorld, consumedWorld, writtenWorld] using beforeWrite
                  have first := NativeIncomingReference.runs_trans _ _ _ callStart
                    (settle_incoming_projects entered.world (eval callee entered) (calleeIH entered))
                  cases returned : settle entered.world (eval callee entered) with
                  | normal changed => simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, Flow.world] using first
                  | invalid final => simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, Flow.world] using first
                  | unsupported source final => simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, Flow.world] using first
                  | unwind final =>
                    rw [returned] at first
                    simp only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned]
                    exact NativeIncomingReference.runs_trans _ _ _ first (unwindIH {consumed with world := final})
                  | returned output final =>
                    rw [returned] at first
                    cases stored : write {consumed with world := final} target output with
                    | none => simpa only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, stored, Flow.world] using first
                    | some changed =>
                      simp only [eval, pending, ite_true, reservationEq, argsEq, activated, writtenEq, movedEq, initialized, returned, stored]
                      have later := nextIH changed
                      rw [write_world {consumed with world := final} changed target output stored] at later
                      exact NativeIncomingReference.runs_trans _ _ _ first later
    · simp only [eval, pending, Flow.world]; exact .refl _
  | call name classification types argCount target args callee unwind next calleeIH unwindIH nextIH =>
    cases selected : evalArgs frame args with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := evalArgs_world frame caller args values selected
      cases initialized : initial types argCount values caller.world with
      | none => simp only [eval, selected, initialized, Flow.world]; rw [same]; exact .refl _
      | some entered =>
        have entryWorld := initial_world types argCount values caller.world entered initialized
        have callPrefix : NativeIncomingReference.Preserves frame.world entered.world := by
          rw [entryWorld, same]
          exact .refl _
        have first := NativeIncomingReference.runs_trans _ _ _ callPrefix
          (settle_incoming_projects entered.world (eval callee entered) (calleeIH entered))
        cases returned : settle entered.world (eval callee entered) with
        | normal changed => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | invalid world => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | unsupported source world => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | unwind world =>
          rw [returned] at first
          simp only [eval, selected, initialized, returned]
          exact NativeIncomingReference.runs_trans _ _ _ first (unwindIH {caller with world})
        | returned output world =>
          rw [returned] at first
          cases written : write {caller with world} target output with
          | none => simpa only [eval, selected, initialized, returned, written, Flow.world] using first
          | some changed =>
            have second := nextIH changed
            rw [write_world {caller with world} changed target output written] at second
            simp only [eval, selected, initialized, returned, written]
            exact NativeIncomingReference.runs_trans _ _ _ first second

theorem invoke_incoming_projects (function : Function) (world : State) (args : List Input) :
    NativeIncomingReference.Preserves world (invoke function world args).world := by
  cases decoded : decodeArgs world args with
  | none => simp only [invoke, decoded, Flow.world]; exact .refl _
  | some values =>
    cases initialized : initial function.types function.argCount values world with
    | none => simp only [invoke, decoded, initialized, Flow.world]; exact .refl _
    | some frame =>
      have same := initial_world function.types function.argCount values world frame initialized
      have evaluated := eval_incoming_projects function.body frame
      rw [same] at evaluated
      have first := settle_incoming_projects world (eval function.body frame) evaluated
      simpa only [invoke, decoded, initialized, same] using first


end FormalProof4FHE.HasteBoots.NativeRecordLLBC
