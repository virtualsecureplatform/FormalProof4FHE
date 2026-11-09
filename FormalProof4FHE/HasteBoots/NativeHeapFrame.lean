module
public import FormalProof4FHE.HasteBoots.NativeRecordDropCalls
@[expose] public section

/-! Heap framing for the closed read/borrow operations used by the destructor.
This is a property of the modeled heap, not a native lifetime or work theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeHeapFrame
open NativeReferenceMachine (State Op)

def readOnly : Op → Bool
  | .raw (.fromAddress _) | .raw (.withAddress _ _) | .raw (.load _) => true
  | .borrow _ _ _ | .reborrow _ _ _ _ | .endBorrow _ => true
  | .access _ _ (.read _ _) | .access _ _ .loadPointer => true
  | _ => false

theorem raw_heap (world next : NativePointerMachine.State) (op : NativePointerMachine.Op)
    (checked : readOnly (.raw op) = true) (actual : NativePointerMachine.execute world op = some next) :
    next.heap = world.heap := by
  cases op with
  | fromAddress address => cases actual; rfl
  | withAddress register address =>
    simp only [NativePointerMachine.execute, Option.map_eq_some_iff] at actual
    obtain ⟨pointer,_,same⟩ := actual
    cases same; rfl
  | load register =>
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at actual
    obtain ⟨pointer,_,value,_,same⟩ := actual
    cases same; rfl
  | allocate => cases checked
  | store => cases checked
  | writeBytes => cases checked
  | copy => cases checked
  | copyNonoverlapping => cases checked
  | free => cases checked

theorem execute_heap (world next : State) (op : Op) (checked : readOnly op = true)
    (actual : NativeReferenceMachine.execute world op = some next) : next.pointers.heap = world.pointers.heap := by
  cases op with
  | raw op =>
    simp only [NativeReferenceMachine.execute] at actual
    split at actual
    · obtain ⟨pointers,executed,same⟩ := Option.map_eq_some_iff.mp actual
      cases same
      exact raw_heap world.pointers pointers op checked executed
    · cases actual
  | borrow register mode layout =>
    simp only [NativeReferenceMachine.execute, Option.bind_eq_some_iff] at actual
    obtain ⟨pointer,_,granted⟩ := actual
    obtain ⟨_,_,_,same,_⟩ := NativeReferenceMachine.grant_success world next none mode pointer layout granted
    exact congrArg NativePointerMachine.State.heap same
  | reborrow parent register mode layout =>
    simp only [NativeReferenceMachine.execute, Option.bind_eq_some_iff] at actual
    obtain ⟨reference,_,pointer,_,granted⟩ := actual
    obtain ⟨_,_,_,same,_⟩ := NativeReferenceMachine.grant_success world next (some reference.tag) mode pointer layout granted
    exact congrArg NativePointerMachine.State.heap same
  | endBorrow index =>
    simp only [NativeReferenceMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at actual
    obtain ⟨reference,_,ledger,_,same⟩ := actual
    cases same; rfl
  | access index offset action =>
    obtain ⟨_,lease,pointer,prepared,_,_,_,_,_,_,preparation,performed⟩ := NativeReferenceMachine.access_success world next index offset action actual
    have preparedHeap : prepared.heap = world.pointers.heap := by
      rw [(NativeReferenceMachine.prepare_success world lease.pointer pointer.address prepared preparation).2]
      rfl
    cases action with
    | read size alignment =>
      simp only [NativeReferenceMachine.perform, Option.map_eq_some_iff] at performed
      obtain ⟨bytes,_,same⟩ := performed
      cases same; exact preparedHeap
    | loadPointer =>
      obtain ⟨pointers,loaded,same⟩ := Option.map_eq_some_iff.mp performed
      cases same
      exact (raw_heap prepared pointers (.load 0) rfl loaded).trans preparedHeap
    | writeBytes => cases checked
    | storePointer => cases checked

/-- A heap-framing proposition. Operational execution is supplied separately
by the original reference-machine projection theorems. -/
structure Runs (before after : State) : Prop where
  heap_eq : after.pointers.heap = before.pointers.heap

theorem Runs.refl (world : State) : Runs world world := ⟨rfl⟩

theorem Runs.step {start world next : State} (first : Runs start world) (op : Op)
    (actual : NativeReferenceMachine.execute world op = some next) (checked : readOnly op = true := by rfl) :
    Runs start next := ⟨(execute_heap world next op checked actual).trans first.heap_eq⟩

theorem runs_trans (before middle after : State) (first : Runs before middle) (second : Runs middle after) :
    Runs before after := ⟨second.heap_eq.trans first.heap_eq⟩

end FormalProof4FHE.HasteBoots.NativeHeapFrame

namespace FormalProof4FHE.HasteBoots.NativeSliceLLBC
open NativeReferenceMachine (State)

theorem issue_heap_projects (world next : State) (mutable : Bool) (input output : Value) {element : Element}
    (issued : issue world mutable input element = some (output,next)) : NativeHeapFrame.Runs world next := by
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
        exact NativeHeapFrame.Runs.step (.refl world) _ actual
      · cases issued
  | reference parent reference length =>
    simp only [issue, Option.bind_eq_some_iff] at issued
    obtain ⟨lease,_,issued⟩ := issued
    split at issued
    · obtain ⟨final,actual,same⟩ := Option.map_eq_some_iff.mp issued
      cases same
      exact NativeHeapFrame.Runs.step (.refl world) _ actual
    · cases issued

end FormalProof4FHE.HasteBoots.NativeSliceLLBC

namespace FormalProof4FHE.HasteBoots.NativeSliceLLBC
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeReferenceMachine (State Reference)
theorem retagValue_heap_projects (frame next : Frame) (input output : Value) (enabled : Bool) (element : Element)
    (tagged : retagValue frame input enabled element = some (output, next)) :
    NativeHeapFrame.Runs frame.world next.world := by
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
      exact issue_heap_projects _ _ _ _ _ actual


end FormalProof4FHE.HasteBoots.NativeSliceLLBC

namespace FormalProof4FHE.HasteBoots.NativeRawVecFields
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
theorem capacityAccess_heap_projects (world : State) (index : Nat) :
    NativeHeapFrame.Runs world (capacityAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => simp only [capacityAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeHeapFrame.Runs.step (.refl world) _ actual
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simpa only [capacityAccess, actual, decoded, Result.world] using first
    | some value =>
      simp only [capacityAccess, actual, decoded]
      split <;> exact first


theorem pointerAccess_heap_projects (world : State) (index : Nat) :
    NativeHeapFrame.Runs world (pointerAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => simp only [pointerAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeHeapFrame.Runs.step (.refl world) _ actual
    cases found : next.pointers.registers[0]? with
    | none => simpa only [pointerAccess, actual, found, Result.world] using first
    | some value =>
      simp only [pointerAccess, actual, found]
      split <;> exact first


theorem markerAccess_heap_projects (world : State) (index : Nat) :
    NativeHeapFrame.Runs world (markerAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 16 (.read 0 1)) with
  | none => simp only [markerAccess, actual, Result.world]; exact .refl _
  | some next =>
    simpa only [markerAccess, actual, Result.world] using NativeHeapFrame.Runs.step (.refl world) _ actual


end FormalProof4FHE.HasteBoots.NativeRawVecFields

namespace FormalProof4FHE.HasteBoots.NativeRawVecReference
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)
open NativeRawVecFields (Result)
theorem eval_heap_projects (world : State) (value : Value) (action : Action) :
    NativeHeapFrame.Runs world (eval world value action).world := by
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
            have first := NativeRawVecFields.capacityAccess_heap_projects world index
            cases loaded : NativeRawVecFields.capacityAccess world index <;> simpa only [loaded, Result.world] using first
          | marker =>
            have first := NativeRawVecFields.markerAccess_heap_projects world index
            cases loaded : NativeRawVecFields.markerAccess world index <;> simpa only [loaded, Result.world] using first
          | pointer =>
            have first := NativeRawVecFields.pointerAccess_heap_projects world index
            cases loaded : NativeRawVecFields.pointerAccess world index <;> simpa only [loaded, Result.world] using first


end FormalProof4FHE.HasteBoots.NativeRawVecReference

namespace FormalProof4FHE.HasteBoots.NativeRawVecBorrow
open NativeReferenceMachine (State Reference)
open NativeRawVecFields (Result)
open NativeSliceLLBC (Value)
theorem reborrow_heap_projects (world : State) (value : Value) (target : Target) :
    NativeHeapFrame.Runs world (reborrow world value target).world := by
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
        have first := NativeHeapFrame.Runs.step (.refl world) _ preparedEq
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) with
        | none => simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using first
        | some next =>
          have later := NativeHeapFrame.Runs.step (.refl prepared) _ issued
          simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using
            NativeHeapFrame.runs_trans _ _ _ first later


end FormalProof4FHE.HasteBoots.NativeRawVecBorrow

namespace FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow
open NativeReferenceMachine (State Reference)
open NativeSliceLLBC (Value)
open NativeRawVecFields (Result)
theorem reserve_heap_projects (world : State) (value : Value) :
    NativeHeapFrame.Runs world (reserve world value).world := by
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
          have first := NativeHeapFrame.Runs.step (.refl world) _ actual
          simp only [reserve, selected, actual]
          split <;> exact first


theorem activate_heap_projects (world : State) (reservation : Reservation) :
    NativeHeapFrame.Runs world (activate world reservation).world := by
  simp only [activate]
  split
  · cases actual : NativeReferenceMachine.execute world (.reborrow
        (world.references.idxOf reservation.parent) (world.pointers.registers.idxOf reservation.pointer) .exclusive ⟨16,8⟩) with
    | none => exact .refl _
    | some next => exact NativeHeapFrame.Runs.step (.refl world) _ actual
  · exact .refl _


theorem immediate_heap_projects (world : State) (value : Value) :
    NativeHeapFrame.Runs world (immediate world value).world := by
  have first := reserve_heap_projects world value
  cases actual : reserve world value with
  | invalid next => simpa only [immediate, actual, Result.world] using first
  | value reservation next =>
    rw [actual] at first
    simpa only [immediate, actual, Result.world] using
      NativeHeapFrame.runs_trans _ _ _ first (activate_heap_projects next reservation)


end FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow

namespace FormalProof4FHE.HasteBoots.NativeVecReference
open NativeReferenceMachine (State Reference)
open NativeRawVecFields (Result)
open NativeSliceLLBC (Value)
theorem reborrow_heap_projects (world : State) (value : Value) (target : Target) :
    NativeHeapFrame.Runs world (reborrow world value target).world := by
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
        have first := NativeHeapFrame.Runs.step (.refl world) _ preparedEq
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) with
        | none => simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using first
        | some next =>
          have later := NativeHeapFrame.Runs.step (.refl prepared) _ issued
          simpa only [reborrow, selected, shifted, preparedEq, issued, Result.world] using
            NativeHeapFrame.runs_trans _ _ _ first later


theorem lengthAccess_heap_projects (world : State) (index : Nat) :
    NativeHeapFrame.Runs world (lengthAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 16 (.read 8 8)) with
  | none => simp only [lengthAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeHeapFrame.Runs.step (.refl world) _ actual
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode <;>
      simpa only [lengthAccess, actual, decoded, Result.world] using first


theorem readField_heap_projects (world : State) (value : Value) (action : Action) :
    NativeHeapFrame.Runs world (readField world value action).world := by
  cases selected : parent world value with
  | none => simp only [readField, selected, Result.world]; exact .refl _
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases action with
    | pointer =>
      have first := NativeRawVecFields.pointerAccess_heap_projects world index
      cases actual : NativeRawVecFields.pointerAccess world index <;>
        simpa only [readField, selected, actual, Result.world] using first
    | length =>
      have first := lengthAccess_heap_projects world index
      cases actual : lengthAccess world index <;>
        simpa only [readField, selected, actual, Result.world] using first


theorem eval_heap_projects (world : State) (value : Value) (operation : Operation) :
    NativeHeapFrame.Runs world (eval world value operation).world := by
  cases operation with
  | borrow target => exact reborrow_heap_projects world value target
  | field action => exact readField_heap_projects world value action


end FormalProof4FHE.HasteBoots.NativeVecReference

namespace FormalProof4FHE.HasteBoots.NativeRecordLLBC
open NativeRecordValues (Ty Value Path)
open NativeReferenceMachine (State)
open NativeSliceLLBC (Element)
open NativeWord64Memory (Word)
open NativeByteDropCalls (Classification)
theorem retag_heap_projects (world : State) (value : Value) (enabled : Bool) (element : Element) :
    NativeHeapFrame.Runs world (retag world value enabled element).world := by
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
          NativeSliceLLBC.retagValue_heap_projects ⟨[],[],world⟩ frame value output true element actual
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
          exact NativeHeapFrame.runs_trans _ _ _ first second
        | value output final =>
          rw [secondEq] at second
          simp only [retag, firstEq, secondEq, Tagged.world]
          exact NativeHeapFrame.runs_trans _ _ _ first second
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


theorem evalRawVecField_heap_projects (frame : Frame) (operand : Operand) (action : NativeRawVecReference.Action) (enabled : Bool) :
    NativeHeapFrame.Runs frame.world (evalRawVecField frame operand action enabled).world := by
  cases selected : evalOperand frame operand with
  | none => simp only [evalRawVecField, selected, Evaluated.world]; exact .refl _
  | some result =>
    rcases result with ⟨value,caller⟩
    have same := evalOperand_world frame caller operand value selected
    cases value with
    | scalar value =>
      have first := NativeRawVecReference.eval_heap_projects caller.world value action
      cases actual : NativeRawVecReference.eval caller.world value action with
      | invalid rejected =>
        rw [actual] at first
        simp only [evalRawVecField, selected, actual, Evaluated.world]
        simpa only [NativeRawVecFields.Result.world, same] using first
      | value output next =>
        rw [actual] at first
        have readPrefix : NativeHeapFrame.Runs frame.world next := by
          simpa only [NativeRawVecFields.Result.world, same] using first
        have second := retag_heap_projects next (.scalar output) enabled .word
        cases tagged : retag next (.scalar output) enabled .word with
        | invalid final =>
          rw [tagged] at second
          simp only [evalRawVecField, selected, actual, tagged, Evaluated.world]
          exact NativeHeapFrame.runs_trans _ _ _ readPrefix second
        | value result final =>
          rw [tagged] at second
          simp only [evalRawVecField, selected, actual, tagged, Evaluated.world]
          exact NativeHeapFrame.runs_trans _ _ _ readPrefix second
    | choice side fields => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | pair left right => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | record tag fields => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | enumeration tag value => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | boolean value => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | uninit => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _


theorem evalRawVecBorrow_heap_projects (frame : Frame) (index : Nat) (path : Path) (target : NativeRawVecBorrow.Target) :
    NativeHeapFrame.Runs frame.world (evalRawVecBorrow frame index path target).world := by
  cases selected : read frame index path with
  | none => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value =>
      have first := NativeRawVecBorrow.reborrow_heap_projects frame.world value target
      cases actual : NativeRawVecBorrow.reborrow frame.world value target <;>
        simpa only [evalRawVecBorrow, selected, actual, Evaluated.world, NativeRawVecFields.Result.world] using first
    | choice side fields => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | pair left right => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | record tag fields => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | enumeration tag value => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | boolean value => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _
    | uninit => simp only [evalRawVecBorrow, selected, Evaluated.world]; exact .refl _


theorem reserveRawVec_heap_projects (frame : Frame) (index : Nat) (path : Path) :
    NativeHeapFrame.Runs frame.world (reserveRawVec frame index path).world := by
  cases selected : read frame index path with
  | none => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value => simpa only [reserveRawVec, selected] using NativeRawVecMutBorrow.reserve_heap_projects frame.world value
    | choice side fields => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | pair left right => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | record tag fields => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | enumeration tag value => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | boolean value => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _
    | uninit => simp only [reserveRawVec, selected, NativeRawVecFields.Result.world]; exact .refl _


theorem evalRawVecMutBorrow_heap_projects (frame : Frame) (index : Nat) (path : Path) :
    NativeHeapFrame.Runs frame.world (evalRawVecMutBorrow frame index path).world := by
  have first := reserveRawVec_heap_projects frame index path
  cases selected : reserveRawVec frame index path with
  | invalid next => simpa only [evalRawVecMutBorrow, selected, Evaluated.world, NativeRawVecFields.Result.world] using first
  | value reservation prepared =>
    rw [selected] at first
    have second := NativeRawVecMutBorrow.activate_heap_projects prepared reservation
    cases actual : NativeRawVecMutBorrow.activate prepared reservation <;>
      simpa only [evalRawVecMutBorrow, selected, actual, Evaluated.world, NativeRawVecFields.Result.world] using
        NativeHeapFrame.runs_trans _ _ _ first second


theorem evalVec_heap_projects (frame : Frame) (index : Nat) (path : Path) (operation : NativeVecReference.Operation) :
    NativeHeapFrame.Runs frame.world (evalVec frame index path operation).world := by
  cases selected : read frame index path with
  | none => simp only [evalVec, selected, Evaluated.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value =>
      have first := NativeVecReference.eval_heap_projects frame.world value operation
      cases actual : NativeVecReference.eval frame.world value operation <;>
        simpa only [evalVec, selected, actual, Evaluated.world, NativeRawVecFields.Result.world] using first
    | choice side fields => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | pair left right => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | record tag fields => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | enumeration tag value => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | boolean value => simp only [evalVec, selected, Evaluated.world]; exact .refl _
    | uninit => simp only [evalVec, selected, Evaluated.world]; exact .refl _


theorem evalBorrowSlice_heap_projects (frame : Frame) (index : Nat) (path : Path) :
    NativeHeapFrame.Runs frame.world (evalBorrowSlice frame index path).world := by
  cases selected : read frame index path with
  | none => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
  | some value =>
    cases value with
    | scalar value =>
      cases issued : NativeSliceLLBC.issue frame.world true value .byte with
      | none => simp only [evalBorrowSlice, selected, issued, Evaluated.world]; exact .refl _
      | some pair =>
        rcases pair with ⟨output,next⟩
        simpa only [evalBorrowSlice, selected, issued, Evaluated.world] using NativeSliceLLBC.issue_heap_projects frame.world next true value output issued
    | choice side fields => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | pair left right => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | record tag fields => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | enumeration tag word => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | boolean value => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _
    | uninit => simp only [evalBorrowSlice, selected, Evaluated.world]; exact .refl _


theorem evalZstBorrow_heap_projects (frame : Frame) (index tag : Nat) (address : NativeWord64Memory.Word) :
    NativeHeapFrame.Runs frame.world (evalZstBorrow frame index tag address).world := by
  unfold evalZstBorrow
  split
  · have first : NativeHeapFrame.Runs frame.world (NativeZstBorrow.issue frame.world address).world :=
      ⟨NativeZstBorrow.issue_heap frame.world address⟩
    cases actual : NativeZstBorrow.issue frame.world address <;>
      simpa only [actual,Evaluated.world,NativeRawVecFields.Result.world] using first
  · exact .refl _

theorem evalZstMutBorrow_heap_projects (frame : Frame) (index tag : Nat) (address : NativeWord64Memory.Word) :
    NativeHeapFrame.Runs frame.world (evalZstMutBorrow frame index tag address).world := by
  unfold evalZstMutBorrow
  split
  · have first : NativeHeapFrame.Runs frame.world (NativeZstBorrow.issueExclusive frame.world address).world :=
      ⟨NativeZstBorrow.issue_exclusive_heap frame.world address⟩
    cases actual : NativeZstBorrow.issueExclusive frame.world address <;>
      simpa only [actual,Evaluated.world,NativeRawVecFields.Result.world] using first
  · exact .refl _

theorem evalRvalue_heap_projects (frame : Frame) (rvalue : Rvalue) :
    NativeHeapFrame.Runs frame.world (evalRvalue frame rvalue).world := by
  induction rvalue with
  | arithmetic operation args =>
    change NativeHeapFrame.Runs frame.world (evalArithmetic frame operation args).world
    rw [evalArithmetic_world]; exact .refl _
  | vec operation index path => exact evalVec_heap_projects frame index path operation
  | borrowSlice index path => exact evalBorrowSlice_heap_projects frame index path
  | parts data length =>
    change NativeHeapFrame.Runs frame.world (evalParts frame data length).world
    rw [evalParts_world]; exact .refl _
  | unit => exact .refl _
  | borrowRawVecMut index path => exact evalRawVecMutBorrow_heap_projects frame index path
  | borrowZstLocal index tag address => exact evalZstBorrow_heap_projects frame index tag address
  | borrowZstMutLocal index tag address => exact evalZstMutBorrow_heap_projects frame index tag address
  | borrowRawVec target index path => exact evalRawVecBorrow_heap_projects frame index path target
  | mulUsizeUB left right =>
    change NativeHeapFrame.Runs frame.world (evalMultiply frame left right).world
    rw [evalMultiply_world]; exact .refl _
  | enumAddress operand enumTag recordTag =>
    change NativeHeapFrame.Runs frame.world (evalEnumAddress frame operand enumTag recordTag).world
    rw [evalEnumAddress_world]; exact .refl _
  | enumWord operand tag =>
    change NativeHeapFrame.Runs frame.world (evalEnumWord frame operand tag).world
    rw [evalEnumWord_world]; exact .refl _
  | recordResult tag singleton inner ih =>
    cases selected : evalRvalue frame inner with
    | invalid world => simpa only [evalRvalue, selected, Evaluated.world] using ih
    | value value caller =>
      cases actual : recordResultValue tag singleton value <;>
        simpa only [evalRvalue, selected, actual, Evaluated.world] using ih
  | rawVecField action operand enabled => exact evalRawVecField_heap_projects frame operand action enabled
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
      have first := retag_heap_projects caller.world value enabled element
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
    change NativeHeapFrame.Runs frame.world (evalKnownDiscriminant frame index descriptor).world
    rw [evalKnownDiscriminant_world]; exact .refl _
  | rawThin operand =>
    change NativeHeapFrame.Runs frame.world (evalRawThin frame operand).world
    rw [evalRawThin_world]; exact .refl _
  | rawAddress operand =>
    change NativeHeapFrame.Runs frame.world (evalRawAddress frame operand).world
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
      · change NativeHeapFrame.Runs frame.world caller.world
        rw [same]; exact .refl _
      · change NativeHeapFrame.Runs frame.world caller.world
        rw [same]; exact .refl _



end FormalProof4FHE.HasteBoots.NativeRecordLLBC

namespace FormalProof4FHE.HasteBoots.NativeReferenceCleanup
open NativeReferenceMachine (State)
theorem closeScope_heap_projects (entered world : State) : NativeHeapFrame.Runs world (closeScope entered world).world := by
  refine ⟨?_⟩
  exact congrArg (fun state => state.pointers.heap) (release_frame world (scopeTags entered world))
end FormalProof4FHE.HasteBoots.NativeReferenceCleanup

namespace FormalProof4FHE.HasteBoots.NativeReferenceCleanup
open NativeReferenceMachine (State)
theorem settleUnit_heap_projects (entered : State) (flow : NativeSliceLLBC.Flow) :
    NativeHeapFrame.Runs flow.world (settleUnit entered flow).world := by
  cases flow with
  | returned value current =>
    cases value with
    | unit =>
      change NativeHeapFrame.Runs current
        (if (closeScope entered current).pending.isEmpty then
          NativeSliceLLBC.Flow.returned .unit (closeScope entered current).world
        else .invalid (closeScope entered current).world).world
      split <;> exact closeScope_heap_projects entered current
    | usize word => exact .refl _
    | raw pointer => exact .refl _
    | reference mutable reference length => exact .refl _
  | continued frame => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _

end FormalProof4FHE.HasteBoots.NativeReferenceCleanup

namespace FormalProof4FHE.HasteBoots.NativeRecordLLBC
open NativeReferenceMachine (State)
theorem settle_heap_projects (entered : State) (flow : Flow) :
    NativeHeapFrame.Runs flow.world (settle entered flow).world := by
  cases flow with
  | normal frame => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | returned value world =>
    cases value with
    | pair left right => exact .refl _
    | choice side fields => exact .refl _
    | record tag fields => exact .refl _
    | enumeration tag value => exact .refl _
    | boolean value => exact .refl _
    | uninit => exact .refl _
    | scalar value =>
      cases value with
      | usize value => exact .refl _
      | raw pointer => exact .refl _
      | reference mutable reference length => exact .refl _
      | unit =>
        have first := NativeReferenceCleanup.settleUnit_heap_projects entered (.returned .unit world)
        cases actual : NativeReferenceCleanup.settleUnit entered (.returned .unit world) with
        | returned value final =>
          cases value <;> simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | continued frame => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | unwind final => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | invalid final => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | unsupported source final => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first

end FormalProof4FHE.HasteBoots.NativeRecordLLBC
