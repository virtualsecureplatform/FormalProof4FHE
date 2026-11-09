namespace HasteBootsRawVecCurrentMemory
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

def layoutInput (size alignment : NativeWord64Memory.Word) : Input :=
  .record 9 (.pair (.scalar (.usize size)) (.pair
    (.record 11 (.pair (.enumeration 12 alignment) .unit)) .unit))
def layoutValue (size alignment : NativeWord64Memory.Word) : NativeRecordValues.Value :=
  .record 9 (.pair (.scalar (.usize size)) (.pair
    (.record 11 (.pair (.enumeration 12 alignment) (.scalar .unit))) (.scalar .unit)))
def noneValue : NativeRecordValues.Value := .record 10 (.choice false (.scalar .unit))
def someValue (pointer : NativePointerStorage.Pointer) (size alignment : NativeWord64Memory.Word) : NativeRecordValues.Value :=
  .record 10 (.choice true (.pair (.pair
    (.record 7 (.pair (.scalar (.raw ⟨pointer,none⟩)) (.scalar .unit)))
    (.pair (layoutValue size alignment) (.scalar .unit))) (.scalar .unit)))

theorem body_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f8.body frame).world := eval_projects f8.body frame

theorem invocation_projects (world : NativeReferenceMachine.State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke f8 world args).world := invoke_projects f8 world args

theorem zero_element_exact (world : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference)
    (decoded : NativeRawVecReference.decode world index .inner = some (.reference false reference 2)) :
    invoke f8 world [.rawVecSharedReference index,layoutInput 0 1] = .returned noneValue world := by
  simp [invoke, f8, decodeArgs, decode, decoded, initial, layoutInput, eval, evalRvalue,
    evalOperand, evalArgs, storageLive, storageDead, write, NativeRecordLLBC.read,
    NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
    NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
    NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
    alignmentDiscriminants, settle, noneValue]

theorem zero_capacity_exact (world next : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference)
    (decoded : NativeRawVecReference.decode world index .inner = some (.reference false reference 2))
    (loaded : NativeRawVecReference.eval world (.reference false reference 2) .capacity = .value (.usize 0) next) :
    invoke f8 world [.rawVecSharedReference index,layoutInput 1 1] = .returned noneValue next := by
  simp [invoke, f8, decodeArgs, decode, decoded, initial, layoutInput, eval, evalRvalue,
    evalRawVecField, evalOperand, evalArgs, storageLive, storageDead, write, NativeRecordLLBC.read,
    NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
    NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
    NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
    alignmentDiscriminants, loaded, settle, noneValue]

end HasteBootsRawVecCurrentMemory
