namespace HasteBootsRawVecReference
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem usize_retag (world : NativeReferenceMachine.State) (value : NativeWord64Memory.Word)
    (enabled : Bool) (element : NativeSliceLLBC.Element) :
    retag world (.scalar (.usize value)) enabled element = .value (.scalar (.usize value)) world := by
  cases enabled <;> rfl

theorem body_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval capacity.body frame).world := eval_projects capacity.body frame

theorem invocation_of_read (world next : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference) (value : NativeWord64Memory.Word)
    (decoded : NativeRawVecReference.decode world index .vector = some (.reference false reference 3))
    (loaded : NativeRawVecReference.eval world (.reference false reference 3) .capacity = .value (.usize value) next) :
    invoke capacity world [.vectorSharedReference index] = .returned (.scalar (.usize value)) next := by
  simp [invoke, capacity, decodeArgs, decode, decoded, initial, eval, evalRvalue,
    evalRawVecField, evalOperand, storageLive, storageDead, write,
    NativeRecordLLBC.read, NativeRecordValues.fits, NativeRecordValues.complete,
    NativeRecordValues.compatible, NativeRecordValues.typeAt, NativeRecordValues.get,
    NativeRecordValues.copyable, NativeSliceLLBC.fits, usize_retag,
    loaded, settle]

theorem invocation_of_failed_read (world next : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference)
    (decoded : NativeRawVecReference.decode world index .vector = some (.reference false reference 3))
    (failed : NativeRawVecReference.eval world (.reference false reference 3) .capacity = .invalid next) :
    invoke capacity world [.vectorSharedReference index] = .invalid next := by
  simp [invoke, capacity, decodeArgs, decode, decoded, initial, eval, evalRvalue,
    evalRawVecField, evalOperand, storageLive, NativeRecordLLBC.read,
    NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
    NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
    NativeSliceLLBC.fits, failed, settle]

end HasteBootsRawVecReference
