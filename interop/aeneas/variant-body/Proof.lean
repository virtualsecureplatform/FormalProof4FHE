namespace HasteBootsVariantBody
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

def noneValue : NativeRecordValues.Value := .record 4 (.choice false (.scalar .unit))
def layoutValue (size alignment : NativeWord64Memory.Word) : NativeRecordValues.Value :=
  .record 3 (.pair (.scalar (.usize size)) (.pair
    (.record 6 (.pair (.enumeration 9 alignment) (.scalar .unit))) (.scalar .unit)))
def pointerValue (pointer : NativeSliceLLBC.Raw) : NativeRecordValues.Value :=
  .record 2 (.pair (.scalar (.raw pointer)) (.scalar .unit))
def someValue (pointer : NativeSliceLLBC.Raw) (size alignment : NativeWord64Memory.Word) : NativeRecordValues.Value :=
  .record 4 (.choice true (.pair (.pair (pointerValue pointer)
    (.pair (layoutValue size alignment) (.scalar .unit))) (.scalar .unit)))

theorem absent_exact (world : NativeReferenceMachine.State) :
    invoke f2 world [] = .returned noneValue world := by
  simp [invoke, f2, decodeArgs, initial, eval, evalRvalue, evalArgs, storageLive,
    write, NativeRecordLLBC.read, NativeRecordValues.fits, NativeRecordValues.complete,
    NativeRecordValues.compatible, NativeRecordValues.get, NativeRecordValues.typeAt,
    NativeSliceLLBC.fits, settle, noneValue]

theorem present_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f1.body frame).world := eval_projects f1.body frame

theorem selected_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f3.body frame).world := eval_projects f3.body frame

end HasteBootsVariantBody
