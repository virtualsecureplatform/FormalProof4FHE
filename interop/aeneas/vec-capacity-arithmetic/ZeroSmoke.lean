namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (world : NativeReferenceMachine.State) :
    eval (layoutPrefix (.unsupported "overflow")
        (capacityDispatch zeroSizeBody (.unsupported "positive") .done) (.unsupported "rejected") .abort)
      (layoutFrame ⟨[],[.dead,.dead,.dead,.live (some allocatorValue)],world⟩ 0) =
      .returned zeroResultValue world := zero_capacity_return _ rfl _ _ _ _

example : NativeRecordValues.get zeroResultValue
    [(.unwrap 8),(.active false),.left,(.unwrap 3),.left,(.unwrap 6),.left,(.unwrap 13),.left] =
    some (.scalar (.raw ⟨⟨1,none⟩,none⟩)) := by decide

example : NativeRecordValues.get zeroResultValue
    [(.unwrap 8),(.active false),.left,(.unwrap 3),.right,.left,(.unwrap 7),.left] =
    some (.scalar (.usize 0)) := by decide

example : NativeRecordValues.get zeroResultValue
    [(.unwrap 8),(.active false),.left,(.unwrap 3),.right,.right,.left] = some allocatorValue := by decide

example (world : NativeReferenceMachine.State) :
    eval zeroSizeBody (layoutAcceptedFrame ⟨[],[],world⟩ 0) = .invalid world := by
  simp [zeroSizeBody,eval,storageDead,storageLive,layoutAcceptedFrame,layoutTypes,evalRvalue,evalOperand,
    NativeRecordLLBC.read,NativeRecordValues.typeAt]
end HasteBootsVecCapacityArithmetic
