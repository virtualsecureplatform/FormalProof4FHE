namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- The actual retained checked multiplication assignment consumes its two
source moves and writes its typed result, for every word pair and world. -/
theorem checked_assignment (world : NativeReferenceMachine.State) (left right : NativeWord64Memory.Word) :
    eval step_checkedMultiply (checkedFrame world left right) = .normal (checkedAfter world left right) := by
  simp [step_checkedMultiply,expr_checkedMultiply,checkedFrame,checkedAfter,eval,evalRvalue,evalArithmetic,evalArgs,evalOperand,
    NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeSliceLLBC.fits,NativeRecordArithmetic.eval]

/-- Byte element size one cannot overflow the retained U64 multiplication. -/
theorem byte_assignment (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) :
    eval step_checkedMultiply (checkedFrame world 1 capacity) = .normal (checkedAfter world 1 capacity) ∧
      NativeRecordLLBC.read (checkedAfter world 1 capacity) checkedDestination [] =
        some (.pair (.scalar (.usize capacity)) (.pair (.boolean false) (.scalar .unit))) := by
  refine ⟨checked_assignment world 1 capacity,?_⟩
  have encoded : NativeRecordArithmetic.word capacity.val = capacity := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt capacity.isLt
  simp [checkedAfter,checkedDestination,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,encoded]

/-- The two original moved operands cannot be read after the assignment. -/
theorem checked_moves_consumed (world : NativeReferenceMachine.State) (left right : NativeWord64Memory.Word) :
    NativeRecordLLBC.read (checkedAfter world left right) checkedLeft [] = none ∧
      NativeRecordLLBC.read (checkedAfter world left right) checkedRight [] = none := by
  simp [checkedAfter,checkedLeft,checkedRight,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.complete]

theorem checked_world_preserved (world : NativeReferenceMachine.State) (left right : NativeWord64Memory.Word) :
    (eval step_checkedMultiply (checkedFrame world left right)).world = world := by
  rw [checked_assignment]
  rfl
end HasteBootsVecCapacityArithmetic
