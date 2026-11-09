namespace HasteBootsVecCapacityArithmetic.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
example : eval step_checkedMultiply (checkedFrame NativeReferenceMachine.empty 1 0) =
    .normal (checkedAfter NativeReferenceMachine.empty 1 0) ∧
    NativeRecordLLBC.read (checkedAfter NativeReferenceMachine.empty 1 0) checkedDestination [] =
      some (.pair (.scalar (.usize 0)) (.pair (.boolean false) (.scalar .unit))) :=
  byte_assignment NativeReferenceMachine.empty 0
example : eval step_checkedMultiply (checkedFrame NativeReferenceMachine.empty 1 (2^64-1)) =
    .normal (checkedAfter NativeReferenceMachine.empty 1 (2^64-1)) ∧
    NativeRecordLLBC.read (checkedAfter NativeReferenceMachine.empty 1 (2^64-1)) checkedDestination [] =
      some (.pair (.scalar (.usize (2^64-1))) (.pair (.boolean false) (.scalar .unit))) :=
  byte_assignment NativeReferenceMachine.empty (2^64-1)
example : eval step_checkedMultiply (checkedFrame NativeReferenceMachine.empty (2^64-1) 2) =
    .normal (checkedAfter NativeReferenceMachine.empty (2^64-1) 2) ∧
    NativeRecordLLBC.read (checkedAfter NativeReferenceMachine.empty (2^64-1) 2) checkedDestination [] =
      some (.pair (.scalar (.usize (2^64-2))) (.pair (.boolean true) (.scalar .unit))) :=
  ⟨checked_assignment NativeReferenceMachine.empty (2^64-1) 2,by decide⟩
example : NativeRecordLLBC.read (checkedAfter NativeReferenceMachine.empty 7 9) checkedLeft [] = none ∧
    NativeRecordLLBC.read (checkedAfter NativeReferenceMachine.empty 7 9) checkedRight [] = none :=
  checked_moves_consumed NativeReferenceMachine.empty 7 9
end HasteBootsVecCapacityArithmetic.Smoke
