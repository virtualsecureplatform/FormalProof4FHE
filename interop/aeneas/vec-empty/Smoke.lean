namespace HasteBootsVecEmpty.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
private def populated : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 64 ⟨8,1⟩)]).getD NativeReferenceMachine.empty
example : invoke f0 populated [] = .returned emptyValue populated := empty_invocation populated
example (value : NativeRecordValues.Value) (final : NativeReferenceMachine.State)
    (returned : invoke f0 populated [] = .returned value final) :
    final = populated ∧ NativeRecordValues.get value capacityPath = some (.scalar (.usize 0)) ∧
      NativeRecordValues.get value pointerPath = some (.scalar (.raw ⟨⟨1,none⟩,none⟩)) ∧
      NativeRecordValues.get value lengthPath = some (.scalar (.usize 0)) := returned_fields populated final value returned
-- A live allocation at the same numerical address cannot give the dangling value an origin.
private def atOne : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 1 ⟨8,1⟩)]).getD NativeReferenceMachine.empty
example : atOne.pointers.heap.memory.blocks.length = 1 ∧
    NativeByteRange.loadRange atOne.pointers.heap.memory ⟨1,none⟩ ⟨1,1⟩ = none :=
  ⟨by decide,empty_pointer_unreadable atOne ⟨1,1⟩ (by decide)⟩
example : invoke f1 NativeReferenceMachine.empty [] = .returned emptyValue NativeReferenceMachine.empty := by
  simp only [NativeRecordCallValues.invoke_eq,decodeArgs,constructor_exact]
end HasteBootsVecEmpty.Smoke
