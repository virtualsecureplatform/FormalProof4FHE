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
private def headerWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 128 ⟨24,8⟩)]).getD NativeReferenceMachine.empty
private theorem headerReachable : NativeReferenceMachine.Reachable headerWorld :=
  NativeReferenceMachine.run_reachable _ _ .empty [.raw (.allocate 128 ⟨24,8⟩)] (by decide)
example : ∃ next, ∃ ready : NativeEmptyVecStorage.Ready next,
    constructStored headerWorld 0 = some next ∧ NativeReferenceMachine.Reachable next ∧
    next.pointers.registers = headerWorld.pointers.registers ∧ next.leases = ready.descriptor.lease :: headerWorld.leases ∧
    next.references = ⟨headerWorld.nextTag⟩ :: headerWorld.references ∧ ready.descriptor.reference = ⟨headerWorld.nextTag⟩ :=
  constructStored_complete headerWorld 0 ⟨128,some ⟨128,0⟩⟩ headerReachable (by decide) (by decide) (by
    intro lease member
    cases member)
private def storedWorld : NativeReferenceMachine.State := (constructStored headerWorld 0).getD NativeReferenceMachine.empty
example : constructStored storedWorld 0 = none := by
  simp only [constructStored,empty_invocation,empty_fields.1,empty_fields.2.1,empty_fields.2.2,and_self,ite_true]
  decide
end HasteBootsVecEmpty.Smoke
