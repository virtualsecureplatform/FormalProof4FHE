namespace HasteBootsAllocatorCallerGuardSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC HasteBootsAllocatorCaller
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨8,8⟩),.raw (.writeBytes 0 8 (List.replicate 8 0))]).getD NativeReferenceMachine.empty

-- For the gate's changed true guard, execution reaches the retained foreign
-- declaration and stops with its explicit unsupported result before freeing.
example : invoke f2 ready
    [.scalar (.rawRegister 0),.record 0 (.pair (.scalar (.usize ⟨8,by decide⟩))
      (.pair (.record 1 (.pair (.enumeration 4 ⟨8,by decide⟩) .unit)) .unit))] =
    .unsupported f3.name ready := by decide
end HasteBootsAllocatorCallerGuardSmoke
