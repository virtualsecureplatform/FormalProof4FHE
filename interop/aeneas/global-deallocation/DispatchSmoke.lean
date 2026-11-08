namespace HasteBootsGlobalDeallocationDispatchSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC HasteBootsGlobalDeallocation
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.fromAddress ⟨1,by decide⟩),.borrow 0 .shared ⟨0,1⟩,
     .raw (.allocate ⟨64,by decide⟩ ⟨1,1⟩),.raw (.writeBytes 0 1 [0])]).getD NativeReferenceMachine.empty

-- The gate changes only the retained switch label from zero to one. Its
-- one-byte input must then take the skip branch and retain its allocation.
example : invoke f1 ready
    [.zstSharedReference 0,.record 0 (.pair (.scalar (.rawRegister 0)) .unit),
      .record 1 (.pair (.scalar (.usize ⟨1,by decide⟩))
        (.pair (.record 3 (.pair (.enumeration 4 ⟨1,by decide⟩) .unit)) .unit))] =
    .returned (.scalar .unit) ready := by decide
end HasteBootsGlobalDeallocationDispatchSmoke
