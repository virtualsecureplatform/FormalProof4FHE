namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeRecordLLBC (Flow)

-- Only the resident header is allocated; its empty data pointer has no origin.
private def emptyReady : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .raw (.fromAddress 1),.raw (.withAddress 1 136),.raw (.store 0 1),
     .raw (.withAddress 2 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .borrow 3 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
example : emptyReady.nextTag = 1 ∧ emptyReady.pointers.heap.memory.blocks.length = 1 := by decide
example : ∃ flow, Invokes f1 emptyReady [.vectorExclusiveReference 0] flow ∧
    (match flow with | .returned (.scalar .unit) _ => true | _ => false) = true ∧
    flow.world.pointers.heap = emptyReady.pointers.heap ∧ flow.world.nextTag = 8 ∧
    flow.world.leases.map NativeByteBorrow.Lease.tag = [0] := by
  econstructor
  constructor
  · apply Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_drop
  · decide

-- Reserved capacity need not contain initialized elements when length is zero.
private def reservedReady : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),.borrow 2 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
example : NativeByteRange.loadRange reservedReady.pointers.heap.memory ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = none := by decide
example : ∃ flow, Invokes f1 reservedReady [.vectorExclusiveReference 0] flow ∧
    (match flow with | .returned (.scalar .unit) _ => true | _ => false) = true ∧
    flow.world.pointers.heap.memory.blocks.length = 1 ∧ flow.world.nextTag = 9 ∧
    flow.world.leases.map NativeByteBorrow.Lease.tag = [0] := by
  econstructor
  constructor
  · apply Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_drop
  · decide

end HasteBootsVecDrop.Smoke
