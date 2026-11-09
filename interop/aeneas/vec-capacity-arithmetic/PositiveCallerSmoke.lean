namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example : NativeRecordValues.get (positiveVecValue ⟨8,some ⟨8,0⟩⟩ 3)
    [(.unwrap 0),.left, (.unwrap 2),.left, (.unwrap 3),.left, (.unwrap 6),.left, (.unwrap 13),.left] =
      some (.scalar (.raw ⟨⟨8,some ⟨8,0⟩⟩,none⟩)) := rfl

example : NativeRecordValues.get (positiveVecValue ⟨8,some ⟨8,0⟩⟩ 3)
    [(.unwrap 0),.left, (.unwrap 2),.left, (.unwrap 3),.right,.left, (.unwrap 7),.left] = some (.scalar (.usize 3)) := rfl

example : NativeRecordValues.get (positiveVecValue ⟨8,some ⟨8,0⟩⟩ 3) [(.unwrap 0),.right,.left] =
    some (.scalar (.usize 0)) := rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (positiveCapacityRootReturned ambient 3 world ⟨8,some ⟨8,0⟩⟩).slots[2]? = some (.live (some .uninit)) := by
  simp [positiveCapacityRootReturned,capacityRootMoved]

private def callerBorrowed : NativeReferenceMachine.State := NativeZstBorrow.granted NativeReferenceMachine.empty 64
private def callerAllocated : NativeReferenceMachine.State := NativeAllocatorExecution.allocated callerBorrowed 8 ⟨3,1⟩

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) callerBorrowed [] = .returned (.scalar .unit) callerBorrowed) :
    NativeAllocatorLLBC.invoke (positiveCapacityRoot {ambient with world := NativeReferenceMachine.empty} 64 (some 8) shim)
      NativeReferenceMachine.empty [.scalar (.usize 3)] = .returned (positiveVecValue ⟨8,some ⟨8,0⟩⟩ 3) callerAllocated :=
  positive_capacity_decoded _ 3 64 (by decide) (some 8) shim _ _ _ (by decide) (by decide) (by decide) returned (by decide)

example : NativeByteRange.loadRange callerAllocated.pointers.heap.memory ⟨8,some ⟨8,0⟩⟩ ⟨3,1⟩ = none := by decide

example (ambient : Frame) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0) :
    eval (rawCallerTail (.unsupported "error") (.unsupported "cold")) (positiveRawCallerReturned ambient 3 world pointer) =
      .returned (positiveRawValue pointer 3) world := positive_raw_caller_tail ambient 3 world pointer nonnull _ _

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (value : NativeRecordValues.Value) (reachable : NativeReferenceMachine.Reachable ambient.world)
    (returned : NativeAllocatorLLBC.invoke (positiveCapacityRoot ambient 64 (some 8) shim) ambient.world [.scalar (.usize 3)] =
      .returned value world) : NativeReferenceMachine.Reachable world :=
  positive_capacity_reachable ambient 3 64 (some 8) shim world value reachable returned

end HasteBootsVecCapacityArithmetic
