namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (world : NativeReferenceMachine.State) :
    invoke (capacityZeroRoot ⟨[],[],world⟩) world [.scalar (.usize 0)] = .returned zeroVecValue world :=
  capacity_zero_root ⟨[],[],world⟩

example (ambient : Frame) :
    invoke (capacityZeroRoot ambient) ambient.world [] = .invalid ambient.world := by
  simp [invoke,decodeArgs,capacityZeroRoot,initial]

example (ambient : Frame) :
    invoke (capacityZeroRoot ambient) ambient.world [.unit] = .invalid ambient.world := by
  simp [invoke,decodeArgs,decode,capacityZeroRoot,initial,capacityRootTypes,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

example (ambient : Frame) :
    invoke (capacityZeroRoot ambient) ambient.world [.scalar (.usize 0),.scalar (.usize 0)] = .invalid ambient.world := by
  simp [invoke,decodeArgs,decode,NativeSliceLLBC.decodeInput,capacityZeroRoot,initial]

example (ambient : Frame) :
    eval (rawCallerCall ambient .abort (rawCallerTail .abort .abort)) (rawCallerFrame ambient 0) =
      .returned zeroRawValue ambient.world := raw_caller_zero_return ambient .abort .abort .abort

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    evalArgs (vecCallerPrepared ambient capacity) vecCallerArgs =
      some ([.scalar (.usize capacity),allocatorValue,byteLayout],vecCallerMoved ambient capacity) :=
  vec_caller_arguments ambient capacity

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    NativeRecordLLBC.read (rawCallerMoved ambient capacity) 2 [] = none := by
  simp [rawCallerMoved,rawCallerTypes,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.complete]

example : NativeRecordValues.get zeroVecValue [(.unwrap 0),.right,.left] = some (.scalar (.usize 0)) := by decide

example : NativeRecordValues.get zeroVecValue
    [(.unwrap 0),.left,(.unwrap 2),.left,(.unwrap 3),.right,.left,(.unwrap 7),.left] = some (.scalar (.usize 0)) := by decide

example : NativeRecordValues.get zeroVecValue
    [(.unwrap 0),.left,(.unwrap 2),.left,(.unwrap 3),.left,(.unwrap 6),.left,(.unwrap 13),.left] =
    some (.scalar (.raw ⟨⟨1,none⟩,none⟩)) := by decide

example (ambient : Frame) :
    NativeRecordCallValues.invokeValues (zeroCallee ambient) ambient.world
      [.scalar (.usize 1),uninitializedValue,allocatorValue,byteLayout] =
      .unsupported "source positive arm" ambient.world := by
  rw [NativeRecordCallValues.invokeValues_initialized _ _ _ _ (callee_initialized ambient 1)]
  rw [show (zeroCallee ambient).body = zeroCalleeBody from rfl,zeroCalleeBody,
    layout_capacity_dispatch (calleeEntryAmbient ambient) 1 (by decide)]
  rfl
end HasteBootsVecCapacityArithmetic
