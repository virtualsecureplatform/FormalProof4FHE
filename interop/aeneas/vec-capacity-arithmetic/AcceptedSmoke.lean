namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (ambient : Frame) (overflow rejected next : Body) :
    eval (layoutPrefix overflow (capacityDispatch .done (.unsupported "positive") .done) rejected next)
      (layoutFrame ambient 0) = eval next (layoutAcceptedFrame ambient 0) := by
  rw [layout_capacity_dispatch ambient 0 (by decide)]
  rfl

example (ambient : Frame) (overflow rejected next : Body) :
    eval (layoutPrefix overflow (capacityDispatch (.unsupported "zero") .done .done) rejected next)
      (layoutFrame ambient 1) = eval next (layoutAcceptedFrame ambient 1) := by
  rw [layout_capacity_dispatch ambient 1 (by decide)]
  rfl

example (ambient : Frame) (overflow rejected next : Body) :
    eval (layoutPrefix overflow (capacityDispatch (.unsupported "zero") .abort .done) rejected next)
      (layoutFrame ambient ⟨9223372036854775807,by decide⟩) = .invalid ambient.world := by
  rw [layout_capacity_dispatch ambient ⟨9223372036854775807,by decide⟩ (by decide)]
  rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAcceptedFrame ambient capacity).slots[6]? = some (.live (some (capacityLayout capacity))) := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAcceptedFrame ambient capacity).slots[22]? = some .dead := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAcceptedFrame ambient capacity).slots[31]? = some .dead := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAcceptedFrame ambient capacity).slots[2]? = some (ambient.slots[2]?.getD .dead) := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    (layoutAcceptedFrame ambient capacity).world = ambient.world := rfl
end HasteBootsVecCapacityArithmetic
