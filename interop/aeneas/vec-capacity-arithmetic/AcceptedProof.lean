namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- Source success aggregates and partial moves preserve the byte layout. The
unused reservation-error field type is arbitrary in the ambient context. -/
theorem accepted_layout_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (next : Body) :
    eval (acceptedLayoutPrefix next) (layoutAfterFrame ambient capacity) =
    eval next (layoutAcceptedFrame ambient capacity) := by
  simp [acceptedLayoutPrefix,layoutAfterFrame,layoutAcceptedFrame,layoutTypes,capacityLayout,byteAlignment,alignmentDiscriminants,
    eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem usize_dispatch {frame caller : Frame} {operand : Operand} {word : NativeWord64Memory.Word}
    (expected : NativeWord64Memory.Word) (yes no next : Body)
    (selected : evalOperand frame operand = some (.scalar (.usize word),caller)) :
    eval (.switchUsize operand expected yes no next) frame =
    eval (.constIf (decide (word = expected)) yes no next) caller := by
  simp only [eval,selected,decide_eq_true_eq]

theorem capacity_dispatch_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zero positive next : Body) :
    eval (capacityDispatch zero positive next) (layoutAfterFrame ambient capacity) =
    eval (.constIf (decide (capacity = 0)) zero positive next) (layoutAcceptedFrame ambient capacity) := by
  have selected : evalOperand (layoutAcceptedFrame ambient capacity) (.copy 7 []) =
      some (.scalar (.usize capacity),layoutAcceptedFrame ambient capacity) := by
    simp [evalOperand,NativeRecordLLBC.read,layoutAcceptedFrame,layoutTypes,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.copyable,NativeRecordValues.complete,NativeRecordValues.fits,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [capacityDispatch,accepted_layout_exact,usize_dispatch _ _ _ _ selected]

theorem true_branch_continuation (yes no next : Body) (frame : Frame) :
    eval (.constIf true yes no next) frame = continueWith next (eval yes frame) := rfl

/-- The complete retained prefix reaches the correct size-dispatch continuation
when the signed layout bound holds, for arbitrary unprocessed source bodies. -/
theorem layout_capacity_dispatch (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (valid : capacity.val < 2^63) (overflow rejected zero positive next : Body) :
    eval (layoutPrefix overflow (capacityDispatch zero positive .done) rejected next) (layoutFrame ambient capacity) =
    eval (.constIf (decide (capacity = 0)) zero positive next) (layoutAcceptedFrame ambient capacity) := by
  rw [layout_prefix_exact]
  rw [decide_eq_true valid]
  rw [true_branch_continuation]
  rw [capacity_dispatch_exact,constant_branch_tail]

end HasteBootsVecCapacityArithmetic
