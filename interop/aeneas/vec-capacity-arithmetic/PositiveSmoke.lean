namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (ambient : Frame) :
    eval (layoutPrefix (.unsupported "overflow")
      (capacityDispatch (.unsupported "zero") (positiveModePrefix 1 .done (.unsupported "zeroed") .done) .done)
      (.unsupported "layout") .done) (layoutFrame (positiveAmbient ambient false) 1) =
      .normal (positiveBorrowFrame ambient 1 false 1) := by
  rw [positive_layout_entry ambient 1 false (by decide) (by decide) 1 (by decide)]
  rfl

example (ambient : Frame) :
    eval (layoutPrefix (.unsupported "overflow")
      (capacityDispatch (.unsupported "zero") (positiveModePrefix 1 (.unsupported "uninitialized") .done .done) .done)
      (.unsupported "layout") .done) (layoutFrame (positiveAmbient ambient true) ⟨9223372036854775807,by decide⟩) =
      .normal (positiveBorrowFrame ambient ⟨9223372036854775807,by decide⟩ true 1) := by
  rw [positive_layout_entry ambient ⟨9223372036854775807,by decide⟩ true (by decide) (by decide) 1 (by decide)]
  rfl

example (ambient : Frame) :
    eval (positiveModePrefix 1 .abort (.unsupported "zeroed") (.unsupported "tail"))
      (layoutAcceptedFrame (positiveAmbient ambient false) 1) = .invalid (NativeZstBorrow.granted ambient.world 1) := by
  rw [positive_mode_exact ambient 1 false 1 (by decide)]
  rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool) :
    evalArgs (positiveBorrowFrame ambient capacity zeroed 1) (positiveCallArgs zeroed) =
      some ([.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity],positiveMovedFrame ambient capacity zeroed 1) :=
  positive_call_arguments ambient capacity zeroed 1

example (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool) :
    NativeZstReference.decode (positiveMovedFrame ambient capacity zeroed 1).world 0 =
      some (.reference false ⟨ambient.world.nextTag⟩ 0) := positive_borrow_decoded ambient capacity zeroed 1

example (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    NativeRecordLLBC.read (positiveMovedFrame ambient capacity false 1) 11 [] = none := by
  simp [positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,positiveAmbient,layoutAcceptedFrame,layoutTypes,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.complete]

example (ambient : Frame) :
    eval (positiveModePrefix 0 .done .done .done) (layoutAcceptedFrame (positiveAmbient ambient false) 1) =
      .invalid (NativeZstBorrow.placed ambient.world 0) := by
  simp [positiveModePrefix,positiveBorrowPrefix,positiveAmbient,allocationModeValue,allocationInitType,
    layoutAcceptedFrame,layoutTypes,allocatorValue,eval,evalRvalue,evalZstBorrow,NativeZstBorrow.issue_null,
    selectChoice,storageLive,storageDead,NativeRecordLLBC.read,NativeRecordValues.sideAt,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]
end HasteBootsVecCapacityArithmetic
