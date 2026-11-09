namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- The original zero-size arm constructs its success value and returns directly.
The caller's Global argument must be initialized; all other ambient slots and
the incoming memory and reference world are arbitrary. -/
theorem zero_size_exact (ambient : Frame)
    (allocator : ambient.slots[3]?.getD .dead = .live (some allocatorValue)) :
    eval zeroSizeBody (layoutAcceptedFrame ambient 0) = .returned zeroResultValue ambient.world := by
  simp [zeroSizeBody,layoutAcceptedFrame,layoutTypes,allocatorValue,zeroResultValue,zeroRawValue,byteAlignment,
    alignmentDiscriminants,eval,evalRvalue,evalEnumAddress,enumAddressValue,evalArgs,evalOperand,
    storageLive,storageDead,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits,allocator]

/-- The zero-size return suppresses both the positive arm and the outer tail. -/
theorem zero_capacity_return (ambient : Frame)
    (allocator : ambient.slots[3]?.getD .dead = .live (some allocatorValue))
    (overflow rejected positive next : Body) :
    eval (layoutPrefix overflow (capacityDispatch zeroSizeBody positive .done) rejected next)
      (layoutFrame ambient 0) = .returned zeroResultValue ambient.world := by
  rw [layout_capacity_dispatch ambient 0 (by decide)]
  rw [show decide ((0 : NativeWord64Memory.Word) = 0) = true from rfl,true_branch_continuation,
    zero_size_exact ambient allocator]
  rfl

end HasteBootsVecCapacityArithmetic
