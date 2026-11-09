namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeResidentVecBorrow

def currentMemoryLayout : Input := .record 9 (.pair (.scalar (.usize 1)) (.pair
  (.record 11 (.pair (.enumeration 12 1) .unit)) .unit))
def currentMemoryNone : NativeRecordValues.Value := .record 10 (.choice false (.scalar .unit))
def currentMemorySome (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) : NativeRecordValues.Value :=
  .record 10 (.choice true (.pair (.pair
    (.record 7 (.pair (.scalar (.raw ⟨buffer,none⟩)) (.scalar .unit)))
    (.pair (.record 9 (.pair (.scalar (.usize capacity)) (.pair
      (.record 11 (.pair (.enumeration 12 1) (.scalar .unit))) (.scalar .unit)))) (.scalar .unit))) (.scalar .unit)))

def currentMemoryPost (capacity : NativeWord64Memory.Word) (buffer : NativePointerStorage.Pointer) : Flow → Prop
  | .returned result _ => result = if capacity = 0 then currentMemoryNone else currentMemorySome buffer capacity
  | .invalid _ => True
  | _ => False

-- Source dispatch is checked for every outcome; a successful read is not supplied.
theorem current_memory_zero (world : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base 0 length buffer)
    (decoded : NativeRawVecReference.decode world index .inner = some (.reference false reference 2)) :
    currentMemoryPost 0 buffer (invoke HasteBootsRawVecDrop.f8 world [.rawVecSharedReference index,currentMemoryLayout]) := by
  cases loaded : NativeRawVecReference.eval world (.reference false reference 2) .capacity with
  | invalid failed =>
    simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, storageLive, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, loaded, settle, currentMemoryPost]
  | value value next =>
    have same := rawvec_capacity resident loaded
    subst value
    simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, evalArgs, storageLive, storageDead, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, loaded, settle, currentMemoryPost, currentMemoryNone]
theorem current_memory_nonzero (world : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (nonzero : capacity ≠ 0)
    (resident : Resident world (.reference false reference 2) base capacity length buffer)
    (decoded : NativeRawVecReference.decode world index .inner = some (.reference false reference 2)) :
    currentMemoryPost capacity buffer (invoke HasteBootsRawVecDrop.f8 world [.rawVecSharedReference index,currentMemoryLayout]) := by
  have contents := resident
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,fields⟩ := contents
  have nonnull : buffer.address ≠ 0 := by
    intro zero
    exact fields.nonnull (congrArg Fin.val zero)
  cases first : NativeRawVecReference.eval world (.reference false reference 2) .capacity with
  | invalid failed =>
    simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, storageLive, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, settle, currentMemoryPost, 
      first]
  | value value middle =>
    have same := rawvec_capacity resident first
    have carried := rawvec_capacity_preserves resident first
    subst value
    cases second : NativeRawVecReference.eval middle (.reference false reference 2) .capacity with
    | invalid failed =>
      simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, storageLive, storageDead, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, settle, currentMemoryPost, 
      nonzero, first,second]
    | value value afterCapacity =>
      have same := rawvec_capacity carried second
      have carriedAgain := rawvec_capacity_preserves carried second
      subst value
      cases pointerRead : NativeRawVecReference.eval afterCapacity (.reference false reference 2) .pointer with
      | invalid failed =>
        simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, evalArgs, storageLive, storageDead, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, settle, currentMemoryPost, 
      evalMultiply, multiplyWords, evalEnumWord, enumWordValue, nonzero, first,second,pointerRead]
      | value value afterPointer =>
        have same := rawvec_pointer carriedAgain pointerRead
        subst value
        cases markerRead : NativeRawVecReference.eval afterPointer (.reference false reference 2) .marker with
        | invalid failed =>
          simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, evalArgs, storageLive, storageDead, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, settle, currentMemoryPost, 
      evalMultiply, multiplyWords, evalEnumWord, enumWordValue, recordResultValue, nonzero, nonnull, first,second,pointerRead,markerRead]
        | value value final =>
          have same := rawvec_marker afterPointer final (.reference false reference 2) value markerRead
          subst value
          simp [invoke, HasteBootsRawVecDrop.f8, decodeArgs, decode, decoded, initial, currentMemoryLayout, eval, evalRvalue,
      evalRawVecField, evalOperand, evalArgs, storageLive, storageDead, write, NativeRecordLLBC.read,
      NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
      NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.replace, NativeRecordValues.copyable,
      NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag, NativeSliceLLBC.retagValue,
      HasteBootsRawVecDrop.alignmentDiscriminants, settle, currentMemoryPost, currentMemorySome,
      evalMultiply, multiplyWords, evalEnumWord, enumWordValue, recordResultValue, nonzero, nonnull, first,second,pointerRead,markerRead]
theorem current_memory (world : NativeReferenceMachine.State) (index : Nat)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base capacity length buffer)
    (decoded : NativeRawVecReference.decode world index .inner = some (.reference false reference 2)) :
    currentMemoryPost capacity buffer (invoke HasteBootsRawVecDrop.f8 world [.rawVecSharedReference index,currentMemoryLayout]) := by
  by_cases zero : capacity = 0
  · subst capacity; exact current_memory_zero world index reference base buffer length resident decoded
  · exact current_memory_nonzero world index reference base buffer capacity length zero resident decoded

theorem current_memory_resident (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base capacity length buffer) :
    currentMemoryPost capacity buffer (invoke HasteBootsRawVecDrop.f8 world
      [.rawVecSharedReference (world.references.idxOf reference),currentMemoryLayout]) :=
  current_memory world (world.references.idxOf reference) reference base buffer capacity length resident
    (shared_rawvec_decode resident)

theorem current_memory_return (world final : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base capacity length buffer)
    (result : NativeRecordValues.Value)
    (returned : invoke HasteBootsRawVecDrop.f8 world
      [.rawVecSharedReference (world.references.idxOf reference),currentMemoryLayout] = .returned result final) :
    result = if capacity = 0 then currentMemoryNone else currentMemorySome buffer capacity := by
  have checked := current_memory_resident world reference base buffer capacity length resident
  rw [returned] at checked
  exact checked
end HasteBootsVecDrop
