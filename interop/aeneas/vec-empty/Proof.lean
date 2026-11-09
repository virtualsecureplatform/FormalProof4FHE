namespace HasteBootsVecEmpty
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordCallValues

/-- The retained constructor and caller return their actual nominal empty Vec
value for every incoming world, without changing that world. -/
theorem empty_exact (world : NativeReferenceMachine.State) :
    invokeValues f0 world [] = .returned emptyValue world := by
  simp [invokeValues,f0,initial,eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,write,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeRecordValues.copyable,
    NativeSliceLLBC.fits,settle,emptyValue]

theorem constructor_exact (world : NativeReferenceMachine.State) :
    invokeValues f1 world [] = .returned emptyValue world := by
  simp [invokeValues,f1,initial,eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,write,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeRecordValues.copyable,
    NativeSliceLLBC.fits,settle,emptyValue]

theorem empty_invocation (world : NativeReferenceMachine.State) :
    invoke f0 world [] = .returned emptyValue world := by
  simp only [NativeRecordCallValues.invoke_eq,decodeArgs,empty_exact]

theorem empty_fields :
    NativeRecordValues.get emptyValue capacityPath = some (.scalar (.usize 0)) ∧
    NativeRecordValues.get emptyValue pointerPath = some (.scalar (.raw ⟨⟨1,none⟩,none⟩)) ∧
    NativeRecordValues.get emptyValue lengthPath = some (.scalar (.usize 0)) := by decide

theorem returned_fields (world final : NativeReferenceMachine.State) (value : NativeRecordValues.Value)
    (returned : invoke f0 world [] = .returned value final) :
    final = world ∧ NativeRecordValues.get value capacityPath = some (.scalar (.usize 0)) ∧
      NativeRecordValues.get value pointerPath = some (.scalar (.raw ⟨⟨1,none⟩,none⟩)) ∧
      NativeRecordValues.get value lengthPath = some (.scalar (.usize 0)) := by
  rw [empty_invocation] at returned
  cases returned
  exact ⟨rfl,empty_fields⟩

/-- A dangling numerical address carries no live allocation origin. -/
theorem empty_pointer_unreadable (world : NativeReferenceMachine.State) (layout : NativeByteMemory.Layout)
    (positive : 0 < layout.size) :
    NativeByteRange.loadRange world.pointers.heap.memory ⟨1,none⟩ layout = none :=
  NativeByteRange.positive_without_origin _ _ layout positive rfl

end HasteBootsVecEmpty
