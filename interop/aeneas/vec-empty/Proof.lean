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

/-- Execute the retained constructor, validate its fields and store its empty
representation with actual checked machine operations. -/
def constructStored (world : NativeReferenceMachine.State) (register : Nat) : Option NativeReferenceMachine.State :=
  match invoke f0 world [] with
  | .returned value after =>
    if NativeRecordValues.get value capacityPath = some (.scalar (.usize 0)) ∧
        NativeRecordValues.get value pointerPath = some (.scalar (.raw ⟨⟨1,none⟩,none⟩)) ∧
        NativeRecordValues.get value lengthPath = some (.scalar (.usize 0)) then
      NativeEmptyVecStorage.install after register
    else none
  | _ => none

theorem constructStored_complete (world : NativeReferenceMachine.State) (register : Nat) (header : NativePointerStorage.Pointer)
    (reachable : NativeReferenceMachine.Reachable world)
    (resident : world.pointers.registers[register]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (separate : NativeVecBytePrefix.Available world header 24) :
    ∃ next, ∃ ready : NativeEmptyVecStorage.Ready next,
      constructStored world register = some next ∧ NativeReferenceMachine.Reachable next ∧
      next.pointers.registers = world.pointers.registers ∧
      next.leases = ready.descriptor.lease :: world.leases ∧
      next.references = ⟨world.nextTag⟩ :: world.references ∧
      ready.descriptor.reference = ⟨world.nextTag⟩ := by
  obtain ⟨next,ready,installed,reached,registers,loans,references,reference⟩ :=
    NativeEmptyVecStorage.install_complete world register header reachable resident checked separate
  refine ⟨next,ready,?_,reached,registers,loans,references,reference⟩
  simp only [constructStored,empty_invocation,empty_fields.1,empty_fields.2.1,empty_fields.2.2,and_self,ite_true,installed]

end HasteBootsVecEmpty
