/-! Nominal relabeling of the validated getter statement tree. This transports
logical type identities only; native layout and lifetime refinement remain open. -/
namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem getter_overflow_for (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State) :
    eval (getterBodyFor descriptor) ((materializedFrameFor descriptor) world .capacityOverflow) =
      .returned (NativeReservationErrorLocal.kindValue descriptor .capacityOverflow) world := by
  simp [getterBodyFor,allocationBodyFor,overflowBodyFor,materializedFrameFor,alignmentTypeFor,layoutTypeFor,kindTypeFor,errorTypeFor,
    NativeReservationErrorLocal.encode,NativeReservationErrorLocal.kindValue,eval,evalRvalue,evalOperand,evalArgs,retag,NativeSliceLLBC.retagValue,
    selectChoice,storageLive,storageDead,NativeRecordLLBC.read,write,NativeRecordValues.typeAt,
    NativeRecordValues.sideAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem getter_allocation_for (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    eval (getterBodyFor descriptor) ((materializedFrameFor descriptor) world (.allocationError size alignment)) =
      .returned (NativeReservationErrorLocal.kindValue descriptor (.allocationError size alignment)) world := by
  have permitted := alignment_member size alignment valid
  simp [getterBodyFor,allocationBodyFor,overflowBodyFor,materializedFrameFor,alignmentTypeFor,layoutTypeFor,kindTypeFor,errorTypeFor,
    NativeReservationErrorLocal.encode,NativeReservationErrorLocal.kindValue,NativeReservationErrorLocal.layoutValue,
    eval,evalRvalue,evalOperand,evalArgs,retag,NativeSliceLLBC.retagValue,selectChoice,storageLive,storageDead,NativeRecordLLBC.read,write,
    NativeRecordValues.typeAt,NativeRecordValues.sideAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,
    NativeSliceLLBC.fits,permitted]

theorem getter_exact_for (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State) (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    eval (getterBodyFor descriptor) ((materializedFrameFor descriptor) world kind) = .returned (NativeReservationErrorLocal.kindValue descriptor kind) world := by
  cases kind with
  | capacityOverflow => exact getter_overflow_for descriptor world
  | allocationError size alignment => exact getter_allocation_for descriptor world size alignment valid.2

theorem invoke_for_equiv (descriptor : NativeReservationErrorLocal.Tags)
    (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    invokeFor descriptor world value = checkedFlow (NativeReservationErrorRead.getKind descriptor world value) := by
  cases resolved : NativeReservationErrorRead.resolveOperand world value with
  | none => simp only [invokeFor,NativeReservationErrorRead.getKind,resolved,checkedFlow]
  | some index =>
    cases loaded : NativeReservationErrorFields.read world index with
    | invalid next => simp only [invokeFor,NativeReservationErrorRead.getKind,resolved,loaded,checkedFlow]
    | value kind next =>
      simp only [invokeFor,NativeReservationErrorRead.getKind,resolved,loaded,checkedFlow]
      exact getter_exact_for descriptor next kind (loaded_kind_valid world next index kind loaded)

theorem getter_body_specializes : getterBodyFor tags = getterBody := rfl

theorem frame_specializes (world : NativeReferenceMachine.State) (kind : Kind) :
    materializedFrameFor tags world kind = materializedFrame world kind := rfl

theorem invoke_specializes (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    invokeFor tags world value = invoke world value := rfl

theorem invoke_projects_for (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (invokeFor descriptor world value).world := by
  rw [invoke_for_equiv]
  have projected := NativeReservationErrorRead.getKind_projects descriptor world value
  cases actual : NativeReservationErrorRead.getKind descriptor world value <;>
    simpa only [actual,checkedFlow,Flow.world,NativeRawVecFields.Result.world] using projected

theorem invoke_heap_for (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    (invokeFor descriptor world value).world.pointers.heap = world.pointers.heap := by
  rw [invoke_for_equiv]
  have kept := NativeReservationErrorRead.getKind_heap descriptor world value
  cases actual : NativeReservationErrorRead.getKind descriptor world value <;>
    simpa only [actual,checkedFlow,Flow.world,NativeRawVecFields.Result.world] using kept

theorem invoke_snapshot_complete_for (descriptor : NativeReservationErrorLocal.Tags) (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue descriptor world base value = .value result next) :
    ∃ kind final, value = NativeReservationErrorLocal.encode descriptor kind ∧
      invokeFor descriptor next result = .returned (NativeReservationErrorLocal.kindValue descriptor kind) final := by
  obtain ⟨kind,final,same,getter⟩ := NativeReservationErrorRead.snapshot_getKind_complete descriptor world next base value result valid executed
  exact ⟨kind,final,same,by rw [invoke_for_equiv,getter]; rfl⟩

theorem invoke_reachable_for (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value)
    (reachable : NativeStorageBorrowMachine.Reachable world) : NativeStorageBorrowMachine.Reachable (invokeFor descriptor world value).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable (invoke_projects_for descriptor world value)

end HasteBootsReservationErrorKind
