namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem alignment_values : alignmentDiscriminants.map Fin.val = (List.range 64).map (fun exponent => 2 ^ exponent) := by decide

theorem alignment_member (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) : alignment ∈ alignmentDiscriminants := by
  have member : alignment.val ∈ alignmentDiscriminants.map Fin.val := by rw [alignment_values]; exact valid.1
  obtain ⟨word,member,same⟩ := List.mem_map.mp member
  have identical : word = alignment := Fin.ext same
  subst word
  exact member

theorem getter_overflow (world : NativeReferenceMachine.State) :
    eval getterBody (materializedFrame world .capacityOverflow) =
      .returned (NativeReservationErrorLocal.kindValue tags .capacityOverflow) world := by
  simp [getterBody,allocationBody,overflowBody,materializedFrame,alignmentType,layoutType,kindType,errorType,tags,
    NativeReservationErrorLocal.encode,NativeReservationErrorLocal.kindValue,eval,evalRvalue,evalOperand,evalArgs,retag,NativeSliceLLBC.retagValue,
    selectChoice,storageLive,storageDead,NativeRecordLLBC.read,write,NativeRecordValues.typeAt,
    NativeRecordValues.sideAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem getter_allocation (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    eval getterBody (materializedFrame world (.allocationError size alignment)) =
      .returned (NativeReservationErrorLocal.kindValue tags (.allocationError size alignment)) world := by
  have permitted := alignment_member size alignment valid
  simp [getterBody,allocationBody,overflowBody,materializedFrame,alignmentType,layoutType,kindType,errorType,tags,
    NativeReservationErrorLocal.encode,NativeReservationErrorLocal.kindValue,NativeReservationErrorLocal.layoutValue,
    eval,evalRvalue,evalOperand,evalArgs,retag,NativeSliceLLBC.retagValue,selectChoice,storageLive,storageDead,NativeRecordLLBC.read,write,
    NativeRecordValues.typeAt,NativeRecordValues.sideAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,
    NativeSliceLLBC.fits,permitted]

theorem getter_exact (world : NativeReferenceMachine.State) (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    eval getterBody (materializedFrame world kind) = .returned (NativeReservationErrorLocal.kindValue tags kind) world := by
  cases kind with
  | capacityOverflow => exact getter_overflow world
  | allocationError size alignment => exact getter_allocation world size alignment valid.2

theorem loaded_kind_valid (world next : NativeReferenceMachine.State) (index : Nat) (kind : Kind)
    (loaded : NativeReservationErrorFields.read world index = .value kind next) : NativeReservationErrorLocal.Valid kind := by
  cases kind with
  | capacityOverflow => trivial
  | allocationError size alignment =>
    obtain ⟨_,_,_,_,nonzero,_,valid⟩ := NativeReservationErrorFields.allocation_success world next index size alignment loaded
    exact ⟨nonzero,valid⟩

def checkedFlow : NativeRawVecFields.Result NativeRecordValues.Value → Flow
  | .invalid world => .invalid world
  | .value value world => .returned value world

theorem getter_equiv (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    invoke world value = checkedFlow (NativeReservationErrorRead.getKind tags world value) := by
  cases resolved : NativeReservationErrorRead.resolveOperand world value with
  | none => simp only [invoke,NativeReservationErrorRead.getKind,resolved,checkedFlow]
  | some index =>
    cases loaded : NativeReservationErrorFields.read world index with
    | invalid next => simp only [invoke,NativeReservationErrorRead.getKind,resolved,loaded,checkedFlow]
    | value kind next =>
      simp only [invoke,NativeReservationErrorRead.getKind,resolved,loaded,checkedFlow]
      exact getter_exact next kind (loaded_kind_valid world next index kind loaded)

theorem invoke_projects (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (invoke world value).world := by
  rw [getter_equiv]
  have projected := NativeReservationErrorRead.getKind_projects tags world value
  cases actual : NativeReservationErrorRead.getKind tags world value <;>
    simpa only [actual,checkedFlow,Flow.world,NativeRawVecFields.Result.world] using projected

theorem invoke_heap (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    (invoke world value).world.pointers.heap = world.pointers.heap := by
  rw [getter_equiv]
  have kept := NativeReservationErrorRead.getKind_heap tags world value
  cases actual : NativeReservationErrorRead.getKind tags world value <;>
    simpa only [actual,checkedFlow,Flow.world,NativeRawVecFields.Result.world] using kept

theorem invoke_snapshot_complete (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ kind final, value = NativeReservationErrorLocal.encode tags kind ∧
      invoke next result = .returned (NativeReservationErrorLocal.kindValue tags kind) final := by
  obtain ⟨kind,final,same,getter⟩ := NativeReservationErrorRead.snapshot_getKind_complete tags world next base value result valid executed
  exact ⟨kind,final,same,by rw [getter_equiv,getter]; rfl⟩

theorem invoke_reachable (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value)
    (reachable : NativeStorageBorrowMachine.Reachable world) : NativeStorageBorrowMachine.Reachable (invoke world value).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable (invoke_projects world value)

end HasteBootsReservationErrorKind
