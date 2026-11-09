namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)
open NativeReferenceMachine (State Reference)

theorem reborrow_projects (world : State) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (reborrow world value).world := by
  unfold reborrow
  split
  next reference count =>
    cases parentEq : NativeRawVecBorrow.parent world (.reference false reference count) with
    | none => exact .refl _
    | some entry =>
      rcases entry with ⟨index,register,lease⟩
      cases issued : NativeStorageBorrowMachine.execute world (.storageBorrow (some index) register .shared ⟨16,8⟩) with
      | none => simp only [issued,NativeRawVecFields.Result.world]; exact .refl _
      | some next => simpa only [issued,NativeRawVecFields.Result.world] using NativeStorageBorrowMachine.Runs.step (.refl world) _ issued
  next => exact .refl _

theorem reborrow_heap (world : State) (value : NativeRecordValues.Value) :
    (reborrow world value).world.pointers.heap = world.pointers.heap := by
  unfold reborrow
  split
  next reference count =>
    cases parentEq : NativeRawVecBorrow.parent world (.reference false reference count) with
    | none => rfl
    | some entry =>
      rcases entry with ⟨index,register,lease⟩
      cases issued : NativeStorageBorrowMachine.execute world (.storageBorrow (some index) register .shared ⟨16,8⟩) with
      | none => simp only [issued,NativeRawVecFields.Result.world]
      | some next => simpa only [issued,NativeRawVecFields.Result.world] using NativeStorageBorrowMachine.storage_heap world next (some index) register .shared ⟨16,8⟩ issued
  next => rfl

theorem root_initial (world : State) (reference : Reference) (count : NativeWord64Memory.Word) :
    initial rootTypes 1 [.scalar (.reference false reference count)] world = some (rootFrame world (.scalar (.reference false reference count))) := by
  simp [initial,rootTypes,rootFrame,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeSliceLLBC.fits,List.replicate_succ]

theorem kind_fits (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    NativeRecordValues.fits kindType (NativeReservationErrorLocal.kindValue tags kind) = true := by
  cases kind with
  | capacityOverflow => simp [kindType,NativeReservationErrorLocal.kindValue,tags,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  | allocationError size alignment =>
    have permitted := alignment_member size alignment valid.2
    simp [kindType,layoutType,alignmentType,NativeReservationErrorLocal.kindValue,NativeReservationErrorLocal.layoutValue,
      tags,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,permitted]

theorem root_call_returns (world borrowed final : State) (reference : Reference) (kind : Kind)
    (valid : NativeReservationErrorLocal.Valid kind)
    (issued : reborrow world (.scalar (.reference false reference 2)) =
      .value (.scalar (.reference false ⟨world.nextTag⟩ 2)) borrowed)
    (called : invoke borrowed (.scalar (.reference false ⟨world.nextTag⟩ 2)) =
      .returned (NativeReservationErrorLocal.kindValue tags kind) final) :
    rootInvoke world (.scalar (.reference false reference 2)) = .returned (NativeReservationErrorLocal.kindValue tags kind) final := by
  have fits := kind_fits kind valid
  have properties : NativeRecordValues.complete (NativeReservationErrorLocal.kindValue tags kind) = true ∧
      NativeRecordValues.compatible kindType (NativeReservationErrorLocal.kindValue tags kind) = true := by
    simpa only [NativeRecordValues.fits,Bool.and_eq_true] using fits
  rw [rootInvoke,root_initial]
  simp [rootEval,rootFrame,rootTypes,rootPrefix,rootResume,rootTail,eval,storageLive,storageDead,
    NativeRecordLLBC.read,write,evalArgs,evalOperand,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeSliceLLBC.fits,issued,called,properties.1,properties.2]

def authority (start finish : State) : Prop := NativeReferenceMachine.SameAuthority start finish

theorem read_authority (world : State) (index : Nat) :
    authority world (NativeReservationErrorFields.read world index).world := by
  apply NativeReservationErrorFields.read_preserves (authority world) ?_ world index ⟨rfl,rfl,rfl,rfl⟩
  intro before after register offset actual prior
  obtain ⟨_,_,pointer,prepared,_,_,_,_,_,_,_,performed⟩ :=
    NativeReferenceMachine.access_success before after register offset (.read 8 8) actual
  obtain ⟨counter,leases,references,births⟩ := NativeReferenceMachine.perform_authority before after prepared pointer (.read 8 8) performed
  exact ⟨counter.trans prior.1,leases.trans prior.2.1,references.trans prior.2.2.1,births.trans prior.2.2.2⟩

theorem invoke_authority (world : State) (value : NativeRecordValues.Value) : authority world (invoke world value).world := by
  rw [getter_equiv]
  unfold NativeReservationErrorRead.getKind
  cases resolved : NativeReservationErrorRead.resolveOperand world value with
  | none => exact ⟨rfl,rfl,rfl,rfl⟩
  | some index =>
    have preserved := read_authority world index
    cases actual : NativeReservationErrorFields.read world index <;>
      simpa only [actual,checkedFlow,Flow.world,NativeRawVecFields.Result.world] using preserved

end HasteBootsReservationErrorKind
