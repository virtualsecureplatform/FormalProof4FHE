namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeReservationErrorFields (Kind wordAccess)
private def wrapperReady (kind : Kind) : NativeReferenceMachine.State :=
  (NativeReservationErrorLocal.snapshotValue tags NativeReferenceMachine.empty 64 (NativeReservationErrorLocal.encode tags kind)).world
private def wrapperOperand : NativeRecordValues.Value := .scalar (.reference false ⟨0⟩ 2)
private def wrapperBorrowed (kind : Kind) : NativeReferenceMachine.State :=
  borrowedWorld (wrapperReady kind) ⟨0⟩ ⟨64,some ⟨64,0⟩⟩
private def wrapperRead (kind : Kind) : NativeReferenceMachine.State :=
  match kind with
  | .capacityOverflow => (wordAccess (wrapperBorrowed kind) 0 0).world
  | .allocationError _ _ => (wordAccess (wordAccess (wrapperBorrowed kind) 0 0).world 0 8).world
private def wrapperClosed (kind : Kind) : NativeReferenceMachine.State :=
  {wrapperRead kind with leases := (wrapperReady kind).leases}
example : reborrow (wrapperReady .capacityOverflow) wrapperOperand =
    .value (.scalar (.reference false ⟨1⟩ 2)) (wrapperBorrowed .capacityOverflow) := by decide
example : rootInvoke (wrapperReady .capacityOverflow) wrapperOperand =
    .returned (NativeReservationErrorLocal.kindValue tags .capacityOverflow) (wrapperRead .capacityOverflow) := by decide
example : rootWithCleanup (wrapperReady .capacityOverflow) wrapperOperand =
    .returned (NativeReservationErrorLocal.kindValue tags .capacityOverflow) (wrapperClosed .capacityOverflow) := by decide
example : rootWithCleanup (wrapperReady (.allocationError 3 8)) wrapperOperand =
    .returned (NativeReservationErrorLocal.kindValue tags (.allocationError 3 8)) (wrapperClosed (.allocationError 3 8)) := by decide
example : (wrapperClosed .capacityOverflow).leases = (wrapperReady .capacityOverflow).leases := rfl
example : NativeByteBorrow.lookup (wrapperClosed .capacityOverflow).leases 1 = none := by decide
example : NativeByteBorrow.lookup (wrapperClosed .capacityOverflow).leases 0 =
    some ⟨0,none,⟨64,some ⟨64,0⟩⟩,⟨16,8⟩,.shared⟩ := by decide
example : (wrapperClosed .capacityOverflow).nextTag = 2 := by decide
example : (wrapperClosed .capacityOverflow).births.length = 2 := by decide
example : (wrapperClosed .capacityOverflow).references = [⟨1⟩,⟨0⟩] := by decide
example : NativeReservationErrorRead.getKind tags (wrapperClosed .capacityOverflow) (.scalar (.reference false ⟨1⟩ 2)) =
    .invalid (wrapperClosed .capacityOverflow) := by decide
example : NativeReservationErrorRead.getKind tags (wrapperClosed .capacityOverflow) wrapperOperand =
    .value (NativeReservationErrorLocal.kindValue tags .capacityOverflow) (wordAccess (wrapperClosed .capacityOverflow) 1 0).world := by decide
example : NativeByteRange.loadRange (wrapperClosed .capacityOverflow).pointers.heap.memory ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide
example : rootWithCleanup (wrapperReady .capacityOverflow) (.scalar (.reference true ⟨0⟩ 2)) = .invalid (wrapperReady .capacityOverflow) := by decide
example : rootWithCleanup (wrapperReady .capacityOverflow) (.scalar (.reference false ⟨0⟩ 0)) = .invalid (wrapperReady .capacityOverflow) := by decide
example : rootWithCleanup (wrapperReady .capacityOverflow) (.scalar (.reference false ⟨99⟩ 2)) = .invalid (wrapperReady .capacityOverflow) := by decide
example (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    (rootWithCleanup world value).world.pointers.heap = world.pointers.heap := rootWithCleanup_heap world value
example : ∃ kind final, NativeReservationErrorLocal.encode tags .capacityOverflow = NativeReservationErrorLocal.encode tags kind ∧
    rootWithCleanup (wrapperReady .capacityOverflow) wrapperOperand = .returned (NativeReservationErrorLocal.kindValue tags kind) final ∧
      final.leases = (wrapperReady .capacityOverflow).leases :=
  root_snapshot_complete NativeReferenceMachine.empty _ 64 _ wrapperOperand NativeReferenceMachine.empty_wellFormed (by decide)
private def invalidPointee : NativeReferenceMachine.State :=
  (NativeStorageBorrowMachine.run NativeReferenceMachine.empty [.legacy (.raw (.allocate 64 ⟨16,8⟩)),
    .legacy (.raw (.writeBytes 0 8 (NativeWord64Memory.encode 1))),.storageBorrow none 0 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty
private def invalidChild : NativeReferenceMachine.State := borrowedWorld invalidPointee ⟨0⟩ ⟨64,some ⟨64,0⟩⟩
example : rootWithCleanup invalidPointee wrapperOperand = .invalid (wordAccess invalidChild 0 0).world := by decide
example : (rootWithCleanup invalidPointee wrapperOperand).world.leases.length = 2 := by decide
end HasteBootsReservationErrorKind
