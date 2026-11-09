module
import FormalProof4FHE.HasteBoots.NativeIncomingReference
namespace FormalProof4FHETest.HasteBootsIncomingReferenceSmoke
open FormalProof4FHE.HasteBoots
open NativeIncomingReference
private def buffer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def header : NativePointerStorage.Pointer := ⟨128,some ⟨128,1⟩⟩
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨3,1⟩),.raw (.writeBytes 0 1 [9,8,7]),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 3)),.raw (.withAddress 0 136),.raw (.store 0 2),
     .raw (.withAddress 1 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 3)),.borrow 2 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
private def entered : NativeReferenceMachine.State :=
  ((NativeSliceLLBC.issue ready true (.raw ⟨buffer,some 3⟩) .byte).map Prod.snd).getD NativeReferenceMachine.empty
private def slice : NativeByteSliceIndex.Slice := ⟨⟨1⟩,3⟩
private def finished := NativeByteDropTraversal.run entered slice
private def dataLease : NativeByteBorrow.Lease := ⟨1,none,buffer,⟨3,1⟩,.exclusive⟩
private theorem view : NativeResidentVecBorrow.Resident entered (.reference true ⟨0⟩ 3) header 3 3 buffer := by
  refine ⟨true,⟨0⟩,3,⟨0,none,header,⟨24,8⟩,.exclusive⟩,rfl,by decide,by decide,rfl,rfl,Or.inl ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
example : finished.complete = true ∧ finished.world.nextTag = 8 ∧ finished.world.leases.map NativeByteBorrow.Lease.tag = [1,0] := by
  simp only [finished,NativeByteDropTraversal.run,NativeByteDropTraversal.runFrom,slice]
  decide
example : NativeByteBorrow.lookup finished.world.leases 0 = NativeByteBorrow.lookup entered.leases 0 :=
  (run entered slice).lookup 0 (by decide)
example : NativeByteBorrow.lookup finished.world.leases 1 = some dataLease := by
  change NativeByteBorrow.lookup (NativeByteDropTraversal.run entered slice).world.leases 1 = some dataLease
  rw [(run entered slice).lookup 1 (by decide)]
  decide
example : dataLease ∈ finished.world.births := (run entered slice).births dataLease (by decide)
example : NativeResidentVecBorrow.Resident finished.world (.reference true ⟨0⟩ 3) header 3 3 buffer :=
  traversal_resident entered slice true ⟨0⟩ 3 3 3 header buffer view (by decide)
-- A rejected byte index retains its whole-slice reborrow without ending old loans.
private def failedIteration := NativeByteDropTraversal.iteration entered slice 3
example : failedIteration = .invalid failedIteration.world ∧ failedIteration.world.nextTag = 3 ∧
    failedIteration.world.leases.map NativeByteBorrow.Lease.tag = [2,1,0] := by decide
example : NativeByteBorrow.lookup failedIteration.world.leases 1 = NativeByteBorrow.lookup entered.leases 1 :=
  (iteration entered slice 3).lookup 1 (by decide)
private def endedHeader : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute entered (.endBorrow 1)).getD NativeReferenceMachine.empty
private def afterRevocation := NativeByteDropTraversal.run endedHeader slice
-- Historical registers and births do not revive an ended lease.
example : NativeByteBorrow.lookup afterRevocation.world.leases 0 = none := by
  change NativeByteBorrow.lookup (NativeByteDropTraversal.run endedHeader slice).world.leases 0 = none
  rw [(run endedHeader slice).lookup 0 (by decide)]
  decide
example : (NativeReferenceMachine.Reference.mk 0) ∈ afterRevocation.world.references :=
  (run endedHeader slice).references ⟨0⟩ (by decide)
private def endedData : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute entered (.endBorrow 0)).getD NativeReferenceMachine.empty
example : ¬ Preserves entered endedData := by
  intro preserved
  have lookup := preserved.lookup 1 (by decide)
  have removed : NativeByteBorrow.lookup endedData.leases 1 = none := by decide
  have present : NativeByteBorrow.lookup entered.leases 1 = some dataLease := by decide
  rw [removed,present] at lookup
  cases lookup
-- Loan preservation alone does not assert that a memory write was absent.
private def written : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute entered (.access 0 0 (.writeBytes 1 [6]))).getD NativeReferenceMachine.empty
example : Preserves entered written := step entered written (.access 0 0 (.writeBytes 1 [6])) (by decide)
example : written.pointers.heap ≠ entered.pointers.heap := by decide
end FormalProof4FHETest.HasteBootsIncomingReferenceSmoke
