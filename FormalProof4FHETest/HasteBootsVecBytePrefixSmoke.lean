module
import FormalProof4FHE.HasteBoots.NativeVecBytePrefix
namespace FormalProof4FHETest.HasteBootsVecBytePrefixSmoke
open FormalProof4FHE.HasteBoots
open NativeResidentVec
open NativeVecBytePrefix
private def buffer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def header : NativePointerStorage.Pointer := ⟨128,some ⟨128,1⟩⟩
private def headerLease : NativeByteBorrow.Lease := ⟨0,none,header,⟨24,8⟩,.exclusive⟩
private def operations : List NativeReferenceMachine.Op :=
  [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 [10,20]),.raw (.allocate 128 ⟨24,8⟩),
   .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),.raw (.store 0 2),
   .raw (.withAddress 1 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 2)),.borrow 2 .exclusive ⟨24,8⟩]
private def world := (NativeReferenceMachine.run NativeReferenceMachine.empty operations).getD NativeReferenceMachine.empty
private theorem reachable : NativeReferenceMachine.Reachable world := NativeReferenceMachine.run_reachable _ _ .empty operations (by decide)
private def descriptor : Descriptor world 0 where
  reference := ⟨0⟩
  lease := headerLease
  resident := by decide
  registered := by decide
  baseResident := by decide
  exclusive := rfl
  extent := rfl
  capacitySlot := header
  pointerSlot := ⟨136,some ⟨128,1⟩⟩
  lengthSlot := ⟨144,some ⟨128,1⟩⟩
  capacityAt := by decide
  pointerAt := by decide
  lengthAt := by decide
  capacity := 8
  length := 2
  buffer := buffer
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
private theorem initialized : InitializedElements descriptor := ⟨[10,20],by decide⟩
private theorem available : Available world buffer 8 := by
  intro lease member
  have leases : world.leases = [headerLease] := by decide
  rw [leases] at member
  have same := List.mem_singleton.mp member
  subst lease
  decide
private theorem frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease :=
  NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl
example : NativeVecReference.readField world (.reference true descriptor.reference 3) .pointer =
    .value (.raw ⟨buffer,none⟩) (pointerWorld descriptor) :=
  pointer_field_complete descriptor (NativeReferenceMachine.reachable_wellFormed _ reachable).2.1 frontier
example : NativeVecReference.readField (pointerWorld descriptor) (.reference true descriptor.reference 3) .length =
    .value (.usize 2) (lengthWorld descriptor) :=
  length_field_complete descriptor (NativeReferenceMachine.reachable_wellFormed _ reachable).2.1 frontier
example : ∃ next, NativeSliceLLBC.issue (lengthWorld descriptor) true (.raw ⟨buffer,some 2⟩) .byte =
    some (.reference true ⟨world.nextTag⟩ 2,next) ∧ NativeByteTraversalCompleteness.Ready next ⟨⟨world.nextTag⟩,2⟩ :=
  fields_issue_ready descriptor reachable initialized available frontier
example : (lengthWorld descriptor).pointers.registers[1]? = some buffer ∧
    (lengthWorld descriptor).outputs[0]? = some (NativeWord64Memory.encode 2) := by decide
example : NativeByteRange.loadRange world.pointers.heap.memory buffer ⟨8,1⟩ = none ∧
    NativeByteRange.loadRange world.pointers.heap.memory buffer ⟨2,1⟩ = some [10,20] := by decide
example : NativeReferenceCleanup.closeScope world (lengthWorld descriptor) = ⟨lengthWorld descriptor,[],[]⟩ :=
  length_scope descriptor (NativeReferenceMachine.reachable_wellFormed _ reachable).2.1
private def blocked := (NativeReferenceMachine.execute world
  (.borrow (world.pointers.registers.idxOf buffer) .shared ⟨1,1⟩)).getD NativeReferenceMachine.empty
example : NativeSliceLLBC.issue blocked true (.raw ⟨buffer,some 2⟩) .byte = none := by decide
example : ¬ Available blocked buffer 8 := by
  intro separation
  apply separation ⟨1,none,buffer,⟨1,1⟩,.shared⟩ (by decide)
  decide
private def emptyWorld := (NativeReferenceMachine.execute NativeReferenceMachine.empty (.raw (.fromAddress 1))).getD NativeReferenceMachine.empty
example : ∃ next, NativeSliceLLBC.issue emptyWorld true (.raw ⟨⟨1,none⟩,some 0⟩) .byte =
    some (.reference true ⟨0⟩ 0,next) ∧ NativeByteTraversalCompleteness.Ready next ⟨⟨0⟩,0⟩ := by
  apply raw_issue_ready emptyWorld ⟨1,none⟩ 0 (.step .empty (.raw (.fromAddress 1)) (by decide)) (by decide) ?_ [] (by decide)
  intro lease member
  cases member
end FormalProof4FHETest.HasteBootsVecBytePrefixSmoke
