module
import FormalProof4FHE.HasteBoots.NativeRawVecDeallocationCompleteness
namespace FormalProof4FHETest.HasteBootsByteRangeCompletenessSmoke
open FormalProof4FHE.HasteBoots
open NativeByteRangeCompleteness
private def pointer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def memory : NativeByteMemory.State :=
  ⟨1,[⟨⟨64,0⟩,64,⟨8,1⟩,[some 10,some 20,some 30,some 40,none,none,none,none]⟩]⟩
private theorem valid : NativeByteMemory.WellFormed memory := by
  simp only [NativeByteMemory.WellFormed,memory,List.mem_singleton,forall_eq,
    List.pairwise_singleton,and_true,NativeByteMemory.Block.Valid]
  decide
example : ∃ shifted, NativeByteRange.pointerAt pointer 1 = some shifted ∧
    NativeByteRange.loadRange memory shifted ⟨2,1⟩ = some [20,30] :=
  loadRange_subrange memory valid pointer 4 1 2 [10,20,30,40] (by decide) (by decide)
example : ∃ shifted, NativeByteRange.pointerAt pointer 4 = some shifted ∧
    NativeByteRange.loadRange memory shifted ⟨0,1⟩ = some [] :=
  loadRange_subrange memory valid pointer 4 4 0 [10,20,30,40] (by decide) (by decide)
example : NativeByteRange.loadRange memory ⟨68,some ⟨64,0⟩⟩ ⟨1,1⟩ = none := by decide
example : NativeByteRange.loadRange memory ⟨pointer.address,none⟩ ⟨4,1⟩ = none := by decide
example : ∃ shifted, NativeByteRange.pointerAt ⟨1,none⟩ 0 = some shifted ∧
    NativeByteRange.loadRange NativeByteMemory.empty shifted ⟨0,1⟩ = some [] :=
  loadRange_subrange _ NativeByteMemory.empty_wellFormed ⟨1,none⟩ 0 0 0 [] (by decide) (by decide)
private def operations : List NativeReferenceMachine.Op :=
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 [10,20]),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),.raw (.store 0 2),
     .raw (.withAddress 1 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 2)),.borrow 2 .exclusive ⟨24,8⟩]
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty operations).getD NativeReferenceMachine.empty
private theorem readyMemory : NativeByteMemory.WellFormed ready.pointers.heap.memory :=
  (NativeReferenceMachine.run_wellFormed operations ready (by decide)).1.1
private def descriptor : NativeResidentVec.Descriptor ready 0 where
  reference := ⟨0⟩
  lease := ⟨0,none,⟨128,some ⟨128,1⟩⟩,⟨24,8⟩,.exclusive⟩
  resident := by decide
  registered := by decide
  baseResident := by decide
  exclusive := rfl
  extent := rfl
  capacitySlot := ⟨128,some ⟨128,1⟩⟩
  pointerSlot := ⟨136,some ⟨128,1⟩⟩
  lengthSlot := ⟨144,some ⟨128,1⟩⟩
  capacityAt := by decide
  pointerAt := by decide
  lengthAt := by decide
  capacity := 8
  length := 2
  buffer := pointer
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
private theorem initialized : NativeResidentVec.InitializedElements descriptor := ⟨[10,20],by decide⟩
example : ∃ shifted byte, NativeByteRange.pointerAt descriptor.buffer 1 = some shifted ∧
    NativeByteRange.loadRange ready.pointers.heap.memory shifted ⟨1,1⟩ = some [byte] :=
  initialized.byte readyMemory 1 (by decide)
example : ∃ shifted bytes, NativeByteRange.pointerAt descriptor.buffer 2 = some shifted ∧
    NativeByteRange.loadRange ready.pointers.heap.memory shifted ⟨0,1⟩ = some bytes :=
  initialized.subrange readyMemory 2 0 (by decide)
example : NativeByteRange.loadRange ready.pointers.heap.memory ⟨66,some ⟨64,0⟩⟩ ⟨1,1⟩ = none := by decide
example : ∃ bytes, NativeByteRange.loadRange ready.pointers.heap.memory descriptor.lease.pointer
    ⟨24,8⟩ = some bytes := descriptor.header_initialized readyMemory
example : NativeByteRange.readSpan [some 10,some 20,none] (1 + 1) = some ([10] ++ [20]) :=
  readSpan_join _ 1 1 [10] [20] (by decide) (by decide)
example : NativeByteRange.readSpan [some 10,none,some 20] 3 = none := by decide
example : NativeByteRange.loadRange memory pointer ⟨4,1⟩ = some ([10,20] ++ [30,40]) :=
  loadRange_join memory valid pointer ⟨66,some ⟨64,0⟩⟩ 2 2 1 [10,20] [30,40]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : NativeByteRange.loadRange memory ⟨66,some ⟨64,1⟩⟩ ⟨2,1⟩ = none := by decide
example : ∃ next, NativeReferenceMachine.grant ready (some descriptor.lease.tag) .exclusive
      descriptor.lease.pointer ⟨24,8⟩ = some next ∧
    NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger next)
      ⟨ready.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨24,8⟩,.exclusive⟩ := by
  have worldValid := NativeReferenceMachine.run_wellFormed operations ready (by decide)
  apply NativeBorrowFrontier.vec_header_grant_complete ready 0 descriptor
    ⟨worldValid.1.1,worldValid.2.1⟩
  exact NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl
private theorem readyFrontier : NativeBorrowFrontier.ExclusiveFrontier
    (NativeReferenceMachine.ledger ready) descriptor.lease :=
  NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl
private theorem readyReachable : NativeReferenceMachine.Reachable ready :=
  NativeReferenceMachine.run_reachable _ _ .empty operations (by decide)
example : NativeByteRange.loadRange memory pointer ⟨2,1⟩ = some ([10,20,30,40].take 2) :=
  loadRange_prefix memory valid pointer 4 2 1 _ (by decide) (by decide) (by decide)
example : ∃ bytes, NativeByteRange.loadRange ready.pointers.heap.memory descriptor.lease.pointer
    ⟨16,8⟩ = some bytes := descriptor.rawvec_initialized readyMemory
example (target : NativeVecReference.Target) : ∃ next,
    NativeVecReference.reborrow ready (.reference true descriptor.reference 3) target =
      .value (.reference true ⟨ready.nextTag⟩ target.count) next ∧
    NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger next)
      ⟨ready.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,target.layout,.exclusive⟩ ∧
    NativeResidentVecBorrow.Resident next (.reference true ⟨ready.nextTag⟩ target.count)
      descriptor.lease.pointer descriptor.capacity descriptor.length descriptor.buffer := by
  have worldValid := NativeReferenceMachine.reachable_wellFormed ready readyReachable
  exact NativeRawVecBorrowCompleteness.vec_reborrow_complete ready 0 descriptor
    ⟨worldValid.1.1,worldValid.2.1⟩ readyFrontier target
example : ∃ entered next,
    NativeVecReference.reborrow ready (.reference true descriptor.reference 3) .rawVec =
      .value (.reference true ⟨ready.nextTag⟩ 2) entered ∧
    NativeRawVecMutBorrow.immediate entered (.reference true ⟨ready.nextTag⟩ 2) =
      .value (.reference true ⟨entered.nextTag⟩ 2) next ∧
    NativeReferenceMachine.Reachable next ∧ next.pointers.heap = ready.pointers.heap := by
  obtain ⟨entered,next,borrowed,activated,_,_,reached,heap⟩ :=
    NativeRawVecBorrowCompleteness.vec_rawvec_activation_complete ready 0 descriptor readyReachable readyFrontier
  exact ⟨entered,next,borrowed,activated,reached,heap⟩
example : (match NativeVecReference.reborrow ready (.reference true descriptor.reference 3) .rawVec with
    | .invalid _ => none
    | .value operand entered => match NativeRawVecMutBorrow.immediate entered operand with
      | .invalid _ => none
      | .value _ next => some (next.nextTag,next.leases.map NativeByteBorrow.Lease.tag)) =
    some (3,[2,1,0]) := by decide
example : NativeByteRange.loadRange ready.pointers.heap.memory ⟨66,some ⟨64,0⟩⟩ ⟨6,1⟩ = none := by decide
private def rawOperations := operations.dropLast ++ [.borrow 2 .exclusive ⟨16,8⟩]
private def rawWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty rawOperations).getD NativeReferenceMachine.empty
private def rawLease : NativeByteBorrow.Lease := ⟨0,none,⟨128,some ⟨128,1⟩⟩,⟨16,8⟩,.exclusive⟩
private def sharedWorld := (NativeRawVecBorrow.reborrow rawWorld (.reference true ⟨0⟩ 2) .whole).world
private theorem rawReached : NativeReferenceMachine.Reachable rawWorld :=
  NativeReferenceMachine.run_reachable _ _ .empty rawOperations (by decide)
private theorem sharedReached : NativeReferenceMachine.Reachable sharedWorld :=
  NativeRawVecBorrow.reborrow_reachable rawWorld (.reference true ⟨0⟩ 2) .whole rawReached
private theorem rawFrontier : NativeBorrowFrontier.ExclusiveFrontier
    (NativeReferenceMachine.ledger rawWorld) rawLease :=
  NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl
private def sharedHeader : NativeRawVecSharedCompleteness.Header sharedWorld ⟨1⟩ 8 2 pointer where
  lease := ⟨1,some 0,⟨128,some ⟨128,1⟩⟩,⟨16,8⟩,.shared⟩
  valid := (NativeReferenceMachine.reachable_wellFormed sharedWorld sharedReached).2.1
  frontier := NativeRawVecSharedCompleteness.shared_borrow_frontier (NativeReferenceMachine.ledger rawWorld)
    (NativeReferenceMachine.ledger sharedWorld)
    (NativeReferenceMachine.reachable_wellFormed rawWorld rawReached).2.1 rawLease rawFrontier
    rawLease.pointer ⟨16,8⟩ 1 (by decide)
  tag := rfl
  shape := rfl
  referenceResident := by decide
  pointerResident := by decide
  fields := by constructor <;> decide
example : ∃ next, NativeRawVecBorrow.reborrow rawWorld (.reference true ⟨0⟩ 2) .whole =
    .value (.reference false ⟨rawWorld.nextTag⟩ 2) next ∧
    Nonempty (NativeRawVecSharedCompleteness.Header next ⟨rawWorld.nextTag⟩ 8 2 pointer) ∧
    NativeReferenceMachine.Reachable next := by
  apply NativeRawVecSharedCompleteness.rawvec_header_complete rawWorld ⟨0⟩ rawLease 8 2 pointer
    rawReached rawFrontier rfl rfl (by decide) (by decide) (by constructor <;> decide)
    (NativeWord64Memory.encode 8 ++ NativeWord64Memory.encode 64) (by decide)
example : NativeRawVecReference.eval sharedWorld (.reference false ⟨1⟩ 2) .capacity =
    .value (.usize 8) (NativeRawVecSharedCompleteness.wordWorld sharedWorld sharedHeader.lease.pointer 8) :=
  sharedHeader.capacity_eval
example : NativeRawVecReference.eval
    (NativeRawVecSharedCompleteness.wordWorld sharedWorld sharedHeader.lease.pointer 8) (.reference false ⟨1⟩ 2) .capacity =
    .value (.usize 8) (NativeRawVecSharedCompleteness.wordWorld
      (NativeRawVecSharedCompleteness.wordWorld sharedWorld sharedHeader.lease.pointer 8) sharedHeader.lease.pointer 8) :=
  sharedHeader.after_capacity.capacity_eval
example : ∃ next, NativeRawVecReference.eval sharedWorld (.reference false ⟨1⟩ 2) .pointer =
    .value (.raw ⟨pointer,none⟩) next ∧
    Nonempty (NativeRawVecSharedCompleteness.Header next ⟨1⟩ 8 2 pointer) ∧
    next.leases = sharedWorld.leases ∧ next.pointers.heap = sharedWorld.pointers.heap ∧
    pointer ∈ next.pointers.registers := sharedHeader.pointer_eval
example : ∃ next, NativeRawVecReference.eval sharedWorld (.reference false ⟨1⟩ 2) .marker =
    .value .unit next ∧ next.leases = sharedWorld.leases ∧ next.pointers.heap = sharedWorld.pointers.heap :=
  sharedHeader.marker_eval
example : (NativeRawVecReference.eval sharedWorld (.reference false ⟨1⟩ 2) .marker).world.outputs[0]? = some [] := by decide
private def conflictingShared : NativeReferenceMachine.State :=
  {sharedWorld with nextTag := 3,leases := ⟨2,none,⟨128,some ⟨128,1⟩⟩,⟨1,1⟩,.exclusive⟩ :: sharedWorld.leases}
example : NativeRawVecReference.eval conflictingShared (.reference false ⟨1⟩ 2) .capacity =
    .invalid conflictingShared := by decide
private def allocatorWorld :=
  (NativeRawVecBorrow.reborrow sharedWorld (.reference true ⟨0⟩ 2) .allocator).world
private theorem rawAvailable : NativeVecBytePrefix.Available rawWorld pointer 8 := by
  intro lease member
  have only : rawWorld.leases = [rawLease] := by decide
  rw [only] at member
  have same := List.mem_singleton.mp member
  subst lease
  decide
private theorem sharedAvailable : NativeVecBytePrefix.Available sharedWorld pointer 8 :=
  NativeRawVecDeallocationCompleteness.available_reborrow rawWorld sharedWorld pointer 8 (.reference true ⟨0⟩ 2) (.reference false ⟨1⟩ 2) .whole rawAvailable (by decide)
private theorem allocatorAvailable : NativeVecBytePrefix.Available allocatorWorld pointer 8 :=
  NativeRawVecDeallocationCompleteness.available_reborrow sharedWorld allocatorWorld pointer 8 (.reference true ⟨0⟩ 2) (.reference false ⟨2⟩ 0) .allocator sharedAvailable (by decide)
private def bufferBlock : NativeByteMemory.Block :=
  ⟨⟨64,0⟩,64,⟨8,1⟩,[some 10,some 20] ++ List.replicate 6 none⟩
example : ∃ slot next, NativeByteRange.pointerAt rawLease.pointer 16 = some slot ∧
    NativeRawVecBorrow.reborrow sharedWorld (.reference true ⟨0⟩ 2) .allocator =
      .value (.reference false ⟨sharedWorld.nextTag⟩ 0) next ∧ next.nextTag = sharedWorld.nextTag + 1 ∧
    next.leases = ⟨sharedWorld.nextTag,some 0,slot,⟨0,1⟩,.shared⟩ :: sharedWorld.leases ∧
    next.pointers.heap = sharedWorld.pointers.heap :=
  NativeRawVecDeallocationCompleteness.allocator_complete sharedWorld ⟨0⟩ rawLease
    (NativeReferenceMachine.reachable_wellFormed sharedWorld sharedReached).2.1 (by decide) rfl rfl (by decide) (by decide)
example : allocatorWorld.nextTag = 3 ∧ allocatorWorld.leases.map NativeByteBorrow.Lease.tag = [2,1,0] := by decide
example : ∃ next, NativeByteDeallocation.execute allocatorWorld ⟨pointer,none⟩ 8 1 = some next ∧
    NativePointerByteMemory.deallocate allocatorWorld.pointers.heap pointer ⟨8,1⟩ = some next.pointers.heap ∧
    next.leases = allocatorWorld.leases ∧ next.nextTag = allocatorWorld.nextTag :=
  NativeRawVecDeallocationCompleteness.free_complete allocatorWorld pointer 8 (by decide) (by decide) (by decide)
    (by decide) allocatorAvailable bufferBlock (by decide) rfl rfl
example : (NativeByteDeallocation.execute allocatorWorld ⟨pointer,none⟩ 8 1).map
    (fun next => (next.pointers.heap.memory.blocks.length,next.nextTag,next.leases.map NativeByteBorrow.Lease.tag)) =
    some (1,3,[2,1,0]) := by decide
private def protectedAllocatorWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute allocatorWorld
    (.borrow (allocatorWorld.pointers.registers.idxOf pointer) .shared ⟨1,1⟩)).getD allocatorWorld
example : NativeByteDeallocation.execute protectedAllocatorWorld ⟨pointer,none⟩ 8 1 = none := by decide
example : NativeByteRange.loadRange
    ((NativeByteDeallocation.execute allocatorWorld ⟨pointer,none⟩ 8 1).getD allocatorWorld).pointers.heap.memory
    pointer ⟨2,1⟩ = none := by decide
example : (NativeRecordLLBC.settle rawWorld (.returned (.scalar .unit) allocatorWorld)).world.leases.map
    NativeByteBorrow.Lease.tag = [0] := by decide
private def rawReady : NativeRawVecDeallocationCompleteness.Ready rawWorld ⟨0⟩ 8 2 pointer where
  lease := rawLease
  reachable := rawReached
  frontier := rawFrontier
  tag := rfl
  shape := rfl
  referenceResident := by decide
  pointerResident := by decide
  fields := by constructor <;> decide
  initialized := ⟨NativeWord64Memory.encode 8 ++ NativeWord64Memory.encode 64,by decide⟩
example : ∃ next, NativeRawVecMutBorrow.immediate rawWorld (.reference true ⟨0⟩ 2) =
    .value (.reference true ⟨rawWorld.nextTag⟩ 2) next ∧
    Nonempty (NativeRawVecDeallocationCompleteness.Ready next ⟨rawWorld.nextTag⟩ 8 2 pointer) ∧
    next.pointers.heap = rawWorld.pointers.heap := rawReady.immediate_complete
private def immediateWorld := (NativeRawVecMutBorrow.immediate rawWorld (.reference true ⟨0⟩ 2)).world
example : immediateWorld.nextTag = 2 ∧ immediateWorld.leases.map NativeByteBorrow.Lease.tag = [1,0] ∧
    NativeVecBytePrefix.Available immediateWorld pointer 8 := by
  refine ⟨by decide,by decide,?_⟩
  exact NativeRawVecDeallocationCompleteness.available_immediate rawWorld immediateWorld pointer 8
    (.reference true ⟨0⟩ 2) (.reference true ⟨1⟩ 2) rawAvailable (by decide)
end FormalProof4FHETest.HasteBootsByteRangeCompletenessSmoke
