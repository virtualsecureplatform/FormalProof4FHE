module
import FormalProof4FHE.HasteBoots.NativeByteTraversalCompleteness
namespace FormalProof4FHETest.HasteBootsTraversalCompletenessSmoke
open FormalProof4FHE.HasteBoots
open NativeByteTraversalCompleteness
private def pointer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def operations : List NativeReferenceMachine.Op :=
  [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 [10,20,30]),.borrow 0 .exclusive ⟨3,1⟩]
private def world : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty operations).getD NativeReferenceMachine.empty
private def slice : NativeByteSliceIndex.Slice := ⟨⟨0⟩,3⟩
private def lease : NativeByteBorrow.Lease := ⟨0,none,pointer,⟨3,1⟩,.exclusive⟩
private theorem reachable : NativeReferenceMachine.Reachable world :=
  NativeReferenceMachine.run_reachable _ _ .empty operations (by decide)
private theorem ready : Ready world slice := by
  refine ⟨reachable,lease,by decide,by decide,by decide,rfl,?_,[10,20,30],by decide⟩
  exact NativeBorrowFrontier.singleton_frontier _ lease (by decide) rfl
example : ∃ next, NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte =
    some (.reference true ⟨world.nextTag⟩ slice.length,next) ∧ Ready next ⟨⟨world.nextTag⟩,slice.length⟩ :=
  issue_complete world slice ready
example : ∃ pointer next, NativeByteSliceIndex.index world slice 1 = .value ⟨world.nextTag⟩ next ∧
    NativeByteSliceIndex.rawByte next ⟨world.nextTag⟩ = some pointer := index_raw_complete world slice ready 1 (by decide)
example : ∃ pointer next, NativeByteDropTraversal.iteration world slice 1 = .value pointer next ∧
    Ready next slice ∧ next.leases = world.leases := iteration_complete world slice ready 1 (by decide)
example : (NativeByteDropTraversal.run world slice).complete = true ∧
    (NativeByteDropTraversal.run world slice).world.leases = world.leases ∧
    (NativeByteDropTraversal.run world slice).cursor = 3 := by
  have result := run_complete world slice ready
  exact ⟨result.1,result.2.2.1,result.2.2.2⟩
private def after0 := (NativeByteDropTraversal.iteration world slice 0).world
private def after1 := (NativeByteDropTraversal.iteration after0 slice 1).world
private def after2 := (NativeByteDropTraversal.iteration after1 slice 2).world
private theorem computed : NativeByteDropTraversal.run world slice = ⟨after2,3,some ⟨66,some ⟨64,0⟩⟩,true⟩ := by
  symm
  apply NativeByteDropTraversal.executes_result
  apply NativeByteDropTraversal.Executes.next 0 world after0 none ⟨64,some ⟨64,0⟩⟩ _ (by decide) (by decide)
  apply NativeByteDropTraversal.Executes.next 1 after0 after1 (some ⟨64,some ⟨64,0⟩⟩) ⟨65,some ⟨64,0⟩⟩ _ (by decide) (by decide)
  apply NativeByteDropTraversal.Executes.next 2 after1 after2 (some ⟨65,some ⟨64,0⟩⟩) ⟨66,some ⟨64,0⟩⟩ _ (by decide) (by decide)
  exact .stop 3 after2 (some ⟨66,some ⟨64,0⟩⟩) rfl
example : (NativeByteDropTraversal.run world slice).world.nextTag = 7 ∧
    (NativeByteDropTraversal.run world slice).world.leases.map NativeByteBorrow.Lease.tag = [0] := by rw [computed]; decide
example : (NativeByteDropTraversal.run (NativeByteDropTraversal.run world slice).world slice).complete = true :=
  (run_complete _ slice (run_complete world slice ready).2.1).1
private def revoked := (NativeReferenceMachine.execute world (.endBorrow 0)).getD NativeReferenceMachine.empty
private theorem revokedComputed : NativeByteDropTraversal.run revoked slice = ⟨revoked,0,none,false⟩ := by
  symm
  apply NativeByteDropTraversal.executes_result
  exact .fail 0 revoked revoked none (by decide) (by decide)
example : (NativeByteDropTraversal.run revoked slice).complete = false := by rw [revokedComputed]
private def emptyOps : List NativeReferenceMachine.Op := [.raw (.allocate 64 ⟨8,1⟩),.borrow 0 .exclusive ⟨0,1⟩]
private def emptyWorld := (NativeReferenceMachine.run NativeReferenceMachine.empty emptyOps).getD NativeReferenceMachine.empty
private theorem emptyReady : Ready emptyWorld ⟨⟨0⟩,0⟩ := by
  refine ⟨NativeReferenceMachine.run_reachable _ _ .empty emptyOps (by decide),⟨0,none,pointer,⟨0,1⟩,.exclusive⟩,
    by decide,by decide,by decide,rfl,?_,[],by decide⟩
  exact NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl
example : (NativeByteDropTraversal.run emptyWorld ⟨⟨0⟩,0⟩).complete = true ∧
    (NativeByteDropTraversal.run emptyWorld ⟨⟨0⟩,0⟩).world.leases = emptyWorld.leases :=
  ⟨(run_complete _ _ emptyReady).1,(run_complete _ _ emptyReady).2.2.1⟩
end FormalProof4FHETest.HasteBootsTraversalCompletenessSmoke
