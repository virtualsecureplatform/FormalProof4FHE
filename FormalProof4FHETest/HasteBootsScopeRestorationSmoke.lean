module
import FormalProof4FHE.HasteBoots.NativeScopeRestoration
namespace FormalProof4FHETest.HasteBootsScopeRestorationSmoke
open FormalProof4FHE.HasteBoots
open NativeScopeRestoration
private def pointer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def rootLease : NativeByteBorrow.Lease := ⟨0,none,pointer,⟨1,1⟩,.exclusive⟩
private def operations : List NativeReferenceMachine.Op :=
  [.raw (.allocate 64 ⟨1,1⟩),.raw (.writeBytes 0 1 [7]),.borrow 0 .exclusive ⟨1,1⟩]
private def entered := (NativeReferenceMachine.run NativeReferenceMachine.empty operations).getD NativeReferenceMachine.empty
private def first := (NativeReferenceMachine.execute entered (.reborrow 0 0 .exclusive ⟨1,1⟩)).getD NativeReferenceMachine.empty
private def current := (NativeReferenceMachine.execute first (.reborrow 0 0 .exclusive ⟨1,1⟩)).getD NativeReferenceMachine.empty
private def cleaned := NativeReferenceCleanup.closeScope entered current
private theorem enteredReachable : NativeReferenceMachine.Reachable entered :=
  NativeReferenceMachine.run_reachable _ _ .empty operations (by decide)
private theorem currentReachable : NativeReferenceMachine.Reachable current :=
by
  have firstReachable : NativeReferenceMachine.Reachable first :=
    .step enteredReachable (.reborrow 0 0 .exclusive ⟨1,1⟩) (by decide)
  exact .step firstReachable (.reborrow 0 0 .exclusive ⟨1,1⟩) (by decide)
private theorem extended : Extends entered current :=
  (step entered first (.reborrow 0 0 .exclusive ⟨1,1⟩) (by decide)).trans
    (step first current (.reborrow 0 0 .exclusive ⟨1,1⟩) (by decide))
private theorem restored : cleaned.pending = [] ∧ cleaned.world.leases = entered.leases :=
  closeScope_reachable_restores entered current extended (NativeReferenceMachine.reachable_wellFormed entered enteredReachable).2.1 currentReachable
example : NativeReferenceCleanup.scopeTags entered current = [2,1] := by decide
example : cleaned.pending = [] ∧ cleaned.world.leases = entered.leases := restored
example : cleaned.world.nextTag = 3 ∧ cleaned.world.references.map NativeReferenceMachine.Reference.tag = [2,1,0] ∧
    cleaned.world.births.map NativeByteBorrow.Lease.tag = [2,1,0] := by decide
example : NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger current) (some 0) .exclusive pointer ⟨1,1⟩ = false := by decide
example : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger cleaned.world) rootLease :=
  NativeBorrowFrontier.frontier_transport (NativeReferenceMachine.ledger entered) _ rootLease
    (NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl) restored.2
example : (NativeSliceLLBC.issue cleaned.world true (.reference true ⟨0⟩ 1) .byte).map
    (fun (value,next) => (value,next.nextTag)) = some (.reference true ⟨3⟩ 1,4) := by decide
private def ended := (NativeReferenceMachine.execute entered (.endBorrow 0)).getD NativeReferenceMachine.empty
example : ¬ Extends entered ended := by
  intro alleged
  obtain ⟨newer,same,_⟩ := alleged.leases
  have lengths := congrArg List.length same
  have old : entered.leases.length = 1 := by decide
  have gone : ended.leases.length = 0 := by decide
  rw [List.length_append,old,gone] at lengths
  omega
private def written := (NativeReferenceMachine.execute entered (.access 0 0 (.writeBytes 1 [9]))).getD NativeReferenceMachine.empty
example : Extends entered written ∧ written.pointers.heap ≠ entered.pointers.heap :=
  ⟨step entered written (.access 0 0 (.writeBytes 1 [9])) (by decide),by decide⟩
end FormalProof4FHETest.HasteBootsScopeRestorationSmoke
