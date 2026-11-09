module
import FormalProof4FHE.HasteBoots.NativeRecordHeapBounds
namespace FormalProof4FHETest.HasteBootsRecordHeapBoundsSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeHeapLoss (Loss count)
private def leaf : Code := .native (.deallocate .unit .unit .unit 12) .done
private def releaseCall : Code := .call "free" .transparent [] 0 0 [] leaf (.native .resume .done) .done
private def methodCall : Code := .call "method" .transparent [] 0 0 [] (.native .ret .done) (.scope releaseCall (.native .resume .done)) .done
private def continuingMethodCall : Code := .call "method" .transparent [] 0 0 [] (.native .ret .done) releaseCall .done
example : (heapBudget (.scope methodCall releaseCall)).total = 1 := by decide
example : (heapBudget (.scope releaseCall releaseCall)).total = 2 := by decide
example : (heapBudget (.scope continuingMethodCall releaseCall)).total = 2 := by decide
example : NativeRecordLLBC.deallocationBudget (.constIf false (.deallocate .unit .unit .unit 12) (.deallocate .unit .unit .unit 12) .done) = 2 := by decide
example : NativeRecordLLBC.canContinue (.call "leaf" .transparent [] 0 0 [] .done .resume .ret) = false := by decide
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 (List.replicate 8 0))]).getD NativeReferenceMachine.empty
private def written : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.raw (.writeBytes 0 1 [7]))).getD NativeReferenceMachine.empty
-- Equal counts cannot conceal a byte change in a heap-loss certificate.
example : count written = count ready := by decide
example : ¬ Loss ready written 1 := by
  intro bound
  have changed : written.pointers.heap ≠ ready.pointers.heap := by decide
  exact changed (bound.unchanged (by decide))
private def reused : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run ready [.raw (.free 0 ⟨8,1⟩),.raw (.allocate 64 ⟨8,1⟩)]).getD NativeReferenceMachine.empty
-- Free/reallocate cancellation at the same address is excluded too.
example : count reused = count ready := by decide
example : ¬ Loss ready reused 1 := by
  intro bound
  have changed : reused.pointers.heap ≠ ready.pointers.heap := by decide
  exact changed (bound.unchanged (by decide))
private def grew : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.raw (.allocate 128 ⟨8,1⟩))).getD NativeReferenceMachine.empty
example : ¬ Loss ready grew 1 := by
  intro bound
  have old : count ready = 1 := by decide
  have new : count grew = 2 := by decide
  have noGrowth := bound.no_growth
  omega
end FormalProof4FHETest.HasteBootsRecordHeapBoundsSmoke
