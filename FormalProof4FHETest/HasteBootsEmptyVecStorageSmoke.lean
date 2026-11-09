module
import FormalProof4FHE.HasteBoots.NativeEmptyVecStorage
namespace FormalProof4FHETest.HasteBootsEmptyVecStorageSmoke
open FormalProof4FHE.HasteBoots
open NativeEmptyVecStorage
private def allocated : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 128 ⟨24,8⟩)]).getD NativeReferenceMachine.empty
private theorem allocatedReachable : NativeReferenceMachine.Reachable allocated :=
  NativeReferenceMachine.run_reachable _ _ .empty [.raw (.allocate 128 ⟨24,8⟩)] (by decide)
private theorem separated : NativeVecBytePrefix.Available allocated ⟨128,some ⟨128,0⟩⟩ 24 := by
  intro lease member
  cases member
example : NativeByteRange.loadRange allocated.pointers.heap.memory ⟨128,some ⟨128,0⟩⟩ ⟨24,8⟩ = none := by decide
example : ∃ next, ∃ ready : Ready next,
    install allocated 0 = some next ∧ NativeReferenceMachine.Reachable next ∧
    next.pointers.registers = allocated.pointers.registers ∧ next.leases = ready.descriptor.lease :: allocated.leases ∧
    next.references = ⟨allocated.nextTag⟩ :: allocated.references ∧ ready.descriptor.reference = ⟨allocated.nextTag⟩ :=
  install_complete allocated 0 ⟨128,some ⟨128,0⟩⟩ allocatedReachable (by decide) (by decide) separated
example (next : NativeReferenceMachine.State) (installed : install allocated 0 = some next) :
    ∃ ready : Ready next, NativeResidentVec.InitializedElements ready.descriptor ∧
      NativeResidentVec.OwnsBuffer ready.descriptor ∧
      NativeVecBytePrefix.Available next ready.descriptor.buffer ready.descriptor.capacity.val := by
  obtain ⟨actual,ready,expected,_,_,_,_,_⟩ :=
    install_complete allocated 0 ⟨128,some ⟨128,0⟩⟩ allocatedReachable (by decide) (by decide) separated
  have same := Option.some.inj (expected.symm.trans installed)
  subst next
  exact ⟨ready,ready.initialized,ready.owned,ready.available⟩
private def installed : NativeReferenceMachine.State := (install allocated 0).getD NativeReferenceMachine.empty
example : install installed 0 = none := by decide
private def noOrigin : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run allocated [.raw (.fromAddress 128)]).getD NativeReferenceMachine.empty
example : noOrigin.pointers.registers[0]? = some ⟨128,none⟩ ∧ install noOrigin 0 = none := by decide
private def unaligned : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run allocated [.raw (.withAddress 0 129)]).getD NativeReferenceMachine.empty
example : install unaligned 0 = none := by decide
private def loanedOps : List NativeReferenceMachine.Op :=
  [.raw (.allocate 64 ⟨8,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
    .borrow 0 .shared ⟨8,8⟩,.raw (.allocate 128 ⟨24,8⟩)]
private def loaned : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty loanedOps).getD NativeReferenceMachine.empty
private theorem loanedReachable : NativeReferenceMachine.Reachable loaned :=
  NativeReferenceMachine.run_reachable _ _ .empty loanedOps (by decide)
example : loaned.leases.length = 1 ∧ ∃ next, ∃ ready : Ready next,
    install loaned 0 = some next ∧ NativeReferenceMachine.Reachable next ∧
    next.pointers.registers = loaned.pointers.registers ∧ next.leases = ready.descriptor.lease :: loaned.leases ∧
    next.references = ⟨loaned.nextTag⟩ :: loaned.references ∧ ready.descriptor.reference = ⟨loaned.nextTag⟩ :=
  ⟨by decide,install_complete loaned 0 ⟨128,some ⟨128,1⟩⟩ loanedReachable (by decide) (by decide) (by
    intro lease member
    have same : lease = ⟨0,none,⟨64,some ⟨64,0⟩⟩,⟨8,8⟩,.shared⟩ := List.mem_singleton.mp member
    subst lease
    decide)⟩
end FormalProof4FHETest.HasteBootsEmptyVecStorageSmoke
