module
import FormalProof4FHE.HasteBoots.NativeBorrowFrontier
namespace FormalProof4FHETest.HasteBootsBorrowFrontierSmoke
open FormalProof4FHE.HasteBoots
open NativeBorrowFrontier
private def pointer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def memory : NativeByteMemory.State :=
  ⟨1,[⟨⟨64,0⟩,64,⟨8,1⟩,[some 10,some 20,some 30,some 40,none,none,none,none]⟩]⟩
private def parent : NativeByteBorrow.Lease := ⟨0,none,pointer,⟨4,1⟩,.exclusive⟩
private def ready : NativeByteBorrow.State := ⟨memory,1,[parent]⟩
private theorem memoryValid : NativeByteMemory.WellFormed memory := by
  simp only [NativeByteMemory.WellFormed,memory,List.mem_singleton,forall_eq,
    List.pairwise_singleton,and_true,NativeByteMemory.Block.Valid]
  decide
private theorem valid : NativeByteBorrow.WellFormed ready := by
  refine ⟨memoryValid,?_⟩
  simp only [NativeByteBorrow.LedgerValid,ready,List.mem_singleton,forall_eq,List.pairwise_singleton,and_true,parent]
  exact ⟨by decide,by decide⟩
private theorem available : ExclusiveFrontier ready parent := singleton_frontier ready parent rfl rfl
private def child : NativeByteBorrow.Lease := ⟨1,some 0,⟨65,some ⟨64,0⟩⟩,⟨2,1⟩,.exclusive⟩
private def afterChild : NativeByteBorrow.State := ⟨memory,2,[child,parent]⟩
private theorem borrowed : NativeByteBorrow.borrow ready (some 0) .exclusive child.pointer child.layout = some (1,afterChild) := by decide
private theorem childAvailable : ExclusiveFrontier afterChild child :=
  borrow_frontier ready afterChild valid.2 parent available child.pointer child.layout 1 borrowed
private theorem childValid : NativeByteBorrow.WellFormed afterChild :=
  NativeByteBorrow.borrow_wellFormed ready valid (some 0) .exclusive child.pointer child.layout 1 afterChild borrowed
example : ∃ shifted next, NativeByteRange.pointerAt parent.pointer 1 = some shifted ∧
    NativeByteBorrow.borrow ready (some parent.tag) .exclusive shifted ⟨2,1⟩ = some (ready.nextTag,next) ∧
    ExclusiveFrontier next ⟨ready.nextTag,some parent.tag,shifted,⟨2,1⟩,.exclusive⟩ :=
  borrow_subrange ready valid parent available 4 1 2 rfl [10,20,30,40] (by decide) (by decide)
example : ExclusiveFrontier afterChild child := childAvailable
example : NativeByteBorrow.parentAllowed afterChild (some parent.tag) .exclusive parent.pointer parent.layout = false := by decide
example : NativeByteBorrow.parentAllowed afterChild (some child.tag) .exclusive ⟨66,some ⟨64,0⟩⟩ ⟨1,1⟩ = true :=
  parent_allowed afterChild childValid.2 child childAvailable .exclusive _ _ (by exact ⟨rfl,by decide,by decide⟩)
example : NativeByteBorrow.parentAllowed afterChild (some child.tag) .shared child.pointer child.layout = true :=
  parent_allowed afterChild childValid.2 child childAvailable .shared child.pointer child.layout
    (by exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩)
private def grandchild : NativeByteBorrow.Lease := ⟨2,some 1,⟨66,some ⟨64,0⟩⟩,⟨1,1⟩,.exclusive⟩
private def afterGrandchild : NativeByteBorrow.State := ⟨memory,3,[grandchild,child,parent]⟩
example : ExclusiveFrontier afterGrandchild grandchild :=
  borrow_frontier afterChild afterGrandchild childValid.2 child childAvailable grandchild.pointer grandchild.layout 2 (by decide)
private def conflicting : NativeByteBorrow.State :=
  ⟨memory,3,[⟨2,none,⟨66,some ⟨64,0⟩⟩,⟨1,1⟩,.shared⟩,parent]⟩
private theorem conflictLedger : NativeByteBorrow.LedgerValid conflicting := by
  constructor
  · intro lease member
    rcases List.mem_cons.mp member with same | later
    · subst lease
      exact ⟨by decide,by decide,trivial⟩
    · have same := List.mem_singleton.mp later
      subst lease
      exact ⟨by decide,by decide,trivial⟩
  · decide
example : NativeByteBorrow.parentAllowed conflicting (some parent.tag) .exclusive parent.pointer parent.layout = false := by decide
example : ¬ ExclusiveFrontier conflicting parent := by
  intro frontier
  have allowed := parent_allowed conflicting conflictLedger parent frontier .exclusive pointer ⟨4,1⟩ (by exact ⟨rfl,by decide,by decide⟩)
  have blocked : NativeByteBorrow.parentAllowed conflicting (some parent.tag) .exclusive pointer ⟨4,1⟩ = false := by decide
  rw [blocked] at allowed
  cases allowed
example : ∃ shifted next, NativeByteRange.pointerAt parent.pointer 4 = some shifted ∧
    NativeByteBorrow.borrow ready (some parent.tag) .exclusive shifted ⟨0,1⟩ = some (ready.nextTag,next) ∧
    ExclusiveFrontier next ⟨ready.nextTag,some parent.tag,shifted,⟨0,1⟩,.exclusive⟩ :=
  borrow_subrange ready valid parent available 4 4 0 rfl [10,20,30,40] (by decide) (by decide)
private def nativeWorld : NativeReferenceMachine.State :=
  ⟨⟨⟨memory,[]⟩,[pointer],[]⟩,1,[parent],[⟨0⟩],[parent],[]⟩
example : ∃ shifted next, NativeByteRange.pointerAt parent.pointer 1 = some shifted ∧
    NativeReferenceMachine.grant nativeWorld (some parent.tag) .exclusive shifted ⟨2,1⟩ = some next ∧
    ExclusiveFrontier (NativeReferenceMachine.ledger next) ⟨nativeWorld.nextTag,some parent.tag,shifted,⟨2,1⟩,.exclusive⟩ :=
  grant_subrange nativeWorld valid parent available 4 1 2 rfl [10,20,30,40] (by decide) (by decide)
example : (NativeReferenceMachine.grant nativeWorld (some 0) .exclusive child.pointer child.layout).map
    (fun next => (next.references.map NativeReferenceMachine.Reference.tag,next.births.map NativeByteBorrow.Lease.tag,next.nextTag)) =
      some ([1,0],[1,0],2) := by decide
example : ∃ shifted next, NativeByteSliceIndex.index nativeWorld ⟨⟨0⟩,4⟩ 2 = .value ⟨nativeWorld.nextTag⟩ next ∧
    NativeByteRange.pointerAt parent.pointer 2 = some shifted ∧
    ExclusiveFrontier (NativeReferenceMachine.ledger next) ⟨nativeWorld.nextTag,some parent.tag,shifted,⟨1,1⟩,.exclusive⟩ :=
  index_complete nativeWorld valid ⟨⟨0⟩,4⟩ parent (by decide) (by decide) (by decide) rfl available
    [10,20,30,40] (by decide) 2 (by decide)
end FormalProof4FHETest.HasteBootsBorrowFrontierSmoke
