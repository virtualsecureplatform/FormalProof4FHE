namespace HasteBootsByteDeallocationBoundarySmoke
open FormalProof4FHE.HasteBoots
open NativeByteDropCalls HasteBootsByteDeallocationBoundary

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨8,8⟩),.raw (.writeBytes 0 8 (List.replicate 8 0))]).getD NativeReferenceMachine.empty
private def pointer : NativeSliceLLBC.Raw := ⟨⟨⟨64,by decide⟩,some ⟨64,0⟩⟩,none⟩
private def released : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.raw (.free 0 ⟨8,8⟩))).getD ready

example : Invokes boundary ready [.rawRegister 0,.usize ⟨8,by decide⟩,.usize ⟨8,by decide⟩]
    (.returned .unit released) := by
  apply Invokes.run _ _ (.returned .unit released)
  · rfl
  · exact initial_exact ready pointer _ _ rfl
  · exact boundary_execution ready released pointer _ _ (by decide)

example : released.pointers.heap.memory.blocks = [] ∧
    released.pointers.history = ready.pointers.history := by decide

example : Invokes boundary ready [.rawRegister 0,.usize ⟨7,by decide⟩,.usize ⟨8,by decide⟩]
    (.invalid ready) := by
  apply Invokes.run _ _ (.invalid ready)
  · rfl
  · exact initial_exact ready pointer _ _ rfl
  · have executed := Runs.deallocate (entry ready pointer ⟨7,by decide⟩ ⟨8,by decide⟩) [.move 1,.move 2,.move 3]
    exact executed

example : Invokes boundary ready [.usize ⟨64,by decide⟩,.usize ⟨8,by decide⟩,.usize ⟨8,by decide⟩]
    (.invalid ready) := .initialInvalid _ rfl (by decide)

example : Invokes boundary ready [.rawRegister 99,.usize ⟨8,by decide⟩,.usize ⟨8,by decide⟩]
    (.invalid ready) := .argumentsInvalid (by decide)

end HasteBootsByteDeallocationBoundarySmoke
