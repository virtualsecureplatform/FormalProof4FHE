namespace HasteBootsVecDrop.ExecutionSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeRecordLLBC (Flow)

-- Rejected entry preserves every caller state, without requiring reachability.
example (world : NativeReferenceMachine.State) : execute world [] = .invalid world := by
  symm
  apply (invocation_iff_execute world [] (.invalid world)).mp
  exact .initialInvalid [] rfl rfl

example (world : NativeReferenceMachine.State) : execute world [.unit] = .invalid world := by
  symm
  apply (invocation_iff_execute world [.unit] (.invalid world)).mp
  exact .initialInvalid [.scalar .unit] rfl rfl

-- An arbitrary replacement loop is not executed as the retained byte loop.
private def changedLoop : NativeByteLoopLLBC.Function := {HasteBootsVecByteLoop.f6 with body := .done}
example : sourceLoops (.loop .transparent changedLoop) = false := by decide
example (frame : NativeRecordLLBC.Frame) : evalCode (.loop .transparent changedLoop) frame = none := by
  have different : changedLoop ≠ HasteBootsVecByteLoop.f6 := by decide
  simp only [evalCode, different, ite_false]

private def invalidFrame : NativeRecordLLBC.Frame := ⟨[.scalar .unit],[.dead],NativeReferenceMachine.empty⟩
example : evalCode (.loop .transparent HasteBootsVecByteLoop.f6) invalidFrame = some (.invalid NativeReferenceMachine.empty) := by decide

-- Zero length executes no dereference; a positive extent with no parent rejects.
example (world : NativeReferenceMachine.State) : loopOutcome world ⟨⟨999⟩,0⟩ = .returned (.scalar .unit) world := by
  simp [loopOutcome, NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]

example : loopOutcome NativeReferenceMachine.empty ⟨⟨999⟩,1⟩ = .invalid NativeReferenceMachine.empty := by
  simp [loopOutcome, NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom,
    NativeByteDropTraversal.iteration, NativeSliceLLBC.issue, NativeByteBorrow.lookup,
    NativeReferenceMachine.empty]

-- A supplied terminal outcome must agree with the computed outcome, so unit
-- success and rejection cannot coexist even when their final heaps coincide.
example (world final : NativeReferenceMachine.State) (args : List NativeRecordLLBC.Input)
    (accepted : Invokes f1 world args (.returned (.scalar .unit) final)) :
    ¬ Invokes f1 world args (.invalid final) := by
  intro rejected
  have impossible := invokes_deterministic f1 world args _ _ accepted rejected
  cases impossible

end HasteBootsVecDrop.ExecutionSmoke
