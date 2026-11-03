module

public import FormalProof4FHE.HasteBoots.ShortCircuitSequence

@[expose] public section

/-!
# Successful sequential verification preserves the actual result accumulator

An invariant relates retained private memory to the entire ordered attempted
trace. Only the real step transition establishes it; no guessed final result
or acceptance flag is supplied. Failed paths still execute the same program.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.ShortCircuitAccumulator

noncomputable section

variable {Index Memory Result Cfg Input Digest Payload : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Trace/memory invariants propagate through every successful actual step.
An overall successful suffix excludes a rejected head before using its invariant. -/
theorem accepted_invariant (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Result Memory))
    (invariant : List (Index × Result) → Memory → Prop)
    (transition : ∀ history memory, invariant history memory → ∀ index initial result,
      result ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (step index memory)).run initial) → result.1.accepted = true →
      invariant (history ++ [(index, result.1.result)]) result.1.memory)
    (indices : List Index) (history : List (Index × Result)) (memory : Memory)
    (initialInvariant : invariant history memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.Outcome Index Result Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (ShortCircuitSequence.program step indices memory)).run before)) (accepted : outcome.1.accepted = true) :
    invariant (history ++ outcome.1.results) outcome.1.memory := by
  induction indices generalizing history memory before outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    simpa only [List.append_nil] using initialInvariant
  | cons index rest ih =>
    rw [ShortCircuitSequence.program_cons, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
    obtain ⟨packet, packetSupported, equal⟩ := supported
    subst outcome
    obtain ⟨first, firstSupported, later, laterSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy shape (step index memory)
        (fun first => if first.accepted then ShortCircuitSequence.program step rest first.memory
          else pure ⟨[], first.memory, false⟩) before packet).mp packetSupported
    subst packet
    cases flag : first.1.accepted with
    | false =>
      simp only [flag, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at laterSupported
      have equal := eq_of_mem_support_pure _ laterSupported
      subst later
      exact (Bool.false_ne_true accepted).elim
    | true =>
      simp only [flag, reduceIte] at laterSupported
      have head := transition history memory initialInvariant index before first firstSupported flag
      have tail := ih (history ++ [(index, first.1.result)]) first.1.memory head first.2 later laterSupported accepted
      simpa only [List.append_assoc, List.singleton_append] using tail

end

end FormalProof4FHE.HasteBoots.ShortCircuitAccumulator
