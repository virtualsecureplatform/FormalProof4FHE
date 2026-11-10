module
public import FormalProof4FHE.HasteBoots.PrivateSampling
public import FormalProof4FHE.HasteBoots.SharedContinuation
@[expose] public section

/-! Ordered private draws with arbitrary shared work before and after each
draw. A fixed coordinate's event is bounded by one fresh draw, without a
losslessness premise on callbacks or a reset of the shared oracle state.
Production transcript-derived challenges remain a separate refinement. -/
open OracleSpec OracleComp BinaryTree
namespace FormalProof4FHE.HasteBoots.OrderedPrivateDraws
noncomputable section
variable {A Memory Cfg Input Digest Payload : Type} [SampleableType A]

abbrev Shared (Cfg Input Digest : Type) := CheckpointExecution.Spec unifSpec Cfg Input Digest

def program (beforeDraw : ℕ → Memory → OracleComp (Shared Cfg Input Digest) Memory)
    (afterDraw : ℕ → Memory → A → OracleComp (Shared Cfg Input Digest) Memory) :
    (count : ℕ) → ℕ → Memory → OracleComp (Shared Cfg Input Digest) ((Fin count → A) × Memory)
  | 0, _, memory => pure (Fin.elim0,memory)
  | count+1, offset, memory => do
    let ready ← beforeDraw offset memory
    let value ← PrivateSampling.embed Cfg Input Digest ($ᵗ A)
    let updated ← afterDraw offset ready value
    let tail ← program beforeDraw afterDraw count (offset+1) updated
    pure (Fin.cons value tail.1,tail.2)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

theorem run_succ (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (beforeDraw : ℕ → Memory → OracleComp (Shared Cfg Input Digest) Memory)
    (afterDraw : ℕ → Memory → A → OracleComp (Shared Cfg Input Digest) Memory)
    (count offset : ℕ) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program beforeDraw afterDraw (count+1) offset memory)).run state = (do
      let ready ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (beforeDraw offset memory)).run state
      let value ← $ᵗ A
      let updated ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (afterDraw offset ready.1 value)).run ready.2
      let tail ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program beforeDraw afterDraw count (offset+1) updated.1)).run updated.2
      pure ((Fin.cons value tail.1.1,tail.1.2),tail.2)) := by
  simp only [program,simulateQ_bind,StateT.run_bind,PrivateSampling.run_probComp,
    bind_map_left,simulateQ_pure,StateT.run_pure]

/-- Selection is fixed before the draws. Earlier adaptive callbacks and every
later callback retain their real calls but cannot amplify this coordinate's
fresh-draw event. No independence between callbacks is asserted. -/
theorem selected_event_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (beforeDraw : ℕ → Memory → OracleComp (Shared Cfg Input Digest) Memory)
    (afterDraw : ℕ → Memory → A → OracleComp (Shared Cfg Input Digest) Memory)
    (count offset : ℕ) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (selected : Fin count) (event : A → Prop) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program beforeDraw afterDraw count offset memory)).run state}[event (outcome.1.1 selected)] ≤
    Pr{let value ← $ᵗ A}[event value] := by
  induction count generalizing offset memory state with
  | zero => exact Fin.elim0 selected
  | succ count ih =>
    rw [run_succ]
    apply prEvent_bind_le_of_forall_le
    intro ready
    refine Fin.cases ?_ (fun index => ?_) selected
    · apply prEvent_bind_le_prEvent_of_forall_eq_zero ($ᵗ A) _ event
      intro value outside
      simp only [prEvent_norm,Fin.cons_zero,outside]
      have vanish := prEvent_false (do
        let updated ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (afterDraw offset ready.1 value)).run ready.2
        (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (program beforeDraw afterDraw count (offset+1) updated.1)).run updated.2)
      simpa only [prEvent_norm] using vanish
    · apply prEvent_bind_le_of_forall_le
      intro value
      apply prEvent_bind_le_of_forall_le
      intro updated
      simpa only [prEvent_norm,Fin.cons_succ] using ih (offset+1) updated.1 updated.2 index
end
end FormalProof4FHE.HasteBoots.OrderedPrivateDraws
