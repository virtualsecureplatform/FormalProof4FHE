module

public import FormalProof4FHE.HasteBoots.CompletedObservationLimit
public import FormalProof4FHE.HasteBoots.StagedCommitmentPrefix

@[expose] public section

/-!
# Completed observation order on the real staged witness

The original source state is sampled first and retained. The middle starts
only after recording those source roots. Later helper-root recording and
verifier queries retain their actual states and may depend on the whole
middle observation. Nothing moves the original source checkpoint.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.StagedCompletedObservation

noncomputable section

variable {Cfg Input Digest Payload First Second Result : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

abbrev Outcome (shape : Cfg → Skeleton) (First Second Result : Type) :=
  (First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
  (Second × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
  (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)

def complete {shape : Cfg → Skeleton} (done : Second → Prop)
    (outcome : Outcome (Input := Input) (Digest := Digest) shape First Second Result) : Prop := done outcome.2.1.1

/-- Pointwise completed middle order lifts through the actual source commit,
source-root recording, helper-root recording and arbitrary later execution. -/
theorem witness_order (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (left right : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (done : Second → Prop)
    (ordered : ∀ first state, CompletedObservation.LE
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (left first)).run state)
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (right first)).run state)
      (fun second => done second.1)) :
    CompletedObservation.LE
      (StagedCommitmentPrefix.witness enc dummy shape sourceRequests helperRequests sourceCommit left next initial)
      (StagedCommitmentPrefix.witness enc dummy shape sourceRequests helperRequests sourceCommit right next initial)
      (complete done) := by
  unfold StagedCommitmentPrefix.witness
  apply CompletedObservation.bind_same
  intro first
  apply CompletedObservation.bind (ordered first.1 (RecordRoots.state shape (sourceRequests first.1) first.2))
  · intro second _
    exact CompletedObservation.refl _ _
  · intro second suspended
    simp [prEvent_norm, complete, suspended]

/-- A middle completion law independent of the incoming source/state remains
exact after averaging the real source and retaining the whole later result. -/
theorem completion (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (middle : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (done : Second → Prop) (mass : ENNReal)
    (middle_mass : ∀ first state,
      Pr{let second ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (middle first)).run state)}[done second.1] = mass) :
    Pr{let outcome ← StagedCommitmentPrefix.witness enc dummy shape sourceRequests helperRequests sourceCommit middle next initial}[
      complete done outcome] = mass := by
  unfold StagedCommitmentPrefix.witness
  rw [prEvent_bind_eq_tsum]
  apply tsum_prEvent_mul_of_const_on_support
  intro first _
  rw [← middle_mass first.1 (RecordRoots.state shape (sourceRequests first.1) first.2)]
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite]
  apply tsum_congr
  intro second
  by_cases present : done second.1 <;> simp [complete, present, prEvent_norm]


/-- Completion has a uniform conditional mass after each original source,
so its gated source event has precisely that mass times the real source law. -/
theorem source_event (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (middle : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (done : Second → Prop) (mass : ENNReal)
    (middle_mass : ∀ first state,
      Pr{let second ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (middle first)).run state)}[done second.1] = mass)
    (event : First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    Pr{let outcome ← StagedCommitmentPrefix.witness enc dummy shape sourceRequests helperRequests sourceCommit middle next initial}[
      complete done outcome ∧ event outcome.1] =
      Pr{let first ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        sourceCommit).run initial)}[event first] * mass := by
  unfold StagedCommitmentPrefix.witness
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro first
  by_cases present : event first
  · simp only [present, ite_true]
    congr 1
    rw [← middle_mass first.1 (RecordRoots.state shape (sourceRequests first.1) first.2)]
    rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite]
    apply tsum_congr
    intro second
    by_cases finished : done second.1 <;> simp [complete, finished, present, prEvent_norm]
  · simp only [present, ite_false, zero_mul]
    apply mul_eq_zero.mpr
    right
    rw [prEvent_bind_eq_tsum]
    apply ENNReal.tsum_eq_zero.mpr
    intro second
    simp [prEvent_norm, complete, present]

end

end FormalProof4FHE.HasteBoots.StagedCompletedObservation
