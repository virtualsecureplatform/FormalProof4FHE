module

public import FormalProof4FHE.HasteBoots.SharedContinuation

@[expose] public section

/-!
# Sequential checks on one shared execution

Steps retain private memory and use the actual shared hash state. A step can
implement early rejection by returning a stopped memory state; later steps
then issue no queries. The arithmetic union bound needs no independence,
finite memory space, losslessness or bound on adversary hash queries.
This module does not union authentication losses.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.SharedSequence

noncomputable section

variable {Index Memory Result Cfg Input Digest Payload : Type}

abbrev Shared (Cfg Input Digest : Type) := CheckpointExecution.Spec unifSpec Cfg Input Digest

def program (step : Index → Memory → OracleComp (Shared Cfg Input Digest) (Result × Memory)) :
    List Index → Memory → OracleComp (Shared Cfg Input Digest) (List (Index × Result) × Memory)
  | [], memory => pure ([], memory)
  | index :: rest, memory => do
    let first ← step index memory
    let later ← program step rest first.2
    pure ((index, first.1) :: later.1, later.2)

def AnyBad (bad : Index → Result → Prop) (results : List (Index × Result)) : Prop :=
  ∃ entry ∈ results, bad entry.1 entry.2

theorem anyBad_cons (bad : Index → Result → Prop) (index : Index) (first : Result)
    (later : List (Index × Result)) :
    AnyBad bad ((index, first) :: later) ↔ bad index first ∨ AnyBad bad later := by
  simp [AnyBad]

/-- Retaining the earlier step result introduces no extra oracle calls. -/
theorem program_cons (step : Index → Memory → OracleComp (Shared Cfg Input Digest) (Result × Memory))
    (index : Index) (rest : List Index) (memory : Memory) :
    program step (index :: rest) memory =
      (fun pair => ((index, pair.1.1) :: pair.2.1, pair.2.2)) <$>
        SharedContinuation.program (step index memory) (fun first => program step rest first.2) := by
  simp only [program, SharedContinuation.program, map_bind, map_pure]

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Sum only the local arithmetic risks. All calls, including work performed
before rejection, remain in the same program for a later whole-run hash bound. -/
theorem arithmetic_union_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (step : Index → Memory → OracleComp (Shared Cfg Input Digest) (Result × Memory))
    (bad : Index → Result → Prop) (epsilon : Index → ENNReal)
    (indices : List Index)
    (localBound : ∀ index ∈ indices, ∀ memory initial,
      Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
        enc dummy shape) (step index memory)).run initial}[bad index outcome.1.1] ≤ epsilon index)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy shape) (program step indices memory)).run state}[AnyBad bad outcome.1.1] ≤
      (indices.map epsilon).sum := by
  induction indices generalizing memory state with
  | nil => simp [program, AnyBad, prEvent_norm]
  | cons index rest ih =>
    rw [program_cons, simulateQ_map, StateT.run_map, prEvent_map]
    simp only [anyBad_cons]
    have firstBound := SharedContinuation.earlier_event_le enc dummy shape (step index memory)
      (fun first => program step rest first.2) state (fun first => bad index first.1)
    have laterBound := SharedContinuation.later_event_le enc dummy shape (step index memory)
      (fun first => program step rest first.2) state (fun _ outcome => AnyBad bad outcome.1.1)
      ((rest.map epsilon).sum) (fun first initial => ih
        (fun i member => localBound i (List.mem_cons_of_mem index member)) first.2 initial)
    exact (prEvent_or_le _ _ _).trans
      (by simpa only [List.map_cons, List.sum_cons] using
        add_le_add (firstBound.trans (localBound index (List.mem_cons_self) memory state)) laterBound)

end

end FormalProof4FHE.HasteBoots.SharedSequence
