module

public import FormalProof4FHE.HasteBoots.NativeLazyStateExecution
public import Mathlib.MeasureTheory.Measure.Continuity
@[expose] public section

/-! Causal machines may run forever: one step receives only its local state,
and read/hash continuations receive only the corresponding response. Finite
analysis prefixes retain the real machine state and resume without resetting
either oracle cache or the monitor. Persistent bad-log lifetime events are
limits of the actual full-state prefix executions, including after prequeries.
This does not assert termination, a physical work bound or Rust refinement. -/
namespace FormalProof4FHE.HasteBoots.OracleMachine
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleProgram (Program)
open MeasureTheory ProbabilityTheory OracleSpec OracleComp

/-- A causal primitive request and response-dependent next local state. -/
inductive Command (S A : Type) where
  | done (value : A)
  | start (input : Input) (next : S)
  | read (input : Input) (offset count : ℕ) (next : Input → S)
  | hash (input : Input) (next : Digest → S)

/-- A finite analysis prefix, not a retry cap. Done states remain done at fuel zero. -/
def take {S A : Type} (step : S → Command S A) : ℕ → S → Program (S ⊕ A)
  | 0, state => match step state with
    | .done value => .pure (.inr value)
    | _ => .pure (.inl state)
  | fuel+1, state => match step state with
    | .done value => .pure (.inr value)
    | .start input next => .start input (take step fuel next)
    | .read input offset count next => .read input offset count (fun values => take step fuel (next values))
    | .hash input next => .hash input (fun digest => take step fuel (next digest))

/-- Resume the retained local machine state; completed runs remain completed. -/
def resume {S A : Type} (step : S → Command S A) (fuel : ℕ) : S ⊕ A → Program (S ⊕ A)
  | .inl state => take step fuel state
  | .inr value => .pure (.inr value)

/-- Prefixes form a compatible family by exact syntactic suspension and resumption. -/
theorem take_resume {S A : Type} (step : S → Command S A) (first later : ℕ) (state : S) :
    take step (first+later) state = OracleProgram.bind (take step first state) (resume step later) := by
  induction first generalizing state with
  | zero => cases chosen : step state <;> cases later <;> simp [take,chosen,OracleProgram.bind,resume]
  | succ first ih =>
    cases chosen : step state with
    | done value => simp [Nat.succ_add,take,chosen,OracleProgram.bind,resume]
    | start input next => simp only [Nat.succ_add,take,chosen,OracleProgram.bind,ih]
    | read input offset count next =>
      simp only [Nat.succ_add,take,chosen,OracleProgram.bind,ih]
    | hash input next => simp only [Nat.succ_add,take,chosen,OracleProgram.bind,ih]

/-- Extending analysis fuel only extends the complete ordered native log. -/
theorem log_prefix {S A : Type} (step : S → Command S A) (first later : ℕ) (bounded : first ≤ later)
    (state : S) (world : World) :
    (OracleProgram.run (take step first state) world).run.2.IsPrefix
      (OracleProgram.run (take step later state) world).run.2 := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
  rw [take_resume,OracleProgram.run_bind,ObservationReplay.run_bind]
  exact ⟨_,rfl⟩


/-- The actual lazy compiler carries its owned byte cache across a machine suspension. -/
theorem compile_resume {Cfg S A : Type} (step : S → Command S A) (first later : ℕ) (state : S) :
    NativeLazyProgram.compile (Cfg := Cfg) (take step (first+later) state) = (do
      let before ← NativeLazyProgram.compile (take step first state)
      let after ← NativeLazyProgram.compile (resume step later before.1)
      pure (after.1,before.2++after.2)) := by
  rw [take_resume]
  exact NativeLazyProgram.compile_bind _ _

noncomputable section

/-- The actual shared execution carries both caches, checkpoints and the monitor across suspension. -/
theorem execute_resume {Cfg Payload S A : Type} (step : S → Command S A) (first later : ℕ) (initial : S)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    NativeLazyStateExecution.execute enc dummy shape (take step (first+later) initial) cache state = (do
      let before ← NativeLazyStateExecution.execute enc dummy shape (take step first initial) cache state
      let after ← NativeLazyStateExecution.execute enc dummy shape (resume step later before.1.1.1) before.1.2 before.2
      pure (((after.1.1.1,before.1.1.2++after.1.1.2),after.1.2),after.2)) := by
  simp only [NativeLazyStateExecution.execute,compile_resume,StateT.run_bind,simulateQ_bind,
    StateT.run_pure,simulateQ_pure]

/-- Exact lifetime probability of a persistent bad-log event after any replayable prequery history. -/
theorem conditional_lifetime_law {Cfg Payload S A P : Type} (step : S → Command S A) (initial : S)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (bad : List Observation → Prop)
    (persistent : ∀ first later, first.IsPrefix later → bad first → bad later) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, bad (OracleProgram.run (take step fuel initial) other).run.2} =
      ⨆ fuel : ℕ, Pr{let result ← (NativeLazyStateExecution.execute enc dummy shape
        (take step fuel initial) (NativeShakeKernel.observed (past world).run.2 world) state)}[bad result.1.1.2] := by
  have monotone : Monotone (fun fuel : ℕ => {other : World |
      bad (OracleProgram.run (take step fuel initial) other).run.2}) := by
    intro first later bounded other yes
    exact persistent _ _ (log_prefix step first later bounded initial other) yes
  have union : {other | ∃ fuel, bad (OracleProgram.run (take step fuel initial) other).run.2} =
      ⋃ fuel : ℕ, {other | bad (OracleProgram.run (take step fuel initial) other).run.2} := by
    ext other
    simp
  rw [union,monotone.measure_iUnion]
  congr 1
  funext fuel
  exact NativeLazyStateExecution.state_law (take step fuel initial) replay world enc dummy shape state hashStart
    (fun result => bad result.1.1.2)

/-- Lifetime probability from empty caches is the supremum of actual prefix probabilities, with no cutoff. -/
theorem lifetime_law {Cfg Payload S A : Type} (step : S → Command S A) (initial : S)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (bad : List Observation → Prop)
    (persistent : ∀ first later, first.IsPrefix later → bad first → bad later) :
    InputIndexedOracle.law {world | ∃ fuel, bad (OracleProgram.run (take step fuel initial) world).run.2} =
      ⨆ fuel : ℕ, Pr{let result ← (NativeLazyStateExecution.execute enc dummy shape
        (take step fuel initial) NativeShakeCache.empty (CheckpointExecution.empty shape))}[bad result.1.1.2] := by
  have monotone : Monotone (fun fuel : ℕ => {world : World |
      bad (OracleProgram.run (take step fuel initial) world).run.2}) := by
    intro first later bounded world yes
    exact persistent _ _ (log_prefix step first later bounded initial world) yes
  have union : {world | ∃ fuel, bad (OracleProgram.run (take step fuel initial) world).run.2} =
      ⋃ fuel : ℕ, {world | bad (OracleProgram.run (take step fuel initial) world).run.2} := by
    ext world
    simp
  rw [union,monotone.measure_iUnion]
  congr 1
  funext fuel
  exact NativeLazyStateExecution.from_empty (take step fuel initial) enc dummy shape
    (fun result => bad result.1.1.2)

/-- Completed prefixes retain exactly the same result and log at all later fuel values. -/
theorem completed_run {S A : Type} (step : S → Command S A) (first later : ℕ) (state : S) (world : World)
    (value : A) (completed : (OracleProgram.run (take step first state) world).run.1 = .inr value) :
    (OracleProgram.run (take step (first+later) state) world).run =
      (OracleProgram.run (take step first state) world).run := by
  rw [take_resume,OracleProgram.run_bind,ObservationReplay.run_bind,completed]
  change ((Sum.inr value : S ⊕ A),(OracleProgram.run (take step first state) world).run.2 ++ []) = _
  rw [List.append_nil]
  exact Prod.ext completed.symm rfl


/-- Bad completed results have an exact lifetime law without a completion or success floor. -/
theorem completion_lifetime_law {Cfg Payload S A P : Type} (step : S → Command S A) (initial : S)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2) (bad : A → Prop) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel value, (OracleProgram.run (take step fuel initial) other).run.1 = .inr value ∧ bad value} =
      ⨆ fuel : ℕ, Pr{let result ← (NativeLazyStateExecution.execute enc dummy shape
        (take step fuel initial) (NativeShakeKernel.observed (past world).run.2 world) state)}[
          ∃ value, result.1.1.1 = .inr value ∧ bad value] := by
  let events := fun fuel : ℕ => {other : World | ∃ value,
    (OracleProgram.run (take step fuel initial) other).run.1 = .inr value ∧ bad value}
  have monotone : Monotone events := by
    intro first later bounded other yes
    obtain ⟨value,completed,badValue⟩ := yes
    obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le bounded
    exact ⟨value,by rw [completed_run step first extra initial other value completed]; exact completed,badValue⟩
  have union : {other | ∃ fuel value, (OracleProgram.run (take step fuel initial) other).run.1 = .inr value ∧ bad value} =
      ⋃ fuel : ℕ, events fuel := by
    ext other
    simp [events]
  rw [union,monotone.measure_iUnion]
  congr 1
  funext fuel
  exact NativeLazyStateExecution.state_law (take step fuel initial) replay world enc dummy shape state hashStart
    (fun result => ∃ value, result.1.1.1 = .inr value ∧ bad value)


/-- Every eventual prefix-result event is measurable in the original joint
product sigma algebra, even for arbitrary local states and result predicates. -/
theorem eventual_measurable {S A : Type} (step : S → Command S A) (initial : S)
    (event : (S ⊕ A) × List Observation → Prop) :
    MeasurableSet {world : World | ∃ fuel, event (OracleProgram.run (take step fuel initial) world).run} := by
  have union : {world : World | ∃ fuel, event (OracleProgram.run (take step fuel initial) world).run} =
      ⋃ fuel : ℕ, {world : World | event (OracleProgram.run (take step fuel initial) world).run} := by
    ext world
    simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => OracleExecutionLaw.event_measurable
    (OracleProgram.run_replay (take step fuel initial)) event)

end
end FormalProof4FHE.HasteBoots.OracleMachine
