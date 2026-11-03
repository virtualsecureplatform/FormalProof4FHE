module

public import FormalProof4FHE.HasteBoots.SharedSequence
public import FormalProof4FHE.HasteBoots.CheckpointCollision

@[expose] public section

/-!
# Sequential verification with actual early return

A failed step retains its result, private memory and final shared hash state.
The continuation does not run later steps, including their private draws.
Arithmetic losses still sum over the trusted list of possible attempts, while
any whole-run hash charge refers only to the program actually executed.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.ShortCircuitSequence

noncomputable section

structure StepResult (Result Memory : Type) where
  result : Result
  memory : Memory
  accepted : Bool

structure Outcome (Index Result Memory : Type) where
  results : List (Index × Result)
  memory : Memory
  accepted : Bool

variable {Index Memory Result Cfg Input Digest Payload : Type}

/-- The empty suffix succeeds. Rejection records the attempted step and returns
immediately, without invoking any remaining step computation. -/
def program (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory)) :
    List Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (Outcome Index Result Memory)
  | [], memory => pure ⟨[], memory, true⟩
  | index :: rest, memory => do
    let first ← step index memory
    let later ← if first.accepted then program step rest first.memory else pure ⟨[], first.memory, false⟩
    pure ⟨(index, first.result) :: later.results, later.memory, later.accepted⟩

/-- One-step factorization retaining the real state for probability composition. -/
theorem program_cons
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (index : Index) (rest : List Index) (memory : Memory) :
    program step (index :: rest) memory =
      (fun pair => (⟨(index, pair.1.result) :: pair.2.results, pair.2.memory, pair.2.accepted⟩ : Outcome Index Result Memory)) <$>
        SharedContinuation.program (step index memory) (fun first =>
          if first.accepted then program step rest first.memory else pure ⟨[], first.memory, false⟩) := by
  simp only [program, SharedContinuation.program, map_bind, map_pure]
  congr 1
  funext first
  cases first.accepted <;> simp only [Bool.false_eq_true, reduceIte, pure_bind]

/-- Rejection erases the suffix at the oracle-program level, before simulation
or work accounting. The rejected step's private memory is preserved. -/
theorem reject_cons
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (index : Index) (rest : List Index) (memory : Memory) (first : StepResult Result Memory)
    (returns : step index memory = pure first) (rejects : first.accepted = false) :
    program step (index :: rest) memory = pure ⟨[(index, first.result)], first.memory, false⟩ := by
  simp only [program, returns, pure_bind, rejects, Bool.false_eq_true, reduceIte]

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Apply source-independent deterministic checks after the actual step, with
no additional oracle calls. An earlier failure cannot be turned into success. -/
def enforce (check : Index → Result → Bool)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (index : Index) (memory : Memory) :=
  (fun first => { first with accepted := first.accepted && check index first.result }) <$> step index memory

theorem enforce_accepts (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (check : Index → Result → Bool)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (index : Index) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : StepResult Result Memory × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (enforce check step index memory)).run state)) (accepted : outcome.1.accepted = true) :
    check index outcome.1.result = true := by
  rw [enforce, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨first, _, equal⟩ := supported
  subst outcome
  exact (Bool.and_eq_true_iff.mp accepted).2

/-- Overall success means that every trusted factor was attempted in order.
This supplies coverage when reducing a wrong supplied factor to an opening. -/
theorem accepted_indices (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (indices : List Index) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome Index Result Memory × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program step indices memory)).run state))
    (accepted : outcome.1.accepted = true) : outcome.1.results.map Prod.fst = indices := by
  induction indices generalizing memory state outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    rfl
  | cons index rest ih =>
    rw [program_cons, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
    obtain ⟨packet, packetSupported, equal⟩ := supported
    subst outcome
    obtain ⟨first, _, later, laterSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy shape (step index memory)
        (fun first => if first.accepted then program step rest first.memory else pure ⟨[], first.memory, false⟩)
        state packet).mp packetSupported
    subst packet
    cases flag : first.1.accepted with
    | false =>
      simp only [flag, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at laterSupported
      have equal := eq_of_mem_support_pure _ laterSupported
      subst later
      exact (Bool.false_ne_true accepted).elim
    | true =>
      simp only [flag, reduceIte] at laterSupported
      have tail := ih first.1.memory first.2 later laterSupported accepted
      exact congrArg (index :: ·) tail

/-- Every attempted result in a successful run satisfies the actual step's
acceptance consequence. This is an operational interface for the native
coordinate and claimed-value checks, not a security assumption. -/
theorem accepted_results (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (indices : List Index) (checked : Index → Result → Prop)
    (stepChecked : ∀ index ∈ indices, ∀ memory initial result,
      result ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
        enc dummy shape) (step index memory)).run initial) → result.1.accepted = true → checked index result.1.result)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome Index Result Memory × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program step indices memory)).run state))
    (accepted : outcome.1.accepted = true) :
    ∀ entry ∈ outcome.1.results, checked entry.1 entry.2 := by
  induction indices generalizing memory state outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    simp
  | cons index rest ih =>
    rw [program_cons, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
    obtain ⟨packet, packetSupported, equal⟩ := supported
    subst outcome
    obtain ⟨first, firstSupported, later, laterSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy shape (step index memory)
        (fun first => if first.accepted then program step rest first.memory else pure ⟨[], first.memory, false⟩)
        state packet).mp packetSupported
    subst packet
    cases flag : first.1.accepted with
    | false =>
      simp only [flag, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at laterSupported
      have equal := eq_of_mem_support_pure _ laterSupported
      subst later
      exact (Bool.false_ne_true accepted).elim
    | true =>
      simp only [flag, reduceIte] at laterSupported
      have head := stepChecked index List.mem_cons_self memory state first firstSupported flag
      have tail := ih (fun i member => stepChecked i (List.mem_cons_of_mem index member))
        first.1.memory first.2 later laterSupported accepted
      intro entry member
      obtain equal | member := List.mem_cons.mp member
      · subst entry
        exact head
      · exact tail entry member

/-- Local authentication facts valid in every larger cache hold for all
successful factors in the final cache, including earlier factors whose workers
finished before later shared work. No independence or initial safety is used. -/
theorem accepted_cache_results (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (indices : List Index) (checked : Index → Result → (Input →ₒ Digest).QueryCache → Prop)
    (stepChecked : ∀ index ∈ indices, ∀ memory initial result,
      result ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
        enc dummy shape) (step index memory)).run initial) → result.1.accepted = true →
      ∀ later : (Input →ₒ Digest).QueryCache, result.2.hash.cache ≤ later → checked index result.1.result later)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome Index Result Memory × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program step indices memory)).run state))
    (accepted : outcome.1.accepted = true) :
    ∀ entry ∈ outcome.1.results, checked entry.1 entry.2 outcome.2.hash.cache := by
  induction indices generalizing memory state outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    simp
  | cons index rest ih =>
    rw [program_cons, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
    obtain ⟨packet, packetSupported, equal⟩ := supported
    subst outcome
    obtain ⟨first, firstSupported, later, laterSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy shape (step index memory)
        (fun first => if first.accepted then program step rest first.memory else pure ⟨[], first.memory, false⟩)
        state packet).mp packetSupported
    subst packet
    cases flag : first.1.accepted with
    | false =>
      simp only [flag, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at laterSupported
      have equal := eq_of_mem_support_pure _ laterSupported
      subst later
      exact (Bool.false_ne_true accepted).elim
    | true =>
      simp only [flag, reduceIte] at laterSupported
      have grows := CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp)
        enc dummy shape (program step rest first.1.memory) first.2 later laterSupported
      have head := stepChecked index List.mem_cons_self memory state first firstSupported flag later.2.hash.cache grows
      have tail := ih (fun i member => stepChecked i (List.mem_cons_of_mem index member))
        first.1.memory first.2 later laterSupported accepted
      intro entry member
      obtain equal | member := List.mem_cons.mp member
      · subst entry
        exact head
      · exact tail entry member

/-- A successful checked loop enforces the literal check on every result. -/
theorem enforced_results (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (check : Index → Result → Bool)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (indices : List Index) (memory : Memory)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome Index Result Memory × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program (enforce check step) indices memory)).run state)) (accepted : outcome.1.accepted = true) :
    ∀ entry ∈ outcome.1.results, check entry.1 entry.2 = true :=
  accepted_results enc dummy shape (enforce check step) indices (fun index result => check index result = true)
    (fun index _ incoming initial result present passed =>
      enforce_accepts enc dummy shape check step index incoming initial result present passed)
    memory state outcome supported accepted

/-- No independence, losslessness, finite memory space or hash-query cutoff is
needed. Rejected paths are included, with exactly their actual issued work. -/
theorem arithmetic_union_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (step : Index → Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) (StepResult Result Memory))
    (bad : Index → Result → Prop) (epsilon : Index → ENNReal) (indices : List Index)
    (localBound : ∀ index ∈ indices, ∀ memory initial,
      Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
        enc dummy shape) (step index memory)).run initial}[bad index outcome.1.result] ≤ epsilon index)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy shape) (program step indices memory)).run state}[SharedSequence.AnyBad bad outcome.1.results] ≤
      (indices.map epsilon).sum := by
  induction indices generalizing memory state with
  | nil => simp [program, SharedSequence.AnyBad, prEvent_norm]
  | cons index rest ih =>
    rw [program_cons, simulateQ_map, StateT.run_map, prEvent_map]
    simp only [SharedSequence.anyBad_cons]
    let next := fun (first : StepResult Result Memory) =>
      if first.accepted then program step rest first.memory else pure ⟨[], first.memory, false⟩
    have firstBound := SharedContinuation.earlier_event_le enc dummy shape (step index memory)
      next state (fun first => bad index first.result)
    have laterBound := SharedContinuation.later_event_le enc dummy shape (step index memory)
      next state (fun _ outcome => SharedSequence.AnyBad bad outcome.1.results) ((rest.map epsilon).sum) (by
        intro first initial
        cases accepted : first.accepted with
        | false => simp [next, accepted, SharedSequence.AnyBad, prEvent_norm]
        | true =>
          simp only [next, accepted, reduceIte]
          exact ih (fun i member => localBound i (List.mem_cons_of_mem index member)) first.memory initial)
    exact (prEvent_or_le _ _ _).trans
      (by simpa only [List.map_cons, List.sum_cons] using
        add_le_add (firstBound.trans (localBound index (List.mem_cons_self) memory state)) laterBound)

end

end FormalProof4FHE.HasteBoots.ShortCircuitSequence
