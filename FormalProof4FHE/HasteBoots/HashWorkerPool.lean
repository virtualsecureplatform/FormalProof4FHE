module

public import FormalProof4FHE.HasteBoots.InterleavedMerkleWorker

@[expose] public section

/-!
# A shared-oracle scheduler for interleaved hash workers

A worker advance performs at most one primitive hash call. Scheduling may do
arbitrary shared work between advances and may cancel after rejection, keeping
all work already issued. Acceptance is computed from the residual programs;
it is never supplied by the scheduler. The finite advance count concerns only
verifier-owned worker steps, not the scheduler's or adversary's hash queries.
Native Rayon scheduling/refinement and its concrete completion bound remain
separate from this operational soundness component.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.HashWorkerPool

noncomputable section

variable {Input Digest Cfg Memory Payload : Type} {count : ℕ}

abbrev Workers (Input Digest : Type) (count : ℕ) := Fin count → OracleComp (Input →ₒ Digest) Bool

structure Outcome (Input Digest Memory : Type) (count : ℕ) where
  workers : Workers Input Digest count
  memory : Memory

/-- Only a worker that has actually returned true is complete and accepted. -/
def done (worker : OracleComp (Input →ₒ Digest) Bool) : Bool :=
  OracleComp.casesOn worker (fun value => value) (fun _ _ => false)

theorem done_sound (worker : OracleComp (Input →ₒ Digest) Bool) (accepted : done worker = true) :
    worker = pure true := by
  cases worker with
  | pure value =>
    cases value with
    | false => exact (Bool.false_ne_true accepted).elim
    | true => rfl
  | queryBind input next => exact (Bool.false_ne_true accepted).elim

def allAccepted (workers : Workers Input Digest count) : Bool :=
  (List.ofFn (fun index => done (workers index))).all id

theorem allAccepted_sound (workers : Workers Input Digest count) (accepted : allAccepted workers = true)
    (index : Fin count) : workers index = pure true := by
  have each : ∀ index, done (workers index) = true := by
    simpa only [allAccepted, List.all_eq_true, List.mem_ofFn, forall_exists_index,
      forall_apply_eq_imp_iff, id_eq] using accepted
  exact done_sound _ (each index)

/-- One primitive query is routed to the unique shared hash. Completed workers
stay completed and issue no query when selected again. -/
def tick (worker : OracleComp (Input →ₒ Digest) Bool) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (OracleComp (Input →ₒ Digest) Bool) :=
  OracleComp.casesOn worker (fun value => pure (pure value)) (fun input next =>
    next <$> liftM ((CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inr (.inl input))))

theorem tick_pure (value : Bool) :
    tick (Cfg := Cfg) (pure value : OracleComp (Input →ₒ Digest) Bool) = pure (pure value) := rfl

theorem tick_query (input : Input) (next : Digest → OracleComp (Input →ₒ Digest) Bool) :
    tick (Cfg := Cfg) (OracleComp.queryBind input next) =
      next <$> liftM ((CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inr (.inl input))) := rfl

/-- The scheduler controls interleaving and cancellation, but not acceptance. -/
def program
    (choose : Workers Input Digest count → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin count) × Memory)) :
    ℕ → Workers Input Digest count → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Outcome Input Digest Memory count)
  | 0, workers, memory => pure ⟨workers, memory⟩
  | fuel + 1, workers, memory =>
    if allAccepted workers then pure ⟨workers, memory⟩ else do
      let selected ← choose workers memory
      match selected.1 with
      | none => pure ⟨workers, selected.2⟩
      | some index => do
          let remaining ← tick (workers index)
          program choose fuel (Function.update workers index remaining) selected.2

/-- Residualization is valid in every later cache, including after other workers
or arbitrary shared work have added entries. Equality at only the current cache
would be too weak when both sides currently lack an answer. -/
def Refines (original current : Workers Input Digest count) (cache : (Input →ₒ Digest).QueryCache) : Prop :=
  ∀ index later, cache ≤ later →
    simulateQ later.toPartialImpl (original index) = simulateQ later.toPartialImpl (current index)

theorem refines_refl (workers : Workers Input Digest count) (cache : (Input →ₒ Digest).QueryCache) :
    Refines workers workers cache := fun _ _ _ => rfl

theorem refines_mono (original current : Workers Input Digest count)
    (before after : (Input →ₒ Digest).QueryCache) (grows : before ≤ after)
    (refines : Refines original current before) : Refines original current after :=
  fun index later extension => refines index later (grows.trans extension)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- An actual worker advance fixes its consumed hash answer in every future
cache; it does not sample that answer again during replay. -/
theorem tick_refines (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (worker : OracleComp (Input →ₒ Digest) Bool)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : OracleComp (Input →ₒ Digest) Bool × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (tick worker)).run before))
    (later : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ later) :
    simulateQ later.toPartialImpl worker = simulateQ later.toPartialImpl outcome.1 := by
  cases worker with
  | pure value =>
    change outcome ∈ support (pure ((pure value : OracleComp (Input →ₒ Digest) Bool), before) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    rfl
  | queryBind input next =>
    rw [tick_query, simulateQ_map, StateT.run_map, simulateQ_spec_query, support_map, Set.mem_image] at supported
    obtain ⟨answer, queried, equal⟩ := supported
    subst outcome
    have known := InterleavedMerkleWorker.hash_query_caches (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy shape input before answer.2 answer.1 queried
    change simulateQ later.toPartialImpl (liftM ((Input →ₒ Digest).query input) >>= next) = _
    rw [simulateQ_bind, simulateQ_spec_query, QueryCache.toPartialImpl_apply, extension known]
    rfl

/-- Updating one residual retains the invariant for the entire pool. -/
theorem update_refines (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (original current : Workers Input Digest count) (index : Fin count)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (refines : Refines original current before.hash.cache)
    (outcome : OracleComp (Input →ₒ Digest) Bool × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (tick (current index))).run before)) :
    Refines original (Function.update current index outcome.1) outcome.2.hash.cache := by
  have grows := CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (tick (current index)) before outcome supported
  intro selected later extension
  rw [refines selected later (grows.trans extension)]
  by_cases same : selected = index
  · subst selected
    rw [Function.update_self]
    exact tick_refines enc dummy shape _ before outcome supported later extension
  · rw [Function.update_of_ne same]

/-- All scheduling work and worker calls run through the same handler. No
incoming safety, query cutoff or independent scheduling law is required. -/
theorem run_refines (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (choose : Workers Input Digest count → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin count) × Memory))
    (fuel : ℕ) (original current : Workers Input Digest count) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (refines : Refines original current before.hash.cache)
    (outcome : Outcome Input Digest Memory count × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program choose fuel current memory)).run before)) :
    Refines original outcome.1.workers outcome.2.hash.cache := by
  induction fuel generalizing current memory before outcome with
  | zero =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact refines
  | succ fuel ih =>
    unfold program at supported
    by_cases ready : allAccepted current = true
    · rw [ite_eq_left ready, simulateQ_pure, StateT.run_pure] at supported
      have equal := eq_of_mem_support_pure _ supported
      subst outcome
      exact refines
    · rw [ite_eq_right ready, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨selected, selectedSupported, rest⟩ := supported
      have afterChoice := refines_mono original current _ _
        (CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
          (choose current memory) before selected selectedSupported) refines
      cases chosen : selected.1.1 with
      | none =>
        simp only [chosen, simulateQ_pure, StateT.run_pure] at rest
        have equal := eq_of_mem_support_pure _ rest
        subst outcome
        exact afterChoice
      | some index =>
        simp only [chosen, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
        obtain ⟨advanced, advancedSupported, final⟩ := rest
        exact ih _ _ _ (update_refines enc dummy shape original current index selected.2 afterChoice
          advanced advancedSupported) outcome final

/-- Pool acceptance establishes every original worker's replay from the actual
final shared cache, without an external replay or worker-trace certificate. -/
theorem accepted_replays (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (choose : Workers Input Digest count → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin count) × Memory))
    (fuel : ℕ) (workers : Workers Input Digest count) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Outcome Input Digest Memory count × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program choose fuel workers memory)).run before)) (accepted : allAccepted outcome.1.workers = true)
    (index : Fin count) : simulateQ outcome.2.hash.cache.toPartialImpl (workers index) = some true := by
  have refines := run_refines enc dummy shape choose fuel workers workers memory before
    (refines_refl _ _) outcome supported
  rw [refines index _ le_rfl, allAccepted_sound _ accepted index]
  rfl

end

end FormalProof4FHE.HasteBoots.HashWorkerPool
