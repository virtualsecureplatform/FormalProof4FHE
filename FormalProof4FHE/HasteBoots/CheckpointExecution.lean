module

public import FormalProof4FHE.HasteBoots.CachedHashCheckpoint

@[expose] public section

/-!
# Shared hash execution with adaptive checkpoints and a persistent failure flag

Private computations, canonical cached hash calls and checkpoint recording can
interleave arbitrarily. The ghost monitor remembers any loss of a recorded
source, including a loss later repaired by further queries. It does not affect
answers or the cache. Recording snapshots the actual cumulative hash log.
Native phase placement, collision losses and physical-work coupling remain open.
-/

open OracleSpec OracleComp BinaryTree ProbabilityTheory MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.CheckpointExecution

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

abbrev Spec {ι : Type} (base : OracleSpec ι) (Cfg Input Digest : Type) :=
  base + ((Input →ₒ Digest) + (Cfg × Digest →ₒ Unit))

structure State (shape : Cfg → Skeleton) where
  hash : CachedHashHandler.State Input Digest
  checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape
  failed : Bool

def empty (shape : Cfg → Skeleton) : State (Input := Input) (Digest := Digest) shape :=
  ⟨CachedHashHandler.empty, ExtractorState.empty, false⟩

def record (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (tag : Cfg) (root : Digest) : State (Input := Input) (Digest := Digest) shape :=
  { state with checkpoints := state.checkpoints.recordCumulative tag state.hash.log root }

/-- Failure is a passive, persistent monitor, never an extra verifier check. -/
def afterHash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (next : CachedHashHandler.State Input Digest) : State (Input := Input) (Digest := Digest) shape := by
  classical
  exact { state with hash := next, failed := (state.failed ||
    decide (¬MerklePayloadCheckpoints.StableAt enc dummy shape state.checkpoints next.log)) }

def Good (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape) : Prop :=
  CachedHashHandler.Coherent state.hash ∧ state.failed = false ∧
    MerklePayloadCheckpoints.StableAt enc dummy shape state.checkpoints state.hash.log

/-- Coherence always holds; an unset monitor certifies all recorded sources. -/
def Audited (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape) : Prop :=
  CachedHashHandler.Coherent state.hash ∧ (state.failed = false →
    MerklePayloadCheckpoints.StableAt enc dummy shape state.checkpoints state.hash.log)

theorem good_empty (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) : Good enc dummy shape (empty shape) :=
  ⟨CachedHashHandler.coherent_empty, rfl, MerklePayloadCheckpoints.stable_empty enc dummy shape _⟩

omit [DecidableEq Input] in
/-- The monitor fires exactly on a previous failure or a newly unstable source. -/
theorem afterHash_failed_iff (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (next : CachedHashHandler.State Input Digest) :
    (afterHash enc dummy shape state next).failed = true ↔ state.failed = true ∨
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape state.checkpoints next.log := by
  classical
  simp only [afterHash, Bool.or_eq_true, decide_eq_true_eq]

omit [DecidableEq Input] in
theorem afterHash_clear_stable (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (next : CachedHashHandler.State Input Digest)
    (clear : (afterHash enc dummy shape state next).failed = false) :
    MerklePayloadCheckpoints.StableAt enc dummy shape state.checkpoints next.log := by
  by_contra unstable
  have fired := (afterHash_failed_iff enc dummy shape state next).mpr (Or.inr unstable)
  rw [clear] at fired
  cases fired

theorem afterHash_good (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (valid : Good enc dummy shape state) (next : CachedHashHandler.State Input Digest)
    (coherent : CachedHashHandler.Coherent next)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape state.checkpoints next.log) :
    Good enc dummy shape (afterHash enc dummy shape state next) := by
  refine ⟨coherent, ?_, stable⟩
  simp only [afterHash, valid.2.1, stable, not_true_eq_false, decide_false, Bool.false_or]

theorem record_good (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (valid : Good enc dummy shape state) (tag : Cfg) (root : Digest) :
    Good enc dummy shape (record shape state tag root) :=
  ⟨valid.1, valid.2.1, MerklePayloadCheckpoints.stable_record enc dummy shape state.checkpoints
    state.hash.log valid.2.2 tag root⟩

section Runtime

variable [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

/-- Every hash call delegates to the canonical cached handler. Private calls
leave the hash state alone, and recording only freezes a root at the current log. -/
def handler (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton) :
    QueryImpl (Spec base Cfg Input Digest) (StateT (State (Input := Input) (Digest := Digest) shape) ProbComp) :=
  fun query => StateT.mk fun state => match query with
    | .inl privateQuery => (fun answer => (answer, state)) <$> implBase privateQuery
    | .inr (.inl hashQuery) => (fun result =>
        (result.1, afterHash enc dummy shape state result.2)) <$>
          (CachedHashHandler.handler hashQuery).run state.hash
    | .inr (.inr request) => pure ((), record shape state request.1 request.2)

/-- The reference execution has the same private computations and cached hash,
with checkpoint annotations erased to unit-valued no-ops. -/
def canonical (implBase : QueryImpl base ProbComp) :
    QueryImpl (Spec base Cfg Input Digest) (StateT (Input →ₒ Digest).QueryCache ProbComp) :=
  fun query => StateT.mk fun cache => match query with
    | .inl privateQuery => (fun answer => (answer, cache)) <$> implBase privateQuery
    | .inr (.inl hashQuery) => ((Input →ₒ Digest).randomOracle hashQuery).run cache
    | .inr (.inr _) => pure ((), cache)

/-- The ghost monitor and checkpoints never alter a primitive answer or cache. -/
theorem project_step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (Spec base Cfg Input Digest).Domain) (state : State (Input := Input) (Digest := Digest) shape) :
    Prod.map id (fun state => state.hash.cache) <$> (handler implBase enc dummy shape query).run state =
      (canonical (Cfg := Cfg) implBase query).run state.hash.cache := by
  rcases query with privateQuery | (hashQuery | request)
  · change Prod.map id (fun state => state.hash.cache) <$>
      ((fun answer => (answer, state)) <$> implBase privateQuery) = _
    rw [Functor.map_map]
    rfl
  · change Prod.map id (fun state => state.hash.cache) <$>
      ((fun result => (result.1, afterHash enc dummy shape state result.2)) <$>
        (CachedHashHandler.handler hashQuery).run state.hash) = _
    rw [Functor.map_map]
    exact CachedHashHandler.project_step hashQuery state.hash
  · rfl

theorem project_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Spec base Cfg Input Digest) Result)
    (state : State (Input := Input) (Digest := Digest) shape) :
    Prod.map id (fun state => state.hash.cache) <$>
        (simulateQ (handler implBase enc dummy shape) program).run state =
      (simulateQ (canonical (Cfg := Cfg) implBase) program).run state.hash.cache :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (project_step implBase enc dummy shape) program state

/-- Cache coherence and the clear-monitor certificate hold through every step. -/
theorem audited_step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (Spec base Cfg Input Digest).Domain) (state : State (Input := Input) (Digest := Digest) shape)
    (valid : Audited enc dummy shape state)
    (result : (Spec base Cfg Input Digest).Range query × State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((handler implBase enc dummy shape query).run state)) :
    Audited enc dummy shape result.2 := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer, state)) <$> implBase privateQuery) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact valid
  · change result ∈ support ((fun result => (result.1, afterHash enc dummy shape state result.2)) <$>
      (CachedHashHandler.handler hashQuery).run state.hash) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨next, supported, equal⟩ := supported
    subst result
    exact ⟨CachedHashHandler.coherent_step hashQuery state.hash valid.1 next supported,
      afterHash_clear_stable enc dummy shape state next.2⟩
  · change result ∈ support (pure ((), record shape state request.1 request.2) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact ⟨valid.1, fun clear => MerklePayloadCheckpoints.stable_record enc dummy shape
      state.checkpoints state.hash.log (valid.2 clear) request.1 request.2⟩

/-- A clear monitor at return certifies every adaptively recorded source. -/
theorem audited_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Spec base Cfg Input Digest) Result)
    (state : State (Input := Input) (Digest := Digest) shape) (valid : Audited enc dummy shape state)
    (result : Result × State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (handler implBase enc dummy shape) program).run state)) :
    Audited enc dummy shape result.2 :=
  simulateQ_run_preserves_inv_of_query _ _ (audited_step implBase enc dummy shape)
    program state valid result supported

/-- Once raised, the monitor remains raised through any further adaptive run. -/
theorem failed_step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (Spec base Cfg Input Digest).Domain) (state : State (Input := Input) (Digest := Digest) shape)
    (failed : state.failed = true)
    (result : (Spec base Cfg Input Digest).Range query × State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((handler implBase enc dummy shape query).run state)) :
    result.2.failed = true := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer, state)) <$> implBase privateQuery) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact failed
  · change result ∈ support ((fun result => (result.1, afterHash enc dummy shape state result.2)) <$>
      (CachedHashHandler.handler hashQuery).run state.hash) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨next, _, equal⟩ := supported
    subst result
    exact (afterHash_failed_iff enc dummy shape state next.2).mpr (Or.inl failed)
  · change result ∈ support (pure ((), record shape state request.1 request.2) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact failed

theorem failed_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Spec base Cfg Input Digest) Result)
    (state : State (Input := Input) (Digest := Digest) shape) (failed : state.failed = true)
    (result : Result × State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (handler implBase enc dummy shape) program).run state)) :
    result.2.failed = true :=
  simulateQ_run_preserves_inv_of_query _ (fun state => state.failed = true)
    (failed_step implBase enc dummy shape) program state failed result supported


variable [Fintype Digest]

/-- The current shared target bound is charged only for a fresh hash input.
Private computations and checkpoint annotations have zero stability loss. -/
def loss (base : OracleSpec ι) (shape : Cfg → Skeleton)
    (query : (Spec base Cfg Input Digest).Domain)
    (state : State (Input := Input) (Digest := Digest) shape) : ENNReal :=
  match query with
  | .inl _ => 0
  | .inr (.inl hashQuery) => CachedHashCheckpoint.loss shape state.checkpoints hashQuery state.hash
  | .inr (.inr _) => 0

/-- Full-state conditional hazard, allowing adaptive root recording and private
randomness between any two shared hash queries. -/
theorem step_loss_bound (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (Spec base Cfg Input Digest).Domain) (state : State (Input := Input) (Digest := Digest) shape)
    (valid : Good enc dummy shape state) :
    Pr{let result ← (handler implBase enc dummy shape query).run state}[¬Good enc dummy shape result.2] ≤
      loss base shape query state := by
  rcases query with privateQuery | (hashQuery | request)
  · change Pr{let result ← (fun answer => (answer, state)) <$> implBase privateQuery}[
      ¬Good enc dummy shape result.2] ≤ 0
    rw [prEvent_map]
    exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun _ invalid => invalid valid))
  · change Pr{let result ← (fun result =>
        (result.1, afterHash enc dummy shape state result.2)) <$>
          (CachedHashHandler.handler hashQuery).run state.hash}[
        ¬Good enc dummy shape result.2] ≤ _
    rw [prEvent_map]
    apply le_trans (prEvent_mono_of_support _ _ _ ?_)
      (CachedHashCheckpoint.step_loss_bound enc dummy shape state.checkpoints state.hash
        valid.1 valid.2.2 hashQuery)
    intro next supported invalid stable
    exact invalid (afterHash_good enc dummy shape state valid next.2
      (CachedHashHandler.coherent_step hashQuery state.hash valid.1 next supported) stable)
  · change Pr{let result ← (pure ((), record shape state request.1 request.2) : ProbComp _)}[
      ¬Good enc dummy shape result.2] ≤ 0
    apply le_of_eq
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported invalid
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact invalid (record_good enc dummy shape state valid request.1 request.2)

/-- Probability of any monitored failure, including an earlier failure later
repaired, is bounded by the expected accumulated fresh-answer charge. The
program may choose roots, private draws and hash inputs adaptively and has no
maximum query count. All returned failure branches retain their preceding work. -/
theorem failure_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Spec base Cfg Input Digest) Result)
    (state : State (Input := Input) (Digest := Digest) shape) (valid : Good enc dummy shape state) :
    Pr{let result ← (simulateQ (handler implBase enc dummy shape) program).run state}[result.2.failed = true] ≤
      ExpectedHazard.charge (handler implBase enc dummy shape) (loss base shape) program state := by
  apply le_trans (prEvent_mono _ _ _ ?_)
    (ExpectedHazard.terminal_failure_le_charge _ _ _ (step_loss_bound implBase enc dummy shape)
      program state valid)
  intro result failed good
  have impossible : (false : Bool) = true := good.2.1.symm.trans failed
  cases impossible

/-- Empty shared cache and no recorded roots discharge all initial premises. -/
theorem failure_from_empty_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (Spec base Cfg Input Digest) Result) :
    Pr{let result ← (simulateQ (handler implBase enc dummy shape) program).run (empty shape)}[
      result.2.failed = true] ≤
      ExpectedHazard.charge (handler implBase enc dummy shape) (loss base shape) program (empty shape) :=
  failure_le_charge implBase enc dummy shape program (empty shape) (good_empty enc dummy shape)

end Runtime

end

end FormalProof4FHE.HasteBoots.CheckpointExecution
