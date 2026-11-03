module

public import FormalProof4FHE.HasteBoots.CheckpointExecution
public import FormalProof4FHE.HasteBoots.CachedHashCollision

@[expose] public section

/-!
# Combined collision and source-stability loss for adaptive checkpoints

Both events refer to one shared cached hash and one actual execution. A cache
collision cannot disappear; the source-failure monitor also persists. Thus the
terminal disjunction remembers either exception occurring earlier in the run.
The combined loss is accumulated without a query budget or an independence
assumption. Native phase placement, transcript compilation and physical-work
coupling remain open.
-/

open OracleSpec OracleComp BinaryTree ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.CheckpointCollision

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

/-- One event retains both exceptions to frozen-source availability. -/
def Bad (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop :=
  state.failed = true ∨ CacheHasCollision state.hash.cache

def Safe (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop :=
  CheckpointExecution.Good enc dummy shape state ∧ ¬CacheHasCollision state.hash.cache

theorem safe_empty (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) : Safe enc dummy shape (CheckpointExecution.empty shape) :=
  ⟨CheckpointExecution.good_empty enc dummy shape, CachedHashCollision.no_collision_empty⟩

section Runtime

variable [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

/-- Private computations and adaptive root snapshots cannot overwrite hash answers. -/
theorem cache_monotone_step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : (CheckpointExecution.Spec base Cfg Input Digest).Range query ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((CheckpointExecution.handler implBase enc dummy shape query).run state)) :
    state.hash.cache ≤ result.2.hash.cache := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer, state)) <$> implBase privateQuery) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact le_rfl
  · change result ∈ support ((fun result =>
        (result.1, CheckpointExecution.afterHash enc dummy shape state result.2)) <$>
          (CachedHashHandler.handler hashQuery).run state.hash) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨next, present, equal⟩ := supported
    subst result
    exact CachedHashCollision.cache_monotone_step hashQuery state.hash next present
  · change result ∈ support (pure ((), CheckpointExecution.record shape state request.1 request.2) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact le_rfl

/-- Whole-run cache growth includes every private/hash/recording interleaving. -/
theorem cache_monotone_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run state)) :
    state.hash.cache ≤ result.2.hash.cache := by
  apply simulateQ_run_preserves_inv_of_query _ (fun current => state.hash.cache ≤ current.hash.cache)
    ?_ program state le_rfl result supported
  intro query current prior next present
  exact prior.trans (cache_monotone_step implBase enc dummy shape query current next present)

/-- Either earlier exception persists, including across subsequently recorded roots. -/
theorem bad_persistent_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (bad : Bad shape state)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run state)) :
    Bad shape result.2 := by
  obtain failed | collision := bad
  · exact Or.inl (CheckpointExecution.failed_run implBase enc dummy shape program state failed result supported)
  · exact Or.inr (CachedHashCollision.collision_mono _ _
      (cache_monotone_run implBase enc dummy shape program state result supported) collision)

variable [Fintype Digest]

/-- Collision charge is zero on private draws, cached queries and root snapshots. -/
def collisionLoss (base : OracleSpec ι) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : ENNReal :=
  match query with
  | .inl _ => 0
  | .inr (.inl hashQuery) => CachedHashCollision.loss hashQuery state.hash
  | .inr (.inr _) => 0

/-- Combined loss is a union bound on the same answer, not a product. -/
def loss (base : OracleSpec ι) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : ENNReal :=
  CheckpointExecution.loss base shape query state + collisionLoss base shape query state


omit [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
/-- On a fresh hash, both exceptions share the same digest denominator. The
available targets are deduplicated across every recorded root. -/
theorem hash_loss (base : OracleSpec ι) (shape : Cfg → Skeleton)
    (query : Input) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    loss base shape (.inr (.inl query)) state =
      if state.hash.cache query = none then
        ((min state.checkpoints.totalNodeBudget
          (2 * state.hash.keys.card + state.checkpoints.checkpoints.length) + state.hash.keys.card : ℕ) : ENNReal) /
            Fintype.card Digest
      else 0 := by
  simp only [loss, CheckpointExecution.loss, collisionLoss,
    CachedHashCheckpoint.loss, CachedHashCollision.loss]
  by_cases fresh : state.hash.cache query = none
  · simp only [fresh, reduceIte, Nat.cast_add]
    exact ENNReal.add_div.symm
  · simp only [fresh, reduceIte, add_zero]

theorem collision_step_bound (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (coherent : CachedHashHandler.Coherent state.hash) (noCollision : ¬CacheHasCollision state.hash.cache) :
    Pr{let result ← (CheckpointExecution.handler implBase enc dummy shape query).run state}[
      CacheHasCollision result.2.hash.cache] ≤ collisionLoss base shape query state := by
  rcases query with privateQuery | (hashQuery | request)
  · change Pr{let result ← (fun answer => (answer, state)) <$> implBase privateQuery}[
      CacheHasCollision result.2.hash.cache] ≤ 0
    rw [prEvent_map]
    exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun _ collision => noCollision collision))
  · change Pr{let result ← (fun result =>
        (result.1, CheckpointExecution.afterHash enc dummy shape state result.2)) <$>
          (CachedHashHandler.handler hashQuery).run state.hash}[
        CacheHasCollision result.2.hash.cache] ≤ _
    rw [prEvent_map]
    exact CachedHashCollision.step_loss_bound state.hash coherent noCollision hashQuery
  · change Pr{let result ← (pure ((), CheckpointExecution.record shape state request.1 request.2) : ProbComp _)}[
      CacheHasCollision result.2.hash.cache] ≤ 0
    apply le_of_eq
    apply prEvent_eq_zero_of_forall_mem_support
    intro result supported collision
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact noCollision collision

/-- From a safe full state, one step can lose safety only through source
instability or a cache collision. Roots and inputs may depend on all history. -/
theorem step_loss_bound (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (valid : Safe enc dummy shape state) :
    Pr{let result ← (CheckpointExecution.handler implBase enc dummy shape query).run state}[
      ¬Safe enc dummy shape result.2] ≤ loss base shape query state := by
  classical
  apply le_trans (prEvent_mono _ _ (fun result =>
    ¬CheckpointExecution.Good enc dummy shape result.2 ∨ CacheHasCollision result.2.hash.cache) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add
      (CheckpointExecution.step_loss_bound implBase enc dummy shape query state valid.1)
      (collision_step_bound implBase enc dummy shape query state valid.1.1 valid.2))
  · intro result invalid
    by_cases good : CheckpointExecution.Good enc dummy shape result.2
    · exact Or.inr (Classical.byContradiction (fun noCollision => invalid ⟨good, noCollision⟩))
    · exact Or.inl good

/-- The combined first-exception event is bounded by expected accumulated
charges over the actual canonical-hash execution, with no query cutoff. -/
theorem failure_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (valid : Safe enc dummy shape state) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run state}[
      Bad shape result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape) (loss base shape) program state := by
  apply le_trans (prEvent_mono _ _ _ ?_)
    (ExpectedHazard.terminal_failure_le_charge _ _ _ (step_loss_bound implBase enc dummy shape)
      program state valid)
  intro result bad safe
  obtain failed | collision := bad
  · have impossible : (false : Bool) = true := safe.1.2.1.symm.trans failed
    cases impossible
  · exact safe.2 collision

/-- The combined theorem starts from the actual empty cache and root history. -/
theorem failure_from_empty_le_charge {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run
        (CheckpointExecution.empty shape)}[Bad shape result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape) (loss base shape)
        program (CheckpointExecution.empty shape) :=
  failure_le_charge implBase enc dummy shape program (CheckpointExecution.empty shape) (safe_empty enc dummy shape)

end Runtime

end

end FormalProof4FHE.HasteBoots.CheckpointCollision
