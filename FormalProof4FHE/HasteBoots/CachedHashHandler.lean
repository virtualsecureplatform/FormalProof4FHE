module

public import FormalProof4FHE.HasteBoots.MerkleCheckpointProbability
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

@[expose] public section

/-!
# A concrete shared cached hash handler with passive accounting

Every hash step runs VCVio's canonical lazy random oracle. The extra state
retains the complete ordered log and the exact finite set of populated keys.
Projecting away that bookkeeping recovers the canonical oracle computation.
Private sampling, checkpoint recording and cryptographic drift are downstream.
-/

open OracleSpec OracleComp MerkleTreeExtractability MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.CachedHashHandler

noncomputable section

variable {Input Digest : Type} [DecidableEq Input]

structure State (Input Digest : Type) where
  cache : (Input →ₒ Digest).QueryCache
  log : MerkleTreeExtractor.QueryLog Input Digest
  keys : Finset Input

def empty : State Input Digest := ⟨∅, [], ∅⟩

/-- Exact native-analysis invariant; no collision-freedom assumption is included. -/
def Coherent (state : State Input Digest) : Prop :=
  LogCacheKeysInvariant state.log state.cache state.keys

def observe (state : State Input Digest) (query : Input) (answer : Digest)
    (cache : (Input →ₒ Digest).QueryCache) : State Input Digest :=
  ⟨cache, state.log ++ [⟨query, answer⟩], insert query state.keys⟩

theorem coherent_empty : Coherent (empty : State Input Digest) := by
  refine ⟨?_, ?_, ?_⟩
  · intro query answer member
    cases member
  · intro query answer known
    cases known
  · intro query
    change (query ∈ (∅ : Finset Input)) ↔ ∃ answer : Digest, (none : Option Digest) = some answer
    simp

/-- Repeating a known query preserves cache/log/key coherence. -/
theorem coherent_cached (state : State Input Digest) (coherent : Coherent state)
    (query : Input) (answer : Digest) (known : state.cache query = some answer) :
    Coherent (observe state query answer state.cache) := by
  refine ⟨?_, ?_, ?_⟩
  · intro input value member
    change (⟨input, value⟩ : (_input : Input) × Digest) ∈ state.log ++ [⟨query, answer⟩] at member
    obtain old | new := List.mem_append.mp member
    · exact coherent.log_agrees input value old
    · have equal := List.mem_singleton.mp new
      cases equal
      exact known
  · intro input value present
    exact List.mem_append_left _ (coherent.cache_covered input value present)
  · intro input
    change input ∈ insert query state.keys ↔ ∃ value, state.cache input = some value
    rw [Finset.mem_insert]
    constructor
    · rintro (same | old)
      · subst input
        exact ⟨answer, known⟩
      · exact (coherent.mem_keys_iff input).mp old
    · intro present
      exact Or.inr ((coherent.mem_keys_iff input).mpr present)

/-- A new answer extends the cache and the exact finite key cover together. -/
theorem coherent_fresh (state : State Input Digest) (coherent : Coherent state)
    (query : Input) (answer : Digest) (fresh : state.cache query = none) :
    Coherent (observe state query answer (state.cache.cacheQuery query answer)) := by
  have monotone : state.cache ≤ state.cache.cacheQuery query answer := QueryCache.le_cacheQuery _ fresh
  refine ⟨?_, ?_, ?_⟩
  · intro input value member
    change (⟨input, value⟩ : (_input : Input) × Digest) ∈ state.log ++ [⟨query, answer⟩] at member
    obtain old | new := List.mem_append.mp member
    · exact monotone (coherent.log_agrees input value old)
    · have equal := List.mem_singleton.mp new
      cases equal
      exact QueryCache.cacheQuery_self _ _ _
  · intro input value present
    change (state.cache.cacheQuery query answer) input = some value at present
    by_cases same : input = query
    · subst input
      rw [QueryCache.cacheQuery_self] at present
      have equal : answer = value := Option.some.inj present
      subst value
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
      exact List.mem_append_left _ (coherent.cache_covered input value present)
  · intro input
    change input ∈ insert query state.keys ↔ ∃ value, (state.cache.cacheQuery query answer) input = some value
    by_cases same : input = query
    · subst input
      simp only [Finset.mem_insert, true_or, QueryCache.cacheQuery_self, Option.some.injEq,
        exists_eq', iff_self]
    · rw [Finset.mem_insert, or_iff_right same]
      simp only [QueryCache.cacheQuery_of_ne _ _ same]
      exact coherent.mem_keys_iff input

/-- Repeated queries consume a log entry but do not create another cached key. -/
theorem cached_keys (state : State Input Digest) (coherent : Coherent state)
    (query : Input) (answer : Digest) (known : state.cache query = some answer) :
    (observe state query answer state.cache).keys = state.keys := by
  exact Finset.insert_eq_of_mem ((coherent.mem_keys_iff query).mpr ⟨answer, known⟩)

/-- A genuinely fresh query adds exactly one cached key. -/
theorem fresh_key_count (state : State Input Digest) (coherent : Coherent state)
    (query : Input) (answer : Digest) (fresh : state.cache query = none) :
    (observe state query answer (state.cache.cacheQuery query answer)).keys.card = state.keys.card + 1 := by
  apply Finset.card_insert_of_notMem
  intro member
  obtain ⟨value, known⟩ := (coherent.mem_keys_iff query).mp member
  rw [fresh] at known
  cases known

/-- Coherence supplies exactly the cache/log agreement used by extraction. -/
theorem represents_cache (state : State Input Digest) (coherent : Coherent state) :
    LogRepresentsCache state.log state.cache := by
  refine ⟨fun entry member => coherent.log_agrees entry.1 entry.2 member, ?_⟩
  intro query answer known
  exact ⟨⟨query, answer⟩, coherent.cache_covered query answer known, rfl, rfl⟩

section Runtime

variable [SampleableType Digest]

/-- One actual canonical cached hash query, with passive log and key-set tracking. -/
def handler : QueryImpl (Input →ₒ Digest) (StateT (State Input Digest) ProbComp) :=
  fun query => StateT.mk fun state =>
    (fun result => (result.1, observe state query result.1 result.2)) <$>
      ((Input →ₒ Digest).randomOracle query).run state.cache

theorem run_cached (state : State Input Digest) (query : Input) (answer : Digest)
    (known : state.cache query = some answer) :
    (handler query).run state = pure (answer, observe state query answer state.cache) := by
  change (fun result => (result.1, observe state query result.1 result.2)) <$>
    ((Input →ₒ Digest).randomOracle query).run state.cache = _
  rw [randomOracle.run_eq, known, map_pure]

theorem run_fresh (state : State Input Digest) (query : Input) (fresh : state.cache query = none) :
    (handler query).run state =
      (fun answer => (answer, observe state query answer (state.cache.cacheQuery query answer))) <$> ($ᵗ Digest) := by
  change (fun result => (result.1, observe state query result.1 result.2)) <$>
    ((Input →ₒ Digest).randomOracle query).run state.cache = _
  rw [randomOracle.run_eq, fresh, map_bind]
  simp only [map_eq_bind_pure_comp, pure_bind]
  exact bind_congr fun _ => rfl

/-- Every supported hash step preserves exact cache/log/key coherence. -/
theorem coherent_step (query : Input) (state : State Input Digest) (coherent : Coherent state)
    (result : Digest × State Input Digest) (supported : result ∈ support ((handler query).run state)) :
    Coherent result.2 := by
  cases known : state.cache query with
  | none =>
      rw [run_fresh state query known, support_map, Set.mem_image] at supported
      obtain ⟨answer, _, equal⟩ := supported
      subst result
      exact coherent_fresh state coherent query answer known
  | some answer =>
      rw [run_cached state query answer known, mem_support_pure_iff] at supported
      subst result
      exact coherent_cached state coherent query answer known

/-- The invariant holds through every adaptive program, without a query bound. -/
theorem coherent_run {Result : Type} (program : OracleComp (Input →ₒ Digest) Result)
    (state : State Input Digest) (coherent : Coherent state)
    (result : Result × State Input Digest)
    (supported : result ∈ support ((simulateQ handler program).run state)) :
    Coherent result.2 :=
  simulateQ_run_preserves_inv_of_query handler Coherent coherent_step program state coherent
    result supported

/-- Forgetting passive accounting recovers precisely the canonical one-query run. -/
theorem project_step (query : Input) (state : State Input Digest) :
    Prod.map id State.cache <$> (handler query).run state =
      ((Input →ₒ Digest).randomOracle query).run state.cache := by
  change Prod.map id State.cache <$>
    ((fun result => (result.1, observe state query result.1 result.2)) <$>
      ((Input →ₒ Digest).randomOracle query).run state.cache) = _
  rw [Functor.map_map]
  exact id_map _

/-- The same canonical-oracle equality holds for every adaptive hash program. -/
theorem project_run {Result : Type} (program : OracleComp (Input →ₒ Digest) Result)
    (state : State Input Digest) :
    Prod.map id State.cache <$> (simulateQ handler program).run state =
      (simulateQ (Input →ₒ Digest).randomOracle program).run state.cache :=
  map_run_simulateQ_eq_of_query_map_eq handler (Input →ₒ Digest).randomOracle State.cache
    project_step program state

end Runtime

end

end FormalProof4FHE.HasteBoots.CachedHashHandler
