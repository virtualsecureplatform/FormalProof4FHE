module

public import FormalProof4FHE.HasteBoots.CachedHashHandler
public import VCVio.OracleComp.QueryTracking.Birthday

@[expose] public section

/-!
# Collisions in the concrete shared cached hash

A cache hit has no collision loss. From a coherent collision-free cache, a
fresh uniform answer creates a collision with probability at most the actual
number of populated keys divided by the digest alphabet size. Inputs need
not form a finite type. Cache growth preserves any collision already present.
-/

open OracleSpec OracleComp ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.CachedHashCollision

noncomputable section

variable {Input Digest : Type} [DecidableEq Input]

omit [DecidableEq Input] in
/-- Collisions cannot be erased by extending an existing cache. -/
theorem collision_mono (before after : (Input →ₒ Digest).QueryCache)
    (monotone : before ≤ after) (collision : CacheHasCollision before) :
    CacheHasCollision after := by
  obtain ⟨first, second, firstValue, secondValue, distinct, firstKnown, secondKnown, equal⟩ := collision
  exact ⟨first, second, firstValue, secondValue, distinct, monotone firstKnown, monotone secondKnown, equal⟩

omit [DecidableEq Input] in
theorem no_collision_empty : ¬CacheHasCollision (CachedHashHandler.empty : CachedHashHandler.State Input Digest).cache := by
  rintro ⟨first, second, firstValue, secondValue, distinct, firstKnown, secondKnown, equal⟩
  cases firstKnown

section Runtime

variable [SampleableType Digest]

/-- The concrete handler never overwrites an earlier answer. -/
theorem cache_monotone_step (query : Input) (state : CachedHashHandler.State Input Digest)
    (result : Digest × CachedHashHandler.State Input Digest)
    (supported : result ∈ support ((CachedHashHandler.handler query).run state)) :
    state.cache ≤ result.2.cache := by
  cases known : state.cache query with
  | none =>
      rw [CachedHashHandler.run_fresh state query known, support_map, Set.mem_image] at supported
      obtain ⟨answer, _, equal⟩ := supported
      subst result
      exact QueryCache.le_cacheQuery state.cache known
  | some answer =>
      rw [CachedHashHandler.run_cached state query answer known, mem_support_pure_iff] at supported
      subst result
      exact le_rfl

/-- Cache growth holds through every adaptive hash program, without a query bound. -/
theorem cache_monotone_run {Result : Type} (program : OracleComp (Input →ₒ Digest) Result)
    (state : CachedHashHandler.State Input Digest)
    (result : Result × CachedHashHandler.State Input Digest)
    (supported : result ∈ support ((simulateQ CachedHashHandler.handler program).run state)) :
    state.cache ≤ result.2.cache := by
  apply simulateQ_run_preserves_inv_of_query CachedHashHandler.handler
    (fun current => state.cache ≤ current.cache) ?_ program state le_rfl result supported
  intro query current prior next present
  exact prior.trans (cache_monotone_step query current next present)

/-- Returning the cached answer cannot introduce a collision. -/
theorem cached_loss_zero (state : CachedHashHandler.State Input Digest)
    (noCollision : ¬CacheHasCollision state.cache) (query : Input) (answer : Digest)
    (known : state.cache query = some answer) :
    Pr{let result ← (CachedHashHandler.handler query).run state}[CacheHasCollision result.2.cache] = 0 := by
  rw [CachedHashHandler.run_cached state query answer known]
  apply prEvent_eq_zero_of_forall_mem_support
  intro result supported collision
  have equal := eq_of_mem_support_pure _ supported
  subst result
  exact noCollision collision

variable [Fintype Digest]

/-- The birthday step uses the exact current key cover, including all oracle roles. -/
theorem fresh_loss_bound (state : CachedHashHandler.State Input Digest)
    (coherent : CachedHashHandler.Coherent state) (noCollision : ¬CacheHasCollision state.cache)
    (query : Input) (fresh : state.cache query = none) :
    Pr{let result ← (CachedHashHandler.handler query).run state}[CacheHasCollision result.2.cache] ≤
      (state.keys.card : ENNReal) / Fintype.card Digest := by
  classical
  rw [CachedHashHandler.run_fresh state query fresh, prEvent_map]
  apply (SampleableType.prEvent_uniformSample_le_div_iff _).mpr
  apply card_responses_creating_cacheCollision_le noCollision
  intro input populated
  cases known : state.cache input with
  | none => exact (populated known).elim
  | some value => exact (coherent.mem_keys_iff input).mpr ⟨value, known⟩

/-- No artificial query cap; only a fresh input contributes collision loss. -/
def loss (query : Input) (state : CachedHashHandler.State Input Digest) : ENNReal :=
  if state.cache query = none then (state.keys.card : ENNReal) / Fintype.card Digest else 0

theorem step_loss_bound (state : CachedHashHandler.State Input Digest)
    (coherent : CachedHashHandler.Coherent state) (noCollision : ¬CacheHasCollision state.cache)
    (query : Input) :
    Pr{let result ← (CachedHashHandler.handler query).run state}[CacheHasCollision result.2.cache] ≤
      loss query state := by
  unfold loss
  cases known : state.cache query with
  | none =>
      simp only [reduceIte]
      exact fresh_loss_bound state coherent noCollision query known
  | some answer =>
      simp only [reduceCtorEq, reduceIte]
      exact le_of_eq (cached_loss_zero state noCollision query answer known)

end Runtime

end

end FormalProof4FHE.HasteBoots.CachedHashCollision
