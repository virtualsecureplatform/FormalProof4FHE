module

public import FormalProof4FHE.HasteBoots.MerkleAvailability
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# One-step hazard for frozen Merkle availability targets

The fresh query may depend on the entire preceding cache. Provided no earlier
fresh query hit the frozen target list, a new availability exception occurs
exactly when the next uniform response belongs to that list. Prefix collisions
and accumulation over adaptive executions still require separate accounting.
-/

open OracleSpec ProbabilityTheory MerkleTreeExtractability BinaryTree

namespace FormalProof4FHE.HasteBoots.MerkleAvailabilityProbability

variable {Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]

omit [DecidableEq Digest] in
/-- Exact first-target-hit event after one fresh cache update. -/
theorem adds_target_after_update (before current : (Input →ₒ Digest).QueryCache)
    (monotone : before ≤ current) (targetList : List Digest) (query : Input) (answer : Digest)
    (fresh : current query = none)
    (noPrevious : ∀ target ∈ targetList, ¬CacheAddsValue before current target) :
    (∃ target ∈ targetList,
      CacheAddsValue before (current.cacheQuery query answer) target) ↔ answer ∈ targetList := by
  have beforeFresh : before query = none := by
    cases previous : before query with
    | none => rfl
    | some value =>
      have present := monotone previous
      rw [fresh] at present
      cases present
  constructor
  · rintro ⟨target, member, input, returned, unknown⟩
    by_cases equal : input = query
    · subst input
      rw [OracleSpec.QueryCache.cacheQuery_self] at returned
      have same : answer = target := Option.some.inj returned
      exact same.symm ▸ member
    · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ equal] at returned
      exact (noPrevious target member ⟨input, returned, unknown⟩).elim
  · intro member
    exact ⟨answer, member, query, OracleSpec.QueryCache.cacheQuery_self _ _ _, beforeFresh⟩

omit [DecidableEq Input] in
/-- A uniform response hits the prefix-fixed target set with at most one atom
per reached node. Duplicated labels only reduce this probability. -/
theorem uniform_target_bound [Fintype Digest] [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : ℕ)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest) :
    Pr{let answer ← $ᵗ Digest}[
      answer ∈ MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root] ≤
      ((2 * 2 ^ height - 1 : ℕ) : ENNReal) / Fintype.card Digest := by
  classical
  apply (SampleableType.prEvent_uniformSample_le_div_iff _).mpr
  have count : (Finset.univ.filter (fun answer =>
      answer ∈ MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root)).card =
      (MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root).toFinset.card := by
    congr 1
    ext answer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  rw [count]
  exact (List.toFinset_card_le _).trans
    (MerkleAvailability.perfect_targets_length_le enc dummy height log root)

/-- Conditional one-fresh-query availability hazard, without conditioning on
the identity of a later selected leaf, sibling path, or response payload. -/
theorem fresh_update_bound [Fintype Digest] [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (height : ℕ)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (before current : (Input →ₒ Digest).QueryCache) (monotone : before ≤ current)
    (query : Input) (fresh : current query = none)
    (noPrevious : ∀ target ∈ MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root,
      ¬CacheAddsValue before current target) :
    Pr{let answer ← $ᵗ Digest}[
      ∃ target ∈ MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root,
        CacheAddsValue before (current.cacheQuery query answer) target] ≤
      ((2 * 2 ^ height - 1 : ℕ) : ENNReal) / Fintype.card Digest := by
  exact (prEvent_mono _ _ _ (fun answer event =>
    (adds_target_after_update before current monotone _ query answer fresh noPrevious).mp event)).trans
      (uniform_target_bound enc dummy height log root)

end FormalProof4FHE.HasteBoots.MerkleAvailabilityProbability
