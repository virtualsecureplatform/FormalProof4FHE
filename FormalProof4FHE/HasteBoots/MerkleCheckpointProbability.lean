module

public import FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Shared-log hazard for all recorded Merkle payload sources

The live target union has at most the smaller of the full checkpoint node
budget and two labels per populated complete query plus one per checkpoint.
The same bound protects both digest trees and whole-column payloads. This
one-step law is conditioned only on the pre-answer state; the caller still
has to connect native executions and accumulate losses with their work cost.
-/

open BinaryTree ProbabilityTheory MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.MerkleCheckpointProbability

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]
  [Fintype Digest] [SampleableType Digest]

/-- Deduplicated root-wide targets use the actual shared cache-key cover. -/
theorem live_target_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (cache : Input → Option Digest)
    (keys : Finset Input) (cover : LogCacheKeysCover log cache keys) :
    Pr{let answer ← $ᵗ Digest}[
      answer ∈ state.liveTargetSet (MerkleOracle.model enc dummy).view log] ≤
      ((min state.totalNodeBudget (2 * keys.card + state.checkpoints.length) : ℕ) : ENNReal) /
        Fintype.card Digest := by
  classical
  apply (SampleableType.prEvent_uniformSample_le_div_iff _).mpr
  have count : (Finset.univ.filter (fun answer =>
      answer ∈ state.liveTargetSet (MerkleOracle.model enc dummy).view log)).card =
      (state.liveTargetSet (MerkleOracle.model enc dummy).view log).card := by
    congr 1
    ext answer
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [count]
  simpa only [sharedExtractedLabelCountBound] using
    state.liveTargetSet_card_le_sharedExtractedLabelCountBound_of_cover
      (MerkleOracle.model enc dummy).view log cache keys keys.card le_rfl cover

/-- The same single fresh answer cannot destabilize any recorded payload source
except by hitting the pre-sample shared target union. Roots and the next query
may already depend on the entire visible preceding execution. -/
theorem destabilization_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (cache : Input → Option Digest)
    (keys : Finset Input) (cover : LogCacheKeysCover log cache keys)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape state log) (query : Input) :
    Pr{let answer ← $ᵗ Digest}[
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape state (log ++ [⟨query, answer⟩])] ≤
      ((min state.totalNodeBudget (2 * keys.card + state.checkpoints.length) : ℕ) : ENNReal) /
        Fintype.card Digest := by
  have included : ∀ answer,
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape state (log ++ [⟨query, answer⟩]) →
        answer ∈ state.liveTargetSet (MerkleOracle.model enc dummy).view log := by
    intro answer changed
    by_contra outside
    exact changed (MerklePayloadCheckpoints.stable_append_outside_live enc dummy shape state log stable
      query answer outside)
  exact (prEvent_mono _ _ _ included).trans (live_target_bound enc dummy shape state log cache keys cover)

end

end FormalProof4FHE.HasteBoots.MerkleCheckpointProbability
