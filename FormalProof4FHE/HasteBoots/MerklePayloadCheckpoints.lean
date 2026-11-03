module

public import FormalProof4FHE.HasteBoots.MerklePayloadEvolution
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.OnlineInvariant

@[expose] public section

/-!
# Stateful stability of whole-column Merkle checkpoints

Use VCVio's existing heterogeneous checkpoint state and shared target union.
The additional invariant preserves every recovered payload as well as the
digest tree. Recording an adaptively chosen root is valid at any current stable
log; no predetermined root values, phase lengths or independent oracle roles
are required. Probability and cost accumulation are downstream.
-/

open BinaryTree MerkleTreeMultiExtractability OracleSpec MerkleTreeExtractability

namespace FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Digest]

/-- Concrete native nodes are unaddressed; configuration tags still determine tree shape. -/
def configuration (shape : Cfg → Skeleton) : Configuration Cfg Unit where
  skeleton := shape
  addressKey _ _ := ()

abbrev State (shape : Cfg → Skeleton) := ExtractorState Cfg Input Unit Digest (configuration shape)

/-- Every immutable checkpoint still agrees with extraction at the current log,
both for digests and for every optional whole-column payload. -/
structure StableAt (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) : Prop where
  digest : state.StableAt (MerkleOracle.model enc dummy).view log
  payloads : ∀ tag checkpoint, ⟨tag, checkpoint⟩ ∈ state.checkpoints →
    ∀ idx : SkeletonLeafIndex (shape tag),
      MerkleAvailability.payloadAt enc dummy checkpoint.cumulativeLog checkpoint.root idx =
        MerkleAvailability.payloadAt enc dummy log checkpoint.root idx

/-- The empty extraction history is stable at every current log. -/
theorem stable_empty (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (log : MerkleTreeExtractor.QueryLog Input Digest) :
    StableAt enc dummy shape (ExtractorState.empty : State shape) log := by
  refine ⟨ExtractorState.stableAt_empty (MerkleOracle.model enc dummy).view (configuration shape) log, ?_⟩
  intro tag checkpoint member
  simp only [ExtractorState.empty_checkpoints, List.not_mem_nil] at member

/-- Cache-hit log entries preserve all recorded payload extractions. -/
theorem stable_append_cached (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (query : Input) (response : Digest)
    (member : (⟨query, response⟩ : (_input : Input) × Digest) ∈ log) :
    StableAt enc dummy shape state (log ++ [⟨query, response⟩]) := by
  refine ⟨stable.digest.append_cached (MerkleOracle.model enc dummy).view query response member, ?_⟩
  intro tag checkpoint recorded idx
  exact (stable.payloads tag checkpoint recorded idx).trans
    (MerklePayloadEvolution.payloadAt_append_cached enc dummy log checkpoint.root _ member idx).symm

/-- A fresh response outside the pre-sample live target union preserves all
checkpoint trees and payloads, with the same target set for both properties. -/
theorem stable_append_outside_live (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (query : Input) (response : Digest)
    (outside : response ∉ state.liveTargetSet (MerkleOracle.model enc dummy).view log) :
    StableAt enc dummy shape state (log ++ [⟨query, response⟩]) := by
  refine ⟨stable.digest.append_of_not_mem_liveTargetSet (MerkleOracle.model enc dummy).view query response outside, ?_⟩
  intro tag checkpoint recorded idx
  have avoidsRoot : response ∉ MerkleAvailability.targets enc dummy (shape tag) log checkpoint.root := by
    intro hit
    apply outside
    simp only [ExtractorState.liveTargetSet, List.mem_toFinset, ExtractorState.liveTargetList, List.mem_flatMap]
    exact ⟨⟨tag, checkpoint⟩, recorded, hit⟩
  exact (stable.payloads tag checkpoint recorded idx).trans
    (MerklePayloadEvolution.payloadAt_append_outside_targets enc dummy log checkpoint.root
      query response avoidsRoot idx).symm

/-- Under stability, recomputing the live union does not enlarge the frozen target set. -/
theorem live_targets_eq_frozen (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log) :
    state.liveTargetSet (MerkleOracle.model enc dummy).view log =
      state.targetSet (MerkleOracle.model enc dummy).view :=
  stable.digest.liveTargetSet_eq_targetSet (MerkleOracle.model enc dummy).view

theorem stable_append_outside_frozen (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (query : Input) (response : Digest)
    (outside : response ∉ state.targetSet (MerkleOracle.model enc dummy).view) :
    StableAt enc dummy shape state (log ++ [⟨query, response⟩]) := by
  apply stable_append_outside_live enc dummy shape state log stable query response
  rwa [live_targets_eq_frozen enc dummy shape state log stable]

/-- A newly recorded root is stable by construction at its current cumulative log. -/
theorem stable_record (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (tag : Cfg) (root : Digest) :
    StableAt enc dummy shape (state.recordCumulative tag log root) log := by
  refine ⟨stable.digest.recordCumulative (MerkleOracle.model enc dummy).view tag log root, ?_⟩
  intro recordedTag checkpoint recorded idx
  rw [ExtractorState.recordCumulative_checkpoints] at recorded
  obtain old | new := List.mem_append.mp recorded
  · exact stable.payloads recordedTag checkpoint old idx
  · simp only [List.mem_singleton] at new
    cases new
    rfl

/-- Same configuration and root imply the same payload source across all its
recorded checkpoints at a common stable log. -/
theorem same_root_payloads (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (tag : Cfg) (first second : Checkpoint Input Digest (configuration shape) tag)
    (firstRecorded : ⟨tag, first⟩ ∈ state.checkpoints) (secondRecorded : ⟨tag, second⟩ ∈ state.checkpoints)
    (sameRoot : first.root = second.root) (idx : SkeletonLeafIndex (shape tag)) :
    MerkleAvailability.payloadAt enc dummy first.cumulativeLog first.root idx =
      MerkleAvailability.payloadAt enc dummy second.cumulativeLog second.root idx := by
  calc _ = MerkleAvailability.payloadAt enc dummy log first.root idx := stable.payloads tag first firstRecorded idx
       _ = MerkleAvailability.payloadAt enc dummy log second.root idx := by rw [sameRoot]
       _ = _ := (stable.payloads tag second secondRecorded idx).symm

/-- Whole-suffix stability permits target-valued cache hits. Only a target
returned under an input absent at the beginning of the suffix can destabilize
a checkpoint. Suffix length and query positions are unrestricted. -/
theorem stable_append_no_fresh_target (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (suffix : MerkleTreeExtractor.QueryLog Input Digest)
    (initialCache finalCache : (Input →ₒ Digest).QueryCache)
    (cacheLog : ∀ input value, initialCache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (monotone : initialCache ≤ finalCache)
    (suffixFinal : ∀ entry ∈ suffix, finalCache entry.1 = some entry.2)
    (noFresh : ∀ target ∈ state.targetSet (MerkleOracle.model enc dummy).view,
      ¬CacheAddsValue initialCache finalCache target) :
    StableAt enc dummy shape state (log ++ suffix) := by
  induction suffix generalizing log with
  | nil => simpa only [List.append_nil] using stable
  | cons entry suffix ih =>
    have nextStable : StableAt enc dummy shape state (log ++ [entry]) := by
      by_cases outside : entry.2 ∉ state.targetSet (MerkleOracle.model enc dummy).view
      · exact stable_append_outside_frozen enc dummy shape state log stable entry.1 entry.2 outside
      · have target : entry.2 ∈ state.targetSet (MerkleOracle.model enc dummy).view := Classical.not_not.mp outside
        cases previous : initialCache entry.1 with
        | none =>
          exact (noFresh entry.2 target ⟨entry.1,
            suffixFinal entry List.mem_cons_self, previous⟩).elim
        | some value =>
          have same : value = entry.2 := Option.some.inj
            ((monotone previous).symm.trans (suffixFinal entry List.mem_cons_self))
          subst value
          obtain ⟨cached, member, input, output⟩ := cacheLog entry.1 entry.2 previous
          have sameEntry : cached = entry := Sigma.ext input (heq_of_eq output)
          exact stable_append_cached enc dummy shape state log stable entry.1 entry.2
            (sameEntry ▸ member)
    have cacheLogNext : ∀ input value, initialCache input = some value →
        ∃ cached ∈ log ++ [entry], cached.1 = input ∧ cached.2 = value := by
      intro input value known
      obtain ⟨cached, member, inputEqual, outputEqual⟩ := cacheLog input value known
      exact ⟨cached, List.mem_append_left _ member, inputEqual, outputEqual⟩
    have suffixFinalTail : ∀ next ∈ suffix, finalCache next.1 = some next.2 := by
      intro next member
      exact suffixFinal next (List.mem_cons_of_mem _ member)
    simpa only [List.append_assoc, List.singleton_append] using
      ih (log ++ [entry]) nextStable cacheLogNext suffixFinalTail

/-- Any eventual change of a recorded tree or payload exposes a fresh hit on
the same target union fixed at the beginning of the suffix. -/
theorem fresh_target_of_not_stable_append (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (state : State (Input := Input) (Digest := Digest) shape)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (stable : StableAt enc dummy shape state log)
    (suffix : MerkleTreeExtractor.QueryLog Input Digest)
    (initialCache finalCache : (Input →ₒ Digest).QueryCache)
    (cacheLog : ∀ input value, initialCache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (monotone : initialCache ≤ finalCache)
    (suffixFinal : ∀ entry ∈ suffix, finalCache entry.1 = some entry.2)
    (changed : ¬StableAt enc dummy shape state (log ++ suffix)) :
    ∃ target ∈ state.targetSet (MerkleOracle.model enc dummy).view,
      CacheAddsValue initialCache finalCache target := by
  classical
  by_contra absent
  apply changed
  apply stable_append_no_fresh_target enc dummy shape state log stable suffix
    initialCache finalCache cacheLog monotone suffixFinal
  intro target member hit
  exact absent ⟨target, member, hit⟩

end

end FormalProof4FHE.HasteBoots.MerklePayloadCheckpoints
