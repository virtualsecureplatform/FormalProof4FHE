module

public import FormalProof4FHE.HasteBoots.MerkleAvailability
public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.Evolution

@[expose] public section

/-!
# Online evolution of whole Merkle payload extraction

The first-candidate resolver is stable under repeated cached entries. A new
entry whose response is not a reached tree label preserves both the partial
digest tree and every recovered payload. No new exceptional set beyond the
root-reachable digest targets is needed. These are deterministic statements;
an adaptive execution bound is downstream.
-/

open BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.MerklePayloadEvolution

noncomputable section

variable {Input Digest Payload : Type} [DecidableEq Digest]

theorem candidates_append (enc : MerkleOracle.Encoding Input Digest Payload)
    (first rest : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) :
    MerklePayload.candidates enc (first ++ rest) label =
      MerklePayload.candidates enc first label ++ MerklePayload.candidates enc rest label := by
  simp only [MerklePayload.candidates, List.filterMap_append]

/-- An answer unequal to a label contributes no new payload candidate at that label. -/
theorem resolve_append_of_ne (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label response : Digest) (query : Input)
    (different : response ≠ label) :
    MerklePayload.resolve enc (log ++ [⟨query, response⟩]) label = MerklePayload.resolve enc log label := by
  have empty : MerklePayload.candidates enc [⟨query, response⟩] label = [] := by
    simp [MerklePayload.candidates, different]
  simp only [MerklePayload.resolve, candidates_append, empty, List.append_nil]

/-- Repeating an already logged query/answer cannot change first-payload resolution,
even when the log has collisions. -/
theorem resolve_append_of_mem (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (entry : (_input : Input) × Digest)
    (member : entry ∈ log) (label : Digest) :
    MerklePayload.resolve enc (log ++ [entry]) label = MerklePayload.resolve enc log label := by
  have contained : ∀ payload ∈ MerklePayload.candidates enc [entry] label,
      payload ∈ MerklePayload.candidates enc log label := by
    intro payload candidate
    have same := List.mem_singleton.mp ((MerklePayload.mem_candidates_iff enc [entry] label payload).mp candidate)
    apply (MerklePayload.mem_candidates_iff enc log label payload).mpr
    rw [same]
    exact member
  cases old : MerklePayload.candidates enc log label with
  | nil =>
    cases extra : MerklePayload.candidates enc [entry] label with
    | nil => simp only [MerklePayload.resolve, candidates_append, old, extra, List.nil_append]
    | cons head tail =>
      have impossible := contained head (by simp only [extra, List.mem_cons, true_or])
      rw [old] at impossible
      cases impossible
  | cons head tail =>
    simp only [MerklePayload.resolve, candidates_append, old, List.cons_append, List.head?_cons]

/-- An exact cached log entry preserves the partial tree and every payload at once. -/
theorem payloadAt_append_cached (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (entry : (_input : Input) × Digest) (member : entry ∈ log) (idx : SkeletonLeafIndex s) :
    MerkleAvailability.payloadAt enc dummy (log ++ [entry]) root idx =
      MerkleAvailability.payloadAt enc dummy log root idx := by
  have sameTree : MerkleAvailability.tree enc dummy s (log ++ [entry]) root =
      MerkleAvailability.tree enc dummy s log root :=
    tree_append_singleton_eq_of_mem (MerkleOracle.model enc dummy).view s (fun _ => ()) log root entry member
  have sameResolver : MerklePayload.resolve enc (log ++ [entry]) = MerklePayload.resolve enc log := by
    funext label
    exact resolve_append_of_mem enc log entry member label
  simp only [MerkleAvailability.payloadAt, MerkleTreeExtractor.recoverLeaf, sameTree, sameResolver]

/-- A new answer outside the pre-sample target list preserves the entire digest tree. -/
theorem tree_append_outside_targets (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (s : Skeleton) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (query : Input) (response : Digest)
    (outside : response ∉ MerkleAvailability.targets enc dummy s log root) :
    MerkleAvailability.tree enc dummy s (log ++ [⟨query, response⟩]) root =
      MerkleAvailability.tree enc dummy s log root := by
  by_contra changed
  exact outside (tree_ne_append_singleton_implies_response_mem_targets
    (MerkleOracle.model enc dummy).view s (fun _ => ()) log root query response (Ne.symm changed))

/-- The same pre-sample target list also protects every leaf payload resolver. -/
theorem payloadAt_append_outside_targets (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (query : Input) (response : Digest)
    (outside : response ∉ MerkleAvailability.targets enc dummy s log root) (idx : SkeletonLeafIndex s) :
    MerkleAvailability.payloadAt enc dummy (log ++ [⟨query, response⟩]) root idx =
      MerkleAvailability.payloadAt enc dummy log root idx := by
  unfold MerkleAvailability.payloadAt MerkleTreeExtractor.recoverLeaf
  rw [tree_append_outside_targets enc dummy s log root query response outside]
  cases reached : (MerkleAvailability.tree enc dummy s log root).get idx.toNodeIndex with
  | none => rfl
  | some label =>
    have different : response ≠ label := by
      intro equal
      apply outside
      rw [equal]
      exact MerkleAvailability.leaf_mem_targets enc dummy log root idx label reached
    exact resolve_append_of_ne enc log label response query different

/-- The total extracted word is unchanged under a harmless cached query. -/
theorem word_append_cached (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (entry : (_input : Input) × Digest) (member : entry ∈ log) :
    MerkleAvailability.word enc dummy fallback height (log ++ [entry]) root =
      MerkleAvailability.word enc dummy fallback height log root := by
  funext position
  exact congrArg (fun value : Option Payload => value.getD fallback)
    (payloadAt_append_cached enc dummy log root entry member _)

/-- A fresh answer outside the pre-sample root targets preserves the whole total word. -/
theorem word_append_outside_targets (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (query : Input) (response : Digest)
    (outside : response ∉ MerkleAvailability.targets enc dummy (Skeleton.perfect height) log root) :
    MerkleAvailability.word enc dummy fallback height (log ++ [⟨query, response⟩]) root =
      MerkleAvailability.word enc dummy fallback height log root := by
  funext position
  exact congrArg (fun value : Option Payload => value.getD fallback)
    (payloadAt_append_outside_targets enc dummy log root query response outside _)

end

end FormalProof4FHE.HasteBoots.MerklePayloadEvolution
