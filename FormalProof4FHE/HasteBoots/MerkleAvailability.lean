module

public import FormalProof4FHE.HasteBoots.MerklePayload
public import VCVio.CryptoFoundations.MerkleTree.Instability
public import ToMathlib.Data.IndexedBinaryTree.Perfect

@[expose] public section

/-!
# Frozen-prefix payload availability

The entire word is extracted from one prefix log and root, before subsequent
challenges and openings. A later cached authenticated payload disagrees with
that word only if the prefix already contained a hash collision, or a later
fresh query returns a label in one fixed root-reachable target list. The list
has at most 2*L-1 entries and covers every leaf position simultaneously.

This is a deterministic reduction. Target-hit and collision probabilities,
native byte/path refinement, and the protocol's choice of freeze point remain
separate obligations.
-/

open BinaryTree OracleSpec
open MerkleTreeExtractability

namespace FormalProof4FHE.HasteBoots.MerkleAvailability

noncomputable section

variable {Input Digest Payload : Type} [DecidableEq Digest]

/-- Partial digest tree reconstructed exclusively from the frozen prefix. -/
def tree (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (s : Skeleton) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest) :
    FullData (Option Digest) s :=
  MerkleTreeExtractor.tree (MerkleOracle.model enc dummy).view s (fun _ => ()) log root

/-- Reached leaf label followed by prefix-only column-payload recovery. -/
def payloadAt (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (idx : SkeletonLeafIndex s) : Option Payload :=
  MerkleTreeExtractor.recoverLeaf (MerklePayload.resolve enc log) (tree enc dummy s log root) idx

/-- One fixed exceptional set for ALL subsequent openings of the root. -/
def targets (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (s : Skeleton) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest) : List Digest :=
  extractedTargets (MerkleOracle.model enc dummy) s (fun _ => ()) log root

/-- A total available word, with an explicit fallback at unknown payloads. -/
def word (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (fallback : Payload)
    (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (position : Fin (2 ^ height)) : Payload :=
  (payloadAt enc dummy log root (SkeletonLeafIndex.perfectEquiv height position)).getD fallback

omit [DecidableEq Digest] in
/-- Reaching a leaf label puts it in the partial tree's present-label list. -/
theorem leaf_mem_present {s : Skeleton} (t : FullData (Option Digest) s)
    (idx : SkeletonLeafIndex s) (label : Digest) (present : t.get idx.toNodeIndex = some label) :
    label ∈ MerkleTreeExtractor.presentLabels t := by
  induction idx with
  | ofLeaf =>
    cases t with
    | leaf value =>
      change value = some label at present
      simp only [MerkleTreeExtractor.presentLabels, present, Option.toList_some, List.mem_singleton]
  | ofLeft idx ih =>
    cases t with
    | internal root left right =>
      change left.get idx.toNodeIndex = some label at present
      have member := ih left present
      simp only [MerkleTreeExtractor.presentLabels, List.mem_append]
      exact Or.inr (Or.inl member)
  | ofRight idx ih =>
    cases t with
    | internal root left right =>
      change right.get idx.toNodeIndex = some label at present
      have member := ih right present
      simp only [MerkleTreeExtractor.presentLabels, List.mem_append]
      exact Or.inr (Or.inr member)

theorem leaf_mem_targets (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest)
    (idx : SkeletonLeafIndex s) (label : Digest)
    (present : (tree enc dummy s log root).get idx.toNodeIndex = some label) :
    label ∈ targets enc dummy s log root := by
  change label ∈ MerkleTreeExtractor.targetsWith _ s _ root
  rw [MerkleTreeExtractor.targetsWith_eq_presentLabels]
  exact leaf_mem_present _ idx label present

/-- Every complete tree skeleton supplies at most one target per node. -/
theorem targets_length_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (s : Skeleton) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest) :
    (targets enc dummy s log root).length ≤ 2 * s.leafCount - 1 :=
  MerkleTreeExtractor.targets_length_le (MerkleOracle.model enc dummy).view s (fun _ => ()) log root

/-- The native power-of-two column geometry has the same uniform target bound. -/
theorem perfect_targets_length_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest) (root : Digest) :
    (targets enc dummy (Skeleton.perfect height) log root).length ≤ 2 * 2 ^ height - 1 := by
  simpa only [Skeleton.leafCount_perfect] using
    targets_length_le enc dummy (Skeleton.perfect height) log root

/-- Prefix payload recovery is characterized by the represented cache when
that cache has no response collision. -/
theorem resolve_cache_iff (enc : MerkleOracle.Encoding Input Digest Payload)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (cache : (Input →ₒ Digest).QueryCache)
    (represented : LogRepresentsCache log cache) (noCollision : ¬OracleComp.CacheHasCollision cache)
    (label : Digest) (payload : Payload) :
    MerklePayload.resolve enc log label = some payload ↔ cache (enc.leaf () payload) = some label := by
  constructor
  · intro recovered
    exact represented.1 _ (MerklePayload.resolve_spec enc log label payload recovered)
  · intro lookup
    obtain ⟨entry, member, input, output⟩ := represented.2 _ _ lookup
    have entryEqual : entry = (⟨enc.leaf () payload, label⟩ : (_input : Input) × Digest) :=
      Sigma.ext input (heq_of_eq output)
    exact MerklePayload.resolve_of_mem enc log label payload
      (responseInjectiveOn_of_cache_noCollision log cache represented.1 noCollision) (entryEqual ▸ member)

/-- Reordering or repeating a representing log cannot change a resolved payload. -/
theorem resolve_eq_of_represented (enc : MerkleOracle.Encoding Input Digest Payload)
    (log₁ log₂ : MerkleTreeExtractor.QueryLog Input Digest) (cache : (Input →ₒ Digest).QueryCache)
    (rep₁ : LogRepresentsCache log₁ cache) (rep₂ : LogRepresentsCache log₂ cache)
    (noCollision : ¬OracleComp.CacheHasCollision cache) (label : Digest) :
    MerklePayload.resolve enc log₁ label = MerklePayload.resolve enc log₂ label := by
  cases first : MerklePayload.resolve enc log₁ label with
  | none =>
    cases second : MerklePayload.resolve enc log₂ label with
    | none => rfl
    | some payload =>
      have recovered := (resolve_cache_iff enc log₁ cache rep₁ noCollision label payload).mpr
        ((resolve_cache_iff enc log₂ cache rep₂ noCollision label payload).mp second)
      rw [first] at recovered
      cases recovered
  | some payload =>
    exact ((resolve_cache_iff enc log₂ cache rep₂ noCollision label payload).mpr
      ((resolve_cache_iff enc log₁ cache rep₁ noCollision label payload).mp first)).symm

/-- The partial payload at a tree position depends on the frozen cache, not
the presentation order or repetition count of its complete log. -/
theorem payloadAt_eq_of_represented (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (log₁ log₂ : MerkleTreeExtractor.QueryLog Input Digest)
    (cache : (Input →ₒ Digest).QueryCache) (rep₁ : LogRepresentsCache log₁ cache)
    (rep₂ : LogRepresentsCache log₂ cache) (noCollision : ¬OracleComp.CacheHasCollision cache)
    (root : Digest) (idx : SkeletonLeafIndex s) :
    payloadAt enc dummy log₁ root idx = payloadAt enc dummy log₂ root idx := by
  have sameTree : tree enc dummy s log₁ root = tree enc dummy s log₂ root :=
    tree_eq_of_logRepresentsCache (MerkleOracle.model enc dummy).view rep₁ rep₂ noCollision s (fun _ => ()) root
  have sameResolver : MerklePayload.resolve enc log₁ = MerklePayload.resolve enc log₂ := by
    funext label
    exact resolve_eq_of_represented enc log₁ log₂ cache rep₁ rep₂ noCollision label
  simp only [payloadAt, MerkleTreeExtractor.recoverLeaf, sameTree, sameResolver]

/-- One total word per collision-free prefix cache and root, irrespective of log presentation. -/
theorem word_eq_of_represented (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (log₁ log₂ : MerkleTreeExtractor.QueryLog Input Digest)
    (cache : (Input →ₒ Digest).QueryCache) (rep₁ : LogRepresentsCache log₁ cache)
    (rep₂ : LogRepresentsCache log₂ cache) (noCollision : ¬OracleComp.CacheHasCollision cache) (root : Digest) :
    word enc dummy fallback height log₁ root = word enc dummy fallback height log₂ root := by
  funext position
  exact congrArg (fun value : Option Payload => value.getD fallback)
    (payloadAt_eq_of_represented enc dummy log₁ log₂ cache rep₁ rep₂ noCollision root _)

/-- An accepted later payload that is absent or different in the frozen-prefix
extraction exposes a prefix collision or a later hit on a prefix-fixed target. -/
theorem payload_disagreement (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (log : MerkleTreeExtractor.QueryLog Input Digest)
    (cacheCommit cacheFinal : (Input →ₒ Digest).QueryCache) (root label : Digest)
    (idx : SkeletonLeafIndex s) (proof : List.Vector Digest idx.depth) (payload : Payload)
    (represented : LogRepresentsCache log cacheCommit) (monotone : cacheCommit ≤ cacheFinal)
    (chain : ChainInCache (MerkleOracle.model enc dummy) (fun _ => ())
      cacheFinal label root idx proof)
    (leafHash : cacheFinal (enc.leaf () payload) = some label)
    (different : payloadAt enc dummy log root idx ≠ some payload) :
    OracleComp.CacheHasCollision cacheCommit ∨
      ∃ target ∈ targets enc dummy s log root, CacheAddsValue cacheCommit cacheFinal target := by
  classical
  by_cases collision : OracleComp.CacheHasCollision cacheCommit
  · exact Or.inl collision
  right
  by_cases sameLeaf : (tree enc dummy s log root).get idx.toNodeIndex = some label
  · cases previous : cacheCommit (enc.leaf () payload) with
    | none =>
      exact ⟨label, leaf_mem_targets enc dummy log root idx label sameLeaf,
        enc.leaf () payload, leafHash, previous⟩
    | some value =>
      have equal : value = label := Option.some.inj ((monotone previous).symm.trans leafHash)
      subst value
      obtain ⟨entry, member, input, output⟩ := represented.2 _ _ previous
      have entryEqual : entry = (⟨enc.leaf () payload, label⟩ : (_input : Input) × Digest) :=
        Sigma.ext input (heq_of_eq output)
      have leafMember := entryEqual ▸ member
      have recovered := MerklePayload.resolve_of_mem enc log label payload
        (responseInjectiveOn_of_cache_noCollision log cacheCommit represented.1 collision) leafMember
      apply False.elim
      apply different
      simp only [payloadAt, MerkleTreeExtractor.recoverLeaf, sameLeaf, Option.bind_some, recovered]
  · exact fresh_extractedTarget_of_extractor_disagreement (MerkleOracle.model enc dummy)
      (fun _ => ()) idx log cacheCommit cacheFinal root label proof
      represented.1 represented.2 collision monotone chain (Or.inl (fun equal => sameLeaf equal.symm))

/-- Any selected native column must agree with the single frozen total word,
unless one of the same root-wide exceptional events occurs. -/
theorem word_disagreement (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest)
    (cacheCommit cacheFinal : (Input →ₒ Digest).QueryCache) (root label : Digest)
    (position : Fin (2 ^ height))
    (proof : List.Vector Digest (SkeletonLeafIndex.perfectEquiv height position).depth)
    (payload : Payload) (represented : LogRepresentsCache log cacheCommit)
    (monotone : cacheCommit ≤ cacheFinal)
    (chain : ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) cacheFinal label root
      (SkeletonLeafIndex.perfectEquiv height position) proof)
    (leafHash : cacheFinal (enc.leaf () payload) = some label)
    (different : word enc dummy fallback height log root position ≠ payload) :
    OracleComp.CacheHasCollision cacheCommit ∨
      ∃ target ∈ targets enc dummy (Skeleton.perfect height) log root,
        CacheAddsValue cacheCommit cacheFinal target := by
  apply payload_disagreement enc dummy log cacheCommit cacheFinal root label _ proof payload
    represented monotone chain leafHash
  intro recovered
  apply different
  simp only [word, recovered, Option.getD_some]

/-- Away from the explicitly identified hash exceptions, every authenticated
column equals the same frozen word, even when its position is chosen later. -/
theorem word_eq_of_no_exception (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (log : MerkleTreeExtractor.QueryLog Input Digest)
    (cacheCommit cacheFinal : (Input →ₒ Digest).QueryCache) (root label : Digest)
    (position : Fin (2 ^ height))
    (proof : List.Vector Digest (SkeletonLeafIndex.perfectEquiv height position).depth)
    (payload : Payload) (represented : LogRepresentsCache log cacheCommit)
    (monotone : cacheCommit ≤ cacheFinal)
    (chain : ChainInCache (MerkleOracle.model enc dummy) (fun _ => ()) cacheFinal label root
      (SkeletonLeafIndex.perfectEquiv height position) proof)
    (leafHash : cacheFinal (enc.leaf () payload) = some label)
    (noCollision : ¬OracleComp.CacheHasCollision cacheCommit)
    (noTargets : ∀ target ∈ targets enc dummy (Skeleton.perfect height) log root,
      ¬CacheAddsValue cacheCommit cacheFinal target) :
    word enc dummy fallback height log root position = payload := by
  by_contra different
  obtain bad | ⟨target, member, hit⟩ := word_disagreement enc dummy fallback height log
    cacheCommit cacheFinal root label position proof payload represented monotone chain leafHash different
  · exact noCollision bad
  · exact noTargets target member hit

end

end FormalProof4FHE.HasteBoots.MerkleAvailability
