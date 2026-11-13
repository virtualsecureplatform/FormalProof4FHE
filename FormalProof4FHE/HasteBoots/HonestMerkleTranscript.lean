module
public import FormalProof4FHE.HasteBoots.MerkleAvailability
public import VCVio.CryptoFoundations.MerkleTree.Hashing.Defs
public import ToMathlib.Data.IndexedBinaryTree.Lemmas
@[expose] public section

/-! Honest payload commitments use the existing effectful Merkle builder and
the same unaddressed hash-input domain as verification. The computed transcript
recovers the committed payloads without a supplied word-equality certificate. -/
namespace FormalProof4FHE.HasteBoots.HonestMerkleTranscript
open BinaryTree OracleSpec OracleComp
noncomputable section
variable {Input Digest Payload : Type}

/-- Both leaves and nodes query the same encoded-input oracle. -/
def program (enc : MerkleOracle.Encoding Input Digest Payload) {s : Skeleton}
    (payloads : LeafData Payload s) : OracleComp (Input →ₒ Digest) (FullData Digest s) :=
  AddressedMerkleTree.buildMerkleTreeAddressedM
    (fun index => (Input →ₒ Digest).query (enc.leaf () (payloads.get index)))
    (fun _ left right => (Input →ₒ Digest).query (enc.node () (left,right)))

/-- The deterministic tree uses the same bottom-up builder as the oracle program. -/
def tree (enc : MerkleOracle.Encoding Input Digest Payload) (hash : Input → Digest)
    {s : Skeleton} (payloads : LeafData Payload s) : FullData Digest s :=
  populateUp (payloads.map (fun payload => hash (enc.leaf () payload)))
    (fun left right => hash (enc.node () (left,right)))

/-- All actual queries, in left-subtree/right-subtree/parent order. -/
def queries (enc : MerkleOracle.Encoding Input Digest Payload) :
    {s : Skeleton} → LeafData Payload s → FullData Digest s → MerkleTreeExtractor.QueryLog Input Digest
  | .leaf, .leaf payload, .leaf label => [⟨enc.leaf () payload,label⟩]
  | .internal _ _, .internal left right, .internal root leftTree rightTree =>
      queries enc left leftTree ++ queries enc right rightTree ++
        [⟨enc.node () (leftTree.getRootValue,rightTree.getRootValue),root⟩]

/-- A deterministic oracle interpreter that retains every query, including repeats. -/
def handler (hash : Input → Digest) :
    QueryImpl (Input →ₒ Digest) (StateT (MerkleTreeExtractor.QueryLog Input Digest) Id) :=
  fun input => StateT.mk fun log => (hash input,log ++ [⟨input,hash input⟩])

/-- Executing the existing builder generates precisely the computed tree and
transcript. No role separation or collision-freedom premise is needed here. -/
theorem run (enc : MerkleOracle.Encoding Input Digest Payload) (hash : Input → Digest)
    {s : Skeleton} (payloads : LeafData Payload s)
    (before : MerkleTreeExtractor.QueryLog Input Digest) :
    (simulateQ (handler hash) (program enc payloads)).run before =
      (tree enc hash payloads,before ++ queries enc payloads (tree enc hash payloads)) := by
  induction payloads generalizing before with
  | leaf payload =>
      simp [program,AddressedMerkleTree.buildMerkleTreeAddressedM,tree,handler,queries]
      rfl
  | internal left right ihLeft ihRight =>
      simp only [program,AddressedMerkleTree.buildMerkleTreeAddressedM,simulateQ_bind,simulateQ_pure]
      change (do
        let l ← simulateQ (handler hash) (program enc left)
        let r ← simulateQ (handler hash) (program enc right)
        let root ← handler hash (enc.node () (l.getRootValue,r.getRootValue))
        pure (FullData.internal root l r)).run before = _
      simp [StateT.run_bind,ihLeft,ihRight,handler,tree,queries,List.append_assoc]
      dsimp only [Bind.bind,Functor.map]
      simp only [List.append_assoc]

/-- Every generated observation is an answer of the very same hash function. -/
theorem answered (enc : MerkleOracle.Encoding Input Digest Payload) (hash : Input → Digest)
    {s : Skeleton} (payloads : LeafData Payload s) :
    ∀ entry ∈ queries enc payloads (tree enc hash payloads), entry.2 = hash entry.1 := by
  induction payloads with
  | leaf payload =>
      intro entry member
      have equal : entry = ⟨enc.leaf () payload,hash (enc.leaf () payload)⟩ := by
        simpa only [tree,LeafData.map,populateUp,queries,List.mem_singleton] using member
      subst entry
      rfl
  | internal left right ihLeft ihRight =>
      intro entry member
      simp only [tree,LeafData.map,populateUp,queries,List.mem_append,List.mem_singleton] at member
      rcases member with (leftMember | rightMember) | parent
      · exact ihLeft entry leftMember
      · exact ihRight entry rightMember
      · cases parent
        rfl

/-- One query per leaf and one per internal node, including repeated inputs. -/
theorem query_count (enc : MerkleOracle.Encoding Input Digest Payload)
    {s : Skeleton} (payloads : LeafData Payload s) (labels : FullData Digest s) :
    (queries enc payloads labels).length + 1 = 2*s.leafCount := by
  induction payloads with
  | leaf payload => cases labels; rfl
  | internal left right ihLeft ihRight =>
      cases labels with
      | internal root leftTree rightTree =>
          have leftCount := ihLeft leftTree
          have rightCount := ihRight rightTree
          simp only [queries,List.length_append,List.length_singleton,Skeleton.leafCount]
          omega

/-- The transcript contains the complete leaf query at each typed position. -/
theorem leaf_query (enc : MerkleOracle.Encoding Input Digest Payload)
    {s : Skeleton} (payloads : LeafData Payload s) (labels : FullData Digest s)
    (index : SkeletonLeafIndex s) :
    (⟨enc.leaf () (payloads.get index),labels.get index.toNodeIndex⟩ : (_ : Input) × Digest) ∈
      queries enc payloads labels := by
  induction index with
  | ofLeaf => cases payloads; cases labels; exact List.mem_singleton_self _
  | ofLeft index ih =>
      cases payloads with
      | internal left right =>
          cases labels with
          | internal root leftTree rightTree =>
              exact List.mem_append_left _ (List.mem_append_left _ (ih left leftTree))
  | ofRight index ih =>
      cases payloads with
      | internal left right =>
          cases labels with
          | internal root leftTree rightTree =>
              exact List.mem_append_left _ (List.mem_append_right _ (ih right rightTree))

variable [DecidableEq Digest]

/-- The existing transcript extractor recovers the whole committed digest
tree. A larger log may interleave other roles and repeat existing queries. -/
theorem extracted_tree (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (payloads : LeafData Payload s) (labels : FullData Digest s)
    (log : MerkleTreeExtractor.QueryLog Input Digest)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (included : ∀ entry ∈ queries enc payloads labels, entry ∈ log) :
    MerkleAvailability.tree enc dummy s log labels.getRootValue = labels.map some := by
  induction payloads with
  | leaf payload => cases labels; rfl
  | @internal leftShape rightShape left right ihLeft ihRight =>
      cases labels with
      | internal root leftTree rightTree =>
          have leftIncluded : ∀ entry ∈ queries enc left leftTree, entry ∈ log := by
            intro entry member
            exact included entry (List.mem_append_left _ (List.mem_append_left _ member))
          have rightIncluded : ∀ entry ∈ queries enc right rightTree, entry ∈ log := by
            intro entry member
            exact included entry (List.mem_append_left _ (List.mem_append_right _ member))
          have parent : (⟨enc.node () (leftTree.getRootValue,rightTree.getRootValue),root⟩ : (_ : Input) × Digest) ∈ log :=
            included _ (List.mem_append_right _ (List.mem_singleton_self _))
          have resolved := MerkleTreeExtractor.children_eq_some_of_mem_of_responseInjectiveOn
            (MerkleOracle.model enc dummy).view log () root
            ((MerkleOracle.model enc dummy).mkQuery () (leftTree.getRootValue,rightTree.getRootValue))
            rfl parent injective
          rw [(MerkleOracle.model enc dummy).input_mkQuery] at resolved
          change MerkleTreeExtractor.treeWith
            (MerkleTreeExtractor.children (MerkleOracle.model enc dummy).view log)
            (.internal leftShape rightShape) (fun _ => ()) root = _
          rw [MerkleTreeExtractor.treeWith,resolved]
          change FullData.internal (some root)
            (MerkleAvailability.tree enc dummy leftShape log leftTree.getRootValue)
            (MerkleAvailability.tree enc dummy rightShape log rightTree.getRootValue) =
              FullData.internal (some root) (leftTree.map some) (rightTree.map some)
          rw [ihLeft leftTree leftIncluded,ihRight rightTree rightIncluded]

/-- Payload recovery is exact, including leaf/node encoding overlaps. Only
injectivity of responses in the actual supplied log is required. -/
theorem payload_recovered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    {s : Skeleton} (payloads : LeafData Payload s) (labels : FullData Digest s)
    (log : MerkleTreeExtractor.QueryLog Input Digest)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (included : ∀ entry ∈ queries enc payloads labels, entry ∈ log)
    (index : SkeletonLeafIndex s) :
    MerkleAvailability.payloadAt enc dummy log labels.getRootValue index = some (payloads.get index) := by
  unfold MerkleAvailability.payloadAt MerkleTreeExtractor.recoverLeaf
  rw [extracted_tree enc dummy payloads labels log injective included,FullData.get_map]
  exact MerklePayload.resolve_of_mem enc log _ _ injective
    (included _ (leaf_query enc payloads labels index))

/-- The verifier's total available word is the committed payload vector. -/
theorem word_recovered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (fallback : Payload) (height : ℕ) (payloads : LeafData Payload (.perfect height))
    (labels : FullData Digest (.perfect height)) (log : MerkleTreeExtractor.QueryLog Input Digest)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log)
    (included : ∀ entry ∈ queries enc payloads labels, entry ∈ log)
    (position : Fin (2^height)) :
    MerkleAvailability.word enc dummy fallback height log labels.getRootValue position =
      payloads.get (SkeletonLeafIndex.perfectEquiv height position) := by
  unfold MerkleAvailability.word
  rw [payload_recovered enc dummy payloads labels log injective included]
  rfl

end
end FormalProof4FHE.HasteBoots.HonestMerkleTranscript
