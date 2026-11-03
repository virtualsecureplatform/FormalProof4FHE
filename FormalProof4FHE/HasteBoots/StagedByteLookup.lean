module

public import FormalProof4FHE.HasteBoots.ByteLookupPairMiddle
public import FormalProof4FHE.HasteBoots.FrozenLookupSources

@[expose] public section

/-!
# Original-source lookup bound for the actual byte-backed helper phase

Source tuples are decoded only from their original saved checkpoint. The
byte vector is drawn afterwards and the helper phase retains it. Suspended
samples have no completed helper input and contribute no all-pass event.
Native algebra/PCS acceptance and complete FS/Rust refinement remain separate.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.LookupOpeningFamily
open FormalProof4FHE.HasteBoots.StagedRepeatedLookup

namespace FormalProof4FHE.HasteBoots.StagedByteLookup

noncomputable section

variable {F K Cfg Input Digest SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {p sampleDegree d padding c row count repetitions size : ℕ}
  [Module (ZMod p) K]
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions}

/-- Native all-pass arithmetic is evaluated only on a completed helper view,
using its retained typed vector and the two actual recorded states. -/
def AllPass (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    {active inactive : ℕ} (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : ByteLookupPairMiddle.Emission p sampleDegree K Digest HelperMemory repetitions ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  (ByteLookupPairMiddle.completed second.1).elim False (fun helper =>
    StagedRepeatedLookup.AllPass enc dummy basis shape logicalShape table multiplicities LookupPairVectorMiddle.pairs
      domain capacity radius first (helper, second.2))

omit [Module (ZMod p) K] [DecidableEq Input] in
/-- The native pass predicate is the same event on the fixed original source
tuples; no decoding at helper time or after pair sampling enters the bound. -/
theorem allPass_iff (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    {active inactive : ℕ} (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (first : SourceEmission count Digest SourceMemory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (second : ByteLookupPairMiddle.Emission p sampleDegree K Digest HelperMemory repetitions ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    AllPass enc dummy basis shape logicalShape table multiplicities domain capacity radius first second ↔
      ByteLookupPairMiddle.AllPass (FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius first)
        table (fun index => algebraMap F K (multiplicities first.1 index)) second.1 := by
  rfl

variable [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p] [SampleableType Digest]

/-- The original frozen-source all-pass bound is now derived from the actual
byte-backed pair vector, its suspension gate, and the real helper execution. -/
theorem allPass_bound {active inactive : ℕ} {char : ℕ} [CharP K char] (valid : 1 < p)
    (sampleBasis : Module.Basis (Fin sampleDegree) (ZMod p) K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (logicalShape : active + inactive = 2 ^ (c + row))
    (table : Fin size → Fin count → F)
    (multiplicities : SourceEmission count Digest SourceMemory → Fin size → F)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * (d + padding)) (radius : Root count repetitions → ℕ)
    (enough : size + 1 < Fintype.card K) (small : active < char) (hashDepth inner outer : ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (build : SourceEmission count Digest SourceMemory → ByteLookupPairTyped.Raw p sampleDegree K repetitions →
      (Fin repetitions → Pair K) → OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → ByteLookupPairMiddle.Emission p sampleDegree K Digest HelperMemory repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (fun first => ByteLookupPairMiddle.helperRequests
        (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first)) sourceCommit
      (fun first => ByteLookupPairMiddle.program sampleBasis table hashDepth inner outer repetitions (build first)) next initial)}[
        (∃ index, ∀ entry, FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius outcome.1 index ≠ table entry) ∧
        AllPass enc dummy basis shape logicalShape table multiplicities domain capacity radius outcome.1 outcome.2.1] ≤
      TupleLookupPair.error (Fintype.card K) count active size ^ repetitions := by
  have bounded := ByteLookupPairMiddle.staged_bound valid sampleBasis enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
    (fun first => ByteLookupPairMiddle.helperRequests
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first)) sourceCommit table enough hashDepth inner outer build next
    (FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius)
    (fun first index => algebraMap F K (multiplicities first index)) small initial
  refine (prEvent_mono _ _ _ ?_).trans bounded
  intro outcome passed
  exact ⟨passed.1, (allPass_iff enc dummy basis shape logicalShape table multiplicities domain capacity radius outcome.1 outcome.2.1).mp passed.2⟩

end

end FormalProof4FHE.HasteBoots.StagedByteLookup
