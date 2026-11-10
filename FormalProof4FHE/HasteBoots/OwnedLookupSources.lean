module
public import FormalProof4FHE.HasteBoots.FrozenLookupSources
public import FormalProof4FHE.HasteBoots.StagedCommitmentException
public import FormalProof4FHE.HasteBoots.HeterogeneousSourceCoherence
@[expose] public section

/-! Lookup tuples from any matching recorded original source family. The
actual fresh source prefix precedes every pair/helper call; coherence is over
full decoded columns with fixed per-root parameters, not selected queries. -/
namespace FormalProof4FHE.HasteBoots.OwnedLookupSources
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening LookupOpeningFamily StagedRepeatedLookup
noncomputable section
variable {F Cfg Input Digest SourceMemory HelperMemory Result : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding c row count repetitions active inactive : ℕ}
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions}

abbrev Owners (Input Digest : Type) (heights : Cfg → ℕ) (tag : Root count repetitions → Cfg) :=
  ∀ source : Fin count, HeterogeneousSourceCoherence.Snapshot Input Digest Cfg heights (tag (.inl source))

abbrev FirstPrefix (count : ℕ) (Cfg Input Digest SourceMemory : Type) (heights : Cfg → ℕ) :=
  SourceEmission count Digest SourceMemory ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))
abbrev SecondPrefix (repetitions : ℕ) (Cfg Input Digest HelperMemory : Type) (heights : Cfg → ℕ) :=
  HelperEmission repetitions Digest HelperMemory ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))
abbrev Outcome (count repetitions : ℕ) (Cfg Input Digest SourceMemory HelperMemory Result : Type) (heights : Cfg → ℕ) :=
  FirstPrefix count Cfg Input Digest SourceMemory heights × SecondPrefix repetitions Cfg Input Digest HelperMemory heights ×
    (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))

def columns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root*(d+padding)) (radius : Root count repetitions → ℕ)
    (owner : Owners Input Digest heights tag) : Fin count → MatrixFold.Cube row → Fin (d+padding) → F :=
  fun source => PackedQueryArity.table (g.sourceArity source).symm
    (SubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source))
      (word enc dummy heights (tag (.inl source)) (owner source)))

def tuples (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : d+padding = 2^c) (logicalShape : active+inactive = 2^(c+row))
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root*(d+padding)) (radius : Root count repetitions → ℕ)
    (owner : Owners Input Digest heights tag) : Fin active → Fin count → F :=
  LookupPairArithmetic.activeTuples logicalShape (fun source => LookupSourceFlattening.flatten shape
    (columns enc dummy domain capacity radius owner source))

/-- A false tuple from any matching original source family. Acceptance is
kept separate and will be the actual verifier result in the probability bound. -/
def OriginalFalse {size : ℕ} (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : d+padding = 2^c) (logicalShape : active+inactive = 2^(c+row))
    (table : Fin size → Fin count → F) (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root*(d+padding)) (radius : Root count repetitions → ℕ)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights) : Prop :=
  ∃ owner : Owners Input Digest heights tag,
    (∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints) ∧
    ∃ position, ∀ index, tuples enc dummy shape logicalShape domain capacity radius owner position ≠ table index

variable [SampleableType Digest]

omit [Field F] [DecidableEq F] in
theorem fresh_recorded
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))) (root : Root count repetitions) :
    ⟨tag root,StagedHeterogeneousBatchOpening.snapshots heights tag outcome.1 outcome.2.1 root⟩ ∈
      outcome.2.2.2.checkpoints.checkpoints := by
  simp only [StagedCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,second,secondSupported,last,lastSupported,equal⟩ := supported
  subst outcome
  have recorded := StagedHeterogeneousBatchOpening.snapshots_recorded enc dummy heights tag
    (List.finRange count) (List.finRange repetitions) (fun i => List.mem_finRange i) (fun i => List.mem_finRange i)
    helperCommit first second secondSupported root
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (tag root) (StagedHeterogeneousBatchOpening.snapshots heights tag first second root) (next first.1 second.1)
    (RecordRoots.state _ (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions) first.1 second.1) second.2)
    recorded last lastSupported

/-- Complete original columns agree with the actual pre-pair source columns
outside one shared history exception, even for a post-run owner-family choice. -/
theorem tuples_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : d+padding = 2^c) (logicalShape : active+inactive = 2^(c+row))
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root*(d+padding)) (radius : Root count repetitions → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))))
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints) :
    tuples enc dummy shape logicalShape domain capacity radius owner =
      FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius outcome.1 ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2 := by
  classical
  by_cases bad : CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2
  · exact Or.inr bad
  · have audited := StagedCommitmentException.audited_witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next outcome supported
    let fresh : Owners Input Digest heights tag := fun source =>
      StagedHeterogeneousBatchOpening.snapshots heights tag outcome.1 outcome.2.1 (.inl source)
    have same : columns enc dummy domain capacity radius owner = columns enc dummy domain capacity radius fresh := by
      funext source
      rcases HeterogeneousSourceCoherence.source_eq_or_bad (front := g.front (.inl source))
        (suffix := g.suffix (.inl source)) (b := d+padding) (m := g.m (.inl source)) enc dummy heights
        (tag (.inl source)) (domain (.inl source)) (capacity (.inl source)) (radius (.inl source)) outcome.2.2.2 audited
        (owner source) (fresh source) (recorded source).2
        (fresh_recorded enc dummy sourceCommit helperCommit next outcome supported (.inl source)) (recorded source).1 with equal | failed
      · exact congrArg (PackedQueryArity.table (g.sourceArity source).symm) equal
      · exact False.elim (bad failed)
    have equal := congrArg (fun values : Fin count → MatrixFold.Cube row → Fin (d+padding) → F =>
      LookupPairArithmetic.activeTuples logicalShape (fun source => LookupSourceFlattening.flatten shape (values source))) same
    exact Or.inl equal
variable {size : ℕ}

theorem fresh_false_implies_original
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : d+padding = 2^c) (logicalShape : active+inactive = 2^(c+row))
    (table : Fin size → Fin count → F) (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root*(d+padding)) (radius : Root count repetitions → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))))
    (bad : ∃ position, ∀ index,
      FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius outcome.1 position ≠ table index) :
    OriginalFalse enc dummy shape logicalShape table domain capacity radius outcome := by
  refine ⟨(fun source => StagedHeterogeneousBatchOpening.snapshots heights tag outcome.1 outcome.2.1 (.inl source)),?_,?_⟩
  · intro source
    exact ⟨rfl,fresh_recorded enc dummy sourceCommit helperCommit next outcome supported (.inl source)⟩
  · exact bad

theorem original_false_reduction
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : d+padding = 2^c) (logicalShape : active+inactive = 2^(c+row))
    (table : Fin size → Fin count → F) (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root*(d+padding)) (radius : Root count repetitions → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedHeterogeneousBatchOpening.sourceRequests tag (List.finRange count))
      (StagedHeterogeneousBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))))
    (bad : OriginalFalse enc dummy shape logicalShape table domain capacity radius outcome) :
    (∃ position, ∀ index, FrozenLookupSources.tuples enc dummy shape logicalShape domain capacity radius outcome.1 position ≠ table index) ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2 := by
  obtain ⟨owner,recorded,position,outside⟩ := bad
  rcases tuples_eq_or_bad enc dummy shape logicalShape domain capacity radius sourceCommit helperCommit next outcome supported owner recorded with same | failed
  · refine Or.inl ⟨position,?_⟩
    intro index equal
    exact outside index ((congrFun same position).trans equal)
  · exact Or.inr failed


end
end FormalProof4FHE.HasteBoots.OwnedLookupSources
