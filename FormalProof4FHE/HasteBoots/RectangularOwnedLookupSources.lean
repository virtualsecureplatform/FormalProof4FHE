module
public import FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
public import FormalProof4FHE.HasteBoots.HeterogeneousSourceCoherence
@[expose] public section

/-! Complete source columns from any matching recorded original owner family
agree with the actual pre-pair source columns outside the existing history Bad.
Physical helper widths remain independent. Matching preserves the context and
all source interpretation parameters; digest equality alone is insufficient. -/
namespace FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening PaddedMixedWidthLookupOpeningFamily RectangularStagedSharedLookup
noncomputable section
variable {F Cfg Input Digest SourceMemory HelperMemory Result : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count repetitions : ℕ}
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions} {symbolWidth : Root count repetitions → ℕ}

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
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (owner : Owners Input Digest heights tag) : Fin count → MatrixFold.Cube row → Fin (d+padding) → F :=
  fun source => QueryHighZeroPadding.source (g.extra (.inl source)) <|
    PackedQueryArity.table (g.sourceArity source)
    (RectangularSubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source))
      (AmbientRectangularSource.word enc dummy heights (tag (.inl source)) (owner source)))

/-- Actual source columns frozen before any pair/helper work. -/
def freshColumns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (radius : Root count repetitions → ℕ)
    (first : FirstPrefix count Cfg Input Digest SourceMemory heights) :
    Fin count → MatrixFold.Cube row → Fin (d+padding) → F :=
  fun source => QueryHighZeroPadding.source (g.extra (.inl source)) <|
    PackedQueryArity.table (g.sourceArity source)
    (RectangularSubclaimSourceLayout.decodedSource (domain (.inl source)) (capacity (.inl source)) (radius (.inl source))
      (AmbientRectangularSource.word enc dummy heights (tag (.inl source)) ⟨first.1.1 source,first.2.hash.log⟩))

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
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))) (root : Root count repetitions) :
    ⟨tag root,RectangularStagedOpening.snapshots heights tag outcome.1 outcome.2.1 root⟩ ∈
      outcome.2.2.2.checkpoints.checkpoints := by
  simp only [StagedCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,second,secondSupported,last,lastSupported,equal⟩ := supported
  subst outcome
  have recorded := RectangularStagedOpening.snapshots_recorded enc dummy heights tag
    (List.finRange count) (List.finRange repetitions) (fun i => List.mem_finRange i) (fun i => List.mem_finRange i)
    helperCommit first second secondSupported root
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (tag root) (RectangularStagedOpening.snapshots heights tag first second root) (next first.1 second.1)
    (RecordRoots.state _ (RectangularStagedOpening.helperRequests tag (List.finRange repetitions) first.1 second.1) second.2)
    recorded last lastSupported

theorem columns_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count repetitions → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))))
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints) :
    columns (d := d) (padding := padding) enc dummy domain capacity radius owner =
      freshColumns (d := d) (padding := padding) enc dummy domain capacity radius outcome.1 ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2 := by
  classical
  by_cases bad : CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2
  · exact Or.inr bad
  · have audited := StagedCommitmentException.audited_witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next outcome supported
    let fresh : Owners Input Digest heights tag := fun source =>
      RectangularStagedOpening.snapshots heights tag outcome.1 outcome.2.1 (.inl source)
    have same : columns (d := d) (padding := padding) enc dummy domain capacity radius owner = columns (d := d) (padding := padding) enc dummy domain capacity radius fresh := by
      funext source
      rcases AmbientRectangularSource.source_eq_or_bad (front := g.front (.inl source))
        (suffix := g.suffix (.inl source)) (packingWidth := d+padding) (degree := g.m (.inl source))
        (codeWidth := symbolWidth (.inl source)) enc dummy heights
        (tag (.inl source)) rfl (domain (.inl source)) (capacity (.inl source)) (radius (.inl source)) outcome.2.2.2 audited
        (owner source) (fresh source) (recorded source).2
        (fresh_recorded enc dummy sourceCommit helperCommit next outcome supported (.inl source)) (recorded source).1 with equal | failed
      · exact congrArg (fun table => QueryHighZeroPadding.source (g.extra (.inl source))
          (PackedQueryArity.table (g.sourceArity source) table)) equal
      · exact False.elim (bad failed)
    exact Or.inl same

end
end FormalProof4FHE.HasteBoots.RectangularOwnedLookupSources
