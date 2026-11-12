module
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthStagedSharedLookup
public import FormalProof4FHE.HasteBoots.HeterogeneousSourceCoherence
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthOwnedLookupSources
public import FormalProof4FHE.HasteBoots.StagedPrefixSafeBound
@[expose] public section

/-! Original mixed-width source owners and fresh pre-pair snapshots are
coherent on arbitrary audited incoming histories, outside one final event. -/
namespace FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOwnerConditional
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening PaddedMixedWidthLookupOpeningFamily PaddedMixedWidthStagedSharedLookup
open PaddedMixedWidthOwnedLookupSources (Owners Outcome columns freshColumns)
noncomputable section
variable {F Cfg Input Digest SourceMemory HelperMemory Result : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count repetitions : ℕ}
  {heights : Cfg → ℕ} {tag : Root count repetitions → Cfg} {g : Geometry c row count repetitions}

variable [SampleableType Digest]

omit [Field F] [DecidableEq F] in
theorem fresh_recorded
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
      (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      initial)) (root : Root count repetitions) :
    ⟨tag root,StagedVariableWidthBatchOpening.snapshots heights tag outcome.1 outcome.2.1 root⟩ ∈
      outcome.2.2.2.checkpoints.checkpoints := by
  simp only [StagedCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,second,secondSupported,last,lastSupported,equal⟩ := supported
  subst outcome
  have recorded := StagedVariableWidthBatchOpening.snapshots_recorded enc dummy heights tag
    (List.finRange count) (List.finRange repetitions) (fun i => List.mem_finRange i) (fun i => List.mem_finRange i)
    helperCommit first second secondSupported root
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (tag root) (StagedVariableWidthBatchOpening.snapshots heights tag first second root) (next first.1 second.1)
    (RecordRoots.state _ (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange repetitions) first.1 second.1) second.2)
    recorded last lastSupported

theorem columns_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ F)
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * packedWidth (d+padding) (d+helperPadding) root) (radius : Root count repetitions → ℕ)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory → OracleComp (SharedSequence.Shared Cfg Input Digest)
      (HelperEmission repetitions Digest HelperMemory))
    (next : SourceEmission count Digest SourceMemory → HelperEmission repetitions Digest HelperMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) initial)
    (outcome : Outcome count repetitions Cfg Input Digest SourceMemory HelperMemory Result heights)
    (supported : outcome ∈ support (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
      (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next
      initial))
    (owner : Owners Input Digest heights tag)
    (recorded : ∀ source, (owner source).root = outcome.1.1.1 source ∧
      ⟨tag (.inl source),owner source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints) :
    columns enc dummy domain capacity radius owner =
      freshColumns enc dummy domain capacity radius outcome.1 ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2 := by
  classical
  by_cases bad : CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2
  · exact Or.inr bad
  · have audited := StagedPrefixSafeBound.audited_witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
      (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange repetitions)) sourceCommit helperCommit next initial audited outcome supported
    let fresh : Owners Input Digest heights tag := fun source =>
      StagedVariableWidthBatchOpening.snapshots heights tag outcome.1 outcome.2.1 (.inl source)
    have same : columns enc dummy domain capacity radius owner = columns enc dummy domain capacity radius fresh := by
      funext source
      rcases HeterogeneousSourceCoherence.source_eq_or_bad (front := g.front (.inl source))
        (suffix := g.suffix (.inl source)) (b := d+padding) (m := g.m (.inl source)) enc dummy heights
        (tag (.inl source)) (domain (.inl source)) (capacity (.inl source)) (radius (.inl source)) outcome.2.2.2 audited
        (owner source) (fresh source) (recorded source).2
        (fresh_recorded enc dummy sourceCommit helperCommit next initial outcome supported (.inl source)) (recorded source).1 with equal | failed
      · exact congrArg (fun table => QueryHighZeroPadding.source (g.extra (.inl source))
          (PackedQueryArity.table (g.sourceArity source) table)) equal
      · exact False.elim (bad failed)
    exact Or.inl same

end
end FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOwnerConditional
