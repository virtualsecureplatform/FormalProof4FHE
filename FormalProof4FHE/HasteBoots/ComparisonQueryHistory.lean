module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparison
public import FormalProof4FHE.HasteBoots.CheckpointQueryHistory
@[expose] public section

/-! Shared query chronology and frozen-cache receipts through complete native
comparisons and their accepted/rejected predecessor continuations. -/
namespace FormalProof4FHE.HasteBoots.ComparisonQueryHistory
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {F Cfg Input Memory Helper Result : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {d : ℕ}

theorem stage (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (roots : Fin (2*d+2) → Digest) (memory : Memory) (initial : PackedPBSComparisonStage.State s)
    (valid : CachedHashHandler.Coherent initial.hash ∧
      RecordedCheckpointQueries.Sound (fun cfg => Skeleton.perfect (s.heights cfg)) initial)
    (outcome : PackedPBSComparisonStage.Outcome s)
    (supported : outcome ∈ support (PackedPBSComparisonStage.witness enc dummy s roots memory initial)) :
    initial.hash.log <+: outcome.2.2.2.hash.log ∧ CachedHashHandler.Coherent outcome.2.2.2.hash ∧
      RecordedCheckpointQueries.Sound (fun cfg => Skeleton.perfect (s.heights cfg)) outcome.2.2.2 := by
  have actual : (PackedPBSComparisonStage.erase s outcome,outcome.2.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (fun cfg => Skeleton.perfect (s.heights cfg))) (PackedPBSComparisonStage.program s roots memory)).run initial) := by
    rw [←PackedPBSComparisonStage.project_witness enc dummy s roots memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointQueryHistory.run (QueryImpl.ofLift unifSpec ProbComp) enc dummy _
    (PackedPBSComparisonStage.program s roots memory) initial valid
    (PackedPBSComparisonStage.erase s outcome,outcome.2.2.2) actual

section Retained
variable {Before Response CommitMemory : Type} [Field F] {H : Cfg → ℕ} {b n : ℕ}
  {ChildHelper ChildResult : Memory → Type}
variable (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
  (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (ChildHelper memory) (ChildResult memory) d)
  (get : Before → Option (RetainedPaddedComparison.Reconstruction base))
  (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))

/-- All reached comparisons preserve the predecessor's chronology and receipts;
skipped paths preserve them identically. -/
theorem finish (dummy : Digest) (origin : MerkleTreeExtractor.QueryLog Input Digest)
    (before : Before) (outcome : Before × Option (Sigma (RetainedPaddedComparison.Child base comparison)))
    (supported : outcome ∈ support (RetainedPaddedComparison.finish base comparison get state dummy before))
    (valid : origin <+: (state before).hash.log ∧ CachedHashHandler.Coherent (state before).hash ∧
      RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H) (state before)) :
    origin <+: (RetainedPaddedComparison.finalState base comparison state outcome).hash.log ∧
      CachedHashHandler.Coherent (RetainedPaddedComparison.finalState base comparison state outcome).hash ∧
      RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H)
        (RetainedPaddedComparison.finalState base comparison state outcome) := by
  apply DependentStageContinuation.preserves (RetainedPaddedComparison.select base get) state
    (RetainedPaddedComparison.child base comparison dummy) (fun _ result => result.2.2.2)
    (fun current => origin <+: current.hash.log ∧ CachedHashHandler.Coherent current.hash ∧
      RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H) current) _ before outcome supported valid
  intro reconstructed initial result present incoming
  have next := stage (base reconstructed.1).encoding dummy
    (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
    reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory initial incoming.2 result
    (by simpa only [RetainedPaddedComparison.child] using present)
  exact ⟨incoming.1.trans next.1,next.2⟩

/-- The whole predecessor remains opaque at this bind interface. -/
theorem bind (dummy : Digest) (origin : MerkleTreeExtractor.QueryLog Input Digest) (prior : ProbComp Before)
    (incoming : ∀ before ∈ support prior,
      origin <+: (state before).hash.log ∧ CachedHashHandler.Coherent (state before).hash ∧
        RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H) (state before))
    (outcome : Before × Option (Sigma (RetainedPaddedComparison.Child base comparison)))
    (supported : outcome ∈ support (prior >>= RetainedPaddedComparison.finish base comparison get state dummy)) :
    origin <+: (RetainedPaddedComparison.finalState base comparison state outcome).hash.log ∧
      CachedHashHandler.Coherent (RetainedPaddedComparison.finalState base comparison state outcome).hash ∧
      RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H)
        (RetainedPaddedComparison.finalState base comparison state outcome) := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨beforeSupported,laterSupported⟩ := Set.mem_iUnion.mp present
  exact finish base comparison get state dummy origin before outcome laterSupported
    (incoming before beforeSupported)

end Retained
end
end FormalProof4FHE.HasteBoots.ComparisonQueryHistory
