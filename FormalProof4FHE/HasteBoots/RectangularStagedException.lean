module
public import FormalProof4FHE.HasteBoots.RectangularStagedOpening
public import FormalProof4FHE.HasteBoots.StagedCommitmentException
@[expose] public section

/-! Staged heterogeneous grouped PCS, including the terminal common history
exception. Original source/helper checkpoints retain their actual prefix logs;
each root pays once for its complete batch and the whole run pays one hash charge. -/
namespace FormalProof4FHE.HasteBoots.RectangularStagedException
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening RectangularVariableWidthOpening RectangularStagedOpening
noncomputable section
variable {F Source Helper Input Digest Cfg Response Memory SourceMemory HelperMemory QueryData : Type}
  {width symbolWidth : (Source ⊕ Helper) → ℕ} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [Field F] [DecidableEq F]
  {heights : Cfg → ℕ} {tag : (Source ⊕ Helper) → Cfg} {layout : (Source ⊕ Helper) → Layout}
  [∀ factor, SampleableType (TestMatrix F (2 ^ (layout factor).front) (width factor))]
  [∀ factor, SampleableType (Fin (layout factor).queries → Fin (2 ^ heights (tag factor)))]
  [Fintype Digest] [Fintype F]
  [∀ factor, SampleableType ((Fin (2 ^ (layout factor).front) × Fin (width factor)) → F)]

/-- Sources freeze before the adaptive middle phase, helpers afterwards. The
native arithmetic bounds and global authentication charge are derived for that
actual two-prefix execution, without a source-stability equality assumption. -/
theorem soundness_from_empty [∀ factor, NeZero (symbolWidth factor)] [∀ factor, NeZero (layout factor).m]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sources : List Source) (helpers : List Helper)
    (sourceComplete : ∀ source, source ∈ sources) (helperComplete : ∀ helper, helper ∈ helpers)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (enough : ∀ factor, (layout factor).m ≤ Fintype.card (Fin (2 ^ heights (tag factor))))
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * symbolWidth factor) (radius : (Source ⊕ Helper) → ℕ)
    (build : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      QueryData → (factor : Source ⊕ Helper) → Protocol F Input Digest Cfg Response Memory width symbolWidth heights tag layout factor)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (SourceEmission Source Digest SourceMemory))
    (helperCommit : SourceEmission Source Digest SourceMemory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (HelperEmission Helper Digest HelperMemory))
    (selectQuery : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Bool)
    (start : (((Source ⊕ Helper) → Digest) × CommitMemory Source Helper Digest SourceMemory HelperMemory) → QueryData → Memory)
    (large : ∀ factor, radius factor < Fintype.card F)
    (small : ∀ factor, 3*radius factor < Code.minDist (BlockCode.code (domain factor) (layout factor).m (symbolWidth factor) :
      Set (Fin (2^heights (tag factor)) → Fin (symbolWidth factor) → F))) :
    let next := continuation enc domain build selectQuery enabled start sources helpers
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (sourceRequests tag sources) (helperRequests tag helpers) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        RectangularRecordedOpening.Wrong enc dummy domain capacity radius build (emission outcome.1.1 outcome.2.1.1)
          (snapshots heights tag outcome.1 outcome.2.1) outcome.2.2 ∨
        CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      ((factors sources helpers).map (fun factor => error (domain factor) (layout factor).m (symbolWidth factor) (width factor) (layout factor).queries (radius factor))).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program (sourceRequests tag sources) (helperRequests tag helpers) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  apply StagedCommitmentException.event_bound_or_bad enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (sourceRequests tag sources) (helperRequests tag helpers) sourceCommit helperCommit
    (continuation enc domain build selectQuery enabled start sources helpers)
    (fun first second last => RectangularRecordedOpening.Wrong enc dummy domain capacity radius build
      (emission first.1 second.1) (snapshots heights tag first second) last)
    (fun first second last => SharedSequence.AnyBad
      (fun _ => RectangularRecordedOpening.Arithmetic enc dummy domain capacity radius build
        (emission first.1 second.1) (snapshots heights tag first second) last.1.1) last.1.2.results) _
  · intro first second
    exact RectangularRecordedOpening.arithmetic_bound enc dummy (factors sources helpers) domain enough capacity radius
      build selectQuery enabled start (emission first.1 second.1) (snapshots heights tag first second) _ large small
  · intro first _ second secondSupported last lastSupported wrong
    exact RectangularRecordedOpening.reduce_wrong enc dummy (factors sources helpers)
      (factors_complete sources helpers sourceComplete helperComplete) domain capacity radius build selectQuery enabled start
      (emission first.1 second.1) (snapshots heights tag first second) (snapshots_roots heights tag first second) _
      (snapshots_recorded enc dummy heights tag sources helpers sourceComplete helperComplete helperCommit first second secondSupported)
      last lastSupported wrong

end
end FormalProof4FHE.HasteBoots.RectangularStagedException
