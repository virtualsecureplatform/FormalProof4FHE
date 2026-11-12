module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparisonNativeBound
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
@[expose] public section

/-! Combine predecessor arithmetic and reached comparison arithmetic under the
same final exception. Concrete native theorems discharge both component rates;
this bookkeeping introduces no hash charge or losslessness assumption. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedComparisonJointBound
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open RetainedPaddedComparison
noncomputable section
variable {F Before Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ} {Helper Result : Memory → Type}

/-- All earlier risks and the actually reached comparison share one extended
final Bad exclusion. A rejected or nonreturning child cannot increase earlier
safe events. No security certificate is hidden in the execution interface. -/
theorem safe_joint_bound
    (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (dummy : Digest) (prior : ProbComp Before) (earlier : Before → Prop)
    (risk : Sigma (Child base comparison) → Prop) (earlierRate comparisonRate : ENNReal)
    (earlierBound : Pr{let before ← prior}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (state before)] ≤ earlierRate)
    (comparisonBound : Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      ∃ result, outcome.2 = some result ∧ risk result ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base comparison state outcome)] ≤ comparisonRate) :
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      (earlier outcome.1 ∨ ∃ result, outcome.2 = some result ∧ risk result) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base comparison state outcome)] ≤
      earlierRate + comparisonRate := by
  apply PackedPBSComparisonJointBound.safe_union
  · exact (earlier_safe_event_le base comparison get state dummy prior earlier).trans earlierBound
  · refine le_trans (prEvent_mono _ _ _ ?_) comparisonBound
    intro outcome event
    obtain ⟨⟨result,present,risky⟩,clear⟩ := event
    exact ⟨result,present,risky,clear⟩

end
end FormalProof4FHE.HasteBoots.RetainedPaddedComparisonJointBound
