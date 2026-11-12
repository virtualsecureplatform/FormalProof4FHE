module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
@[expose] public section

/-! Combine predecessor arithmetic and reached extraction arithmetic under the
same final exception. Concrete native theorems discharge both component rates;
this bookkeeping introduces no hash charge or losslessness assumption. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedExtractionJointBound
open OracleSpec OracleComp
open RetainedPaddedExtraction
noncomputable section
variable {F Before Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {b n : ℕ}

/-- All earlier risks and the actually reached extraction share one extended
final Bad exclusion. A rejected or nonreturning child cannot increase earlier
safe events. No security certificate is hidden in the execution interface. -/
theorem safe_joint_bound
    (base : Before → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory H b n)
    [SampleableType (Fin b → F)] [SampleableType (PackedZeroReduction.Points F n b)]
    [SampleableType (Fin b → Fin b → F)]
    [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((base before memory).code factor).front) b)]
    [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]
    (get : Before → Option (Bool × Memory))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (dummy : Digest) (prior : ProbComp Before) (earlier : Before → Prop)
    (risk : Sigma (Child base) → Prop) (earlierRate extractionRate : ENNReal)
    (earlierBound : Pr{let before ← prior}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (state before)] ≤ earlierRate)
    (extractionBound : Pr{let outcome ← (prior >>= finish base get state dummy)}[
      ∃ result, outcome.2 = some result ∧ risk result ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base state outcome)] ≤ extractionRate) :
    Pr{let outcome ← (prior >>= finish base get state dummy)}[
      (earlier outcome.1 ∨ ∃ result, outcome.2 = some result ∧ risk result) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base state outcome)] ≤
      earlierRate + extractionRate := by
  apply PackedPBSComparisonJointBound.safe_union
  · exact (earlier_safe_event_le base get state dummy prior earlier).trans earlierBound
  · refine le_trans (prEvent_mono _ _ _ ?_) extractionBound
    intro outcome event
    obtain ⟨⟨result,present,risky⟩,clear⟩ := event
    exact ⟨result,present,risky,clear⟩

end
end FormalProof4FHE.HasteBoots.RetainedPaddedExtractionJointBound
