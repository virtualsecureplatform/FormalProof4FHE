module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparison
@[expose] public section

/-! Extract literal supported calls and computed gates from a returned retained
comparison. These facts concern the same execution, without security premises. -/
namespace FormalProof4FHE.HasteBoots.RetainedComparisonReached
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open RetainedPaddedComparison
noncomputable section
variable {F Before Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ} {Helper Result : Memory → Type}
variable (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))

/-- A complete supported bind yielding a comparison supplies its supported
predecessor, actual selected reconstruction, computed gate and child support. -/
theorem reached_bind (dummy : Digest) (prior : ProbComp Before) (before : Before)
    (result : Sigma (Child base comparison))
    (supported : (before,some result) ∈ support (prior >>= finish base comparison get state dummy)) :
    before ∈ support prior ∧ get before = some result.1 ∧
      PaddedLinear.accepted (base result.1.1) result.1.2.2.1 = true ∧
      result.2 ∈ support (child base comparison dummy result.1 (state before)) := by
  rw [support_bind] at supported
  obtain ⟨selected,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨selectedSupported,remainder⟩ := Set.mem_iUnion.mp present
  have same := DependentStageContinuation.predecessor (select base get) state (child base comparison dummy)
    selected (before,some result) remainder
  subst selected
  exact ⟨selectedSupported,RetainedPaddedComparison.reached base comparison get state dummy before result remainder⟩

/-- A literal comparison started at its reconstruction's returned state is the
same reached optional comparison continuation used by the semantic theorems. -/
theorem continuation_supported (dummy : Digest) (reconstructed : Reconstruction base)
    (outcome : Child base comparison reconstructed)
    (accepted : PaddedLinear.accepted (base reconstructed.1) reconstructed.2.2.1 = true)
    (supported : outcome ∈ support (child base comparison dummy reconstructed reconstructed.2.2.2)) :
    some outcome ∈ support (PaddedReconstructionComparison.continuation (base reconstructed.1)
      (comparison reconstructed.1) dummy reconstructed.2) := by
  simp only [PaddedReconstructionComparison.continuation,accepted,ite_true]
  rw [support_map]
  exact Set.mem_image_of_mem _ supported

/-- When the selected predecessor's final state is the actual incoming state,
the complete bind yields the same literal optional comparison continuation. -/
theorem completed_bind
    (follows : ∀ before reconstructed, get before = some reconstructed → state before = reconstructed.2.2.2)
    (dummy : Digest) (prior : ProbComp Before) (before : Before) (result : Sigma (Child base comparison))
    (supported : (before,some result) ∈ support (prior >>= finish base comparison get state dummy)) :
    before ∈ support prior ∧ get before = some result.1 ∧
      PaddedLinear.accepted (base result.1.1) result.1.2.2.1 = true ∧
      some result.2 ∈ support (PaddedReconstructionComparison.continuation (base result.1.1)
        (comparison result.1.1) dummy result.1.2) := by
  have actual := reached_bind base comparison get state dummy prior before result supported
  refine ⟨actual.1,actual.2.1,actual.2.2.1,?_⟩
  apply continuation_supported base comparison dummy result.1 result.2 actual.2.2.1
  simpa only [follows before result.1 actual.2.1] using actual.2.2.2

/-- Facts proved about the actual supported reconstruction lift through its
returned comparison without re-expanding the predecessor experiment. -/
theorem predecessor_facts {Previous : Type}
    (pairState : Previous × Option (Reconstruction base) →
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (follows : ∀ before reconstructed, before.2 = some reconstructed → pairState before = reconstructed.2.2.2)
    (dummy : Digest) (prior : ProbComp (Previous × Option (Reconstruction base)))
    {Facts : Previous → Reconstruction base → Prop}
    (actualFacts : ∀ previous reconstructed, (previous,some reconstructed) ∈ support prior → Facts previous reconstructed)
    (before : Previous × Option (Reconstruction base)) (result : Sigma (Child base comparison))
    (supported : (before,some result) ∈ support (prior >>= finish base comparison Prod.snd pairState dummy)) :
    Facts before.1 result.1 ∧ before ∈ support prior ∧ before.2 = some result.1 ∧
      PaddedLinear.accepted (base result.1.1) result.1.2.2.1 = true ∧
      some result.2 ∈ support (PaddedReconstructionComparison.continuation (base result.1.1)
        (comparison result.1.1) dummy result.1.2) := by
  have actual := completed_bind base comparison Prod.snd pairState follows dummy prior before result supported
  have same : before = (before.1,some result.1) := Prod.ext rfl actual.2.1
  have reconstructionSupported : (before.1,some result.1) ∈ support prior := same ▸ actual.1
  exact ⟨actualFacts before.1 result.1 reconstructionSupported,actual⟩

end
end FormalProof4FHE.HasteBoots.RetainedComparisonReached
