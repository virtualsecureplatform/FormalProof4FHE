module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparison
public import FormalProof4FHE.HasteBoots.PaddedPBSRequestComparisonStage
@[expose] public section

/-! Average comparison error only over actually reached accepted reconstruction
returns. The generic averaging helper has an explicit local bound; concrete
request instances discharge it from their executed native verifier. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedComparisonProbability
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
open RetainedPaddedComparison
noncomputable section
variable {F Before Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ} {Helper Result : Memory → Type}

/-- Conditional bounds apply only to computed selected children of supported
predecessors. Skipped/rejected reconstruction branches contribute zero. -/
theorem selected_safe_bound
    (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (dummy : Digest) (prior : ProbComp Before)
    (risk : Sigma (Child base comparison) → Prop) (epsilon : ENNReal)
    (bounded : ∀ before ∈ support prior, ∀ reconstructed,
      select base get before = some reconstructed →
      Pr{let result ← child base comparison dummy reconstructed (state before)}[
        risk ⟨reconstructed,result⟩ ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) result.2.2.2] ≤ epsilon) :
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      ∃ result, outcome.2 = some result ∧ risk result ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base comparison state outcome)] ≤ epsilon := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro before present
  cases selected : select base get before with
  | none =>
    simp only [finish,DependentStageContinuation.program,selected]
    refine (prEvent_eq_zero_of_forall_mem_support _ _ ?_).le.trans zero_le
    intro actual supported event
    have same := eq_of_mem_support_pure (before,none) supported
    have absent : actual.2 = none := congrArg Prod.snd same
    obtain ⟨_,someResult,_⟩ := event
    rw [absent] at someResult
    cases someResult
  | some reconstructed =>
    have conditional := bounded before present reconstructed selected
    simp only [finish,DependentStageContinuation.program,selected,prEvent_norm]
    convert conditional using 1
    apply prEvent_congr
    intro result
    simp only [Option.some.injEq,exists_eq_left',finalState,DependentStageContinuation.finalState]

end
end FormalProof4FHE.HasteBoots.RetainedPaddedComparisonProbability
