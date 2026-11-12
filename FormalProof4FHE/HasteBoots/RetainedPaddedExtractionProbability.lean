module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
@[expose] public section

/-! Average extraction error only over actually reached accepted comparison
returns. The generic averaging helper has an explicit local bound; concrete
extraction instances discharge it from their executed native verifier. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProbability
open OracleSpec OracleComp BinaryTree
open RetainedPaddedExtraction
noncomputable section
variable {F Before Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {b n : ℕ}

/-- Conditional bounds apply only to computed selected children of supported
predecessors. Skipped/rejected comparison branches contribute zero. -/
theorem selected_safe_bound
    (base : Before → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
      Input Digest Cfg Response Memory CommitMemory H b n)
    [SampleableType (Fin b → F)] [SampleableType (PackedZeroReduction.Points F n b)]
    [SampleableType (Fin b → Fin b → F)]
    [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((base before memory).code factor).front) b)]
    [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]
    (get : Before → Option (Bool × Memory))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (dummy : Digest) (prior : ProbComp Before)
    (risk : Sigma (Child base) → Prop) (epsilon : ENNReal)
    (bounded : ∀ before ∈ support prior, ∀ selectedChild,
      select get before = some selectedChild →
      Pr{let result ← child base dummy selectedChild (state before)}[
        risk ⟨selectedChild,result⟩ ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) result.2.2] ≤ epsilon) :
    Pr{let outcome ← (prior >>= finish base get state dummy)}[
      ∃ result, outcome.2 = some result ∧ risk result ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base state outcome)] ≤ epsilon := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro before present
  cases selected : select get before with
  | none =>
    simp only [finish,DependentStageContinuation.program,selected]
    refine (prEvent_eq_zero_of_forall_mem_support _ _ ?_).le.trans zero_le
    intro actual supported event
    have same := eq_of_mem_support_pure (before,none) supported
    have absent : actual.2 = none := congrArg Prod.snd same
    obtain ⟨_,someResult,_⟩ := event
    rw [absent] at someResult
    cases someResult
  | some selectedChild =>
    have conditional := bounded before present selectedChild selected
    simp only [finish,DependentStageContinuation.program,selected,prEvent_norm]
    convert conditional using 1
    apply prEvent_congr
    intro result
    simp only [Option.some.injEq,exists_eq_left',finalState,DependentStageContinuation.finalState]

end
end FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProbability
