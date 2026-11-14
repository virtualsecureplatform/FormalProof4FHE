module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
@[expose] public section

/-! Reassemble the literal reached extraction in its actual predecessor
experiment, without replaying it or assuming a child-security bound. -/
namespace FormalProof4FHE.HasteBoots.RetainedExtractionAssembly
open OracleSpec OracleComp
noncomputable section
variable {F Before Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {b n : ℕ}
variable (base : Before → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
    Input Digest Cfg Response Memory CommitMemory H b n)
  (get : Before → Option (Bool × Memory))
  (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
variable [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((base before memory).code factor).front) b)]
  [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]

/-- The computed gate and literal supported child reconstruct its finish support. -/
theorem finish_supported (dummy : Digest) (before : Before) (memory : Memory)
    (result : RetainedPaddedExtraction.Child base (before,memory))
    (found : get before = some (true,memory))
    (supported : result ∈ support (PaddedPublicZeroCheck.witness (base before memory) dummy (state before))) :
    (before,some ⟨(before,memory),result⟩) ∈ support
      (RetainedPaddedExtraction.finish base get state dummy before) := by
  simp only [RetainedPaddedExtraction.finish,DependentStageContinuation.program,
    RetainedPaddedExtraction.select,found,Option.bind_some,↓reduceIte]
  rw [support_bind]
  refine Set.mem_iUnion.mpr ⟨result,Set.mem_iUnion.mpr ⟨supported,?_⟩⟩
  simp only [support_pure,Set.mem_singleton_iff]

/-- The same supported predecessor and child reconstruct the complete bind. -/
theorem bind_supported (dummy : Digest) (prior : ProbComp Before) (before : Before) (memory : Memory)
    (result : RetainedPaddedExtraction.Child base (before,memory))
    (priorSupported : before ∈ support prior)
    (found : get before = some (true,memory))
    (supported : result ∈ support (PaddedPublicZeroCheck.witness (base before memory) dummy (state before))) :
    (before,some ⟨(before,memory),result⟩) ∈ support
      (prior >>= RetainedPaddedExtraction.finish base get state dummy) := by
  rw [support_bind]
  exact Set.mem_iUnion.mpr ⟨before,Set.mem_iUnion.mpr ⟨priorSupported,
    finish_supported base get state dummy before memory result found supported⟩⟩

end
end FormalProof4FHE.HasteBoots.RetainedExtractionAssembly
