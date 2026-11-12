module
public import FormalProof4FHE.HasteBoots.OwnedNTTSoundness
@[expose] public section

/-! Original polynomial-row failures feed the concrete authenticated NTT's
recorded-source risk event. Row projections share the same two original
sources; neither a fresh source interpretation nor an NTT truth certificate
is introduced. Rust transcript/codec correspondence remains separate. -/
namespace FormalProof4FHE.HasteBoots.OwnedNTTBindingCoverage
open NativeBlindRotation (Poly)
noncomputable section
variable {q log b c r k front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Digest]

/-- Replacing the factory transform preserves both original owner sources. -/
theorem original_sources_scheme
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (owner : ∀ side, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag side)) :
    OwnedNTTSoundness.originalSources (PackedNTT.scheme length psi primitive s) dummy capacity radius owner =
      OwnedNTTSoundness.originalSources s dummy capacity radius owner := rfl

/-- A wrong transform at one original row contradicts the complete original
row relation. All row/side addresses and both retained owners are unchanged. -/
theorem accepted_wrong_transform_implies_original
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := ZMod q) (Memory := Memory) (Response := Response)
        (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
        (k := k) (front := front) (queries := queries) (height := height))
    (owner : ∀ side, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag side))
    (recorded : ∀ side, (owner side).root = outcome.1.1.1 side ∧
      ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (row : MatrixFold.Cube r)
    (wrong : BlindRotationNTT.transform log psi
      (PackedNTTBinding.row length (OwnedNTTSoundness.originalSources s dummy capacity radius owner false) row) ≠
      PackedNTTBinding.row length (OwnedNTTSoundness.originalSources s dummy capacity radius owner true) row)
    (passes : AuthenticatedNTT.accepted outcome.2.1 = true) :
    OwnedNTTSoundness.OriginalRisk (PackedNTT.scheme length psi primitive s) dummy capacity radius outcome := by
  refine ⟨owner,recorded,?_,passes⟩
  intro holds
  have relation : PackedNTT.Relation length psi
      (NTTCompression.sourceRows c r (OwnedNTTSoundness.originalSources s dummy capacity radius owner false))
      (NTTCompression.sourceRows c r (OwnedNTTSoundness.originalSources s dummy capacity radius owner true)) := holds
  exact wrong (PackedNTTBinding.transform_of_relation length psi primitive _ _ relation row)

/-- An arbitrary family of application polynomials is either mismatched to
the original source rows, or its wrong transform reaches ONE original risk.
There is no union over the number of row projections. -/
theorem accepted_wrong_family_coverage {I : Type}
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := ZMod q) (Memory := Memory) (Response := Response)
        (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
        (k := k) (front := front) (queries := queries) (height := height))
    (owner : ∀ side, RecordedSourceCoherence.Snapshot Input Digest Cfg height (s.tag side))
    (recorded : ∀ side, (owner side).root = outcome.1.1.1 side ∧
      ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (rows : I → MatrixFold.Cube r) (coefficients evaluations : I → Poly q (2^log))
    (wrong : ∃ index, BlindRotationNTT.transform log psi (coefficients index) ≠ evaluations index)
    (passes : AuthenticatedNTT.accepted outcome.2.1 = true) :
    (∃ index, PackedNTTBinding.row length
      (OwnedNTTSoundness.originalSources s dummy capacity radius owner false) (rows index) ≠ coefficients index) ∨
    (∃ index, PackedNTTBinding.row length
      (OwnedNTTSoundness.originalSources s dummy capacity radius owner true) (rows index) ≠ evaluations index) ∨
    OwnedNTTSoundness.OriginalRisk (PackedNTT.scheme length psi primitive s) dummy capacity radius outcome := by
  classical
  obtain ⟨index, bad⟩ := wrong
  by_cases source : PackedNTTBinding.row length
      (OwnedNTTSoundness.originalSources s dummy capacity radius owner false) (rows index) = coefficients index
  · by_cases target : PackedNTTBinding.row length
        (OwnedNTTSoundness.originalSources s dummy capacity radius owner true) (rows index) = evaluations index
    · apply Or.inr ∘ Or.inr
      apply accepted_wrong_transform_implies_original length psi primitive s dummy capacity radius outcome
        owner recorded (rows index) _ passes
      simpa only [source,target] using bad
    · exact Or.inr (Or.inl ⟨index,target⟩)
  · exact Or.inl ⟨index,source⟩


open OracleSpec OracleComp
variable [DecidableEq Input] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]

/-- A supported execution supplies its own original checkpoints. No separate
owner-recording certificate is needed for the fresh-source case. -/
theorem fresh_wrong_transform_implies_original
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
    (s : AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b c r k front suffix m queries height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (outcome : AuthenticatedNTT.Prefix (Digest := Digest) (CommitMemory := CommitMemory) (Input := Input)
        (Cfg := Cfg) (height := height) ×
      AuthenticatedNTT.RunResult (F := ZMod q) (Memory := Memory) (Response := Response)
        (Input := Input) (Digest := Digest) (Cfg := Cfg) (b := b) (c := c) (r := r)
        (k := k) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AuthenticatedNTT.witness (PackedNTT.scheme length psi primitive s) dummy))
    (row : MatrixFold.Cube r)
    (wrong : BlindRotationNTT.transform log psi
      (PackedNTTBinding.row length (AuthenticatedNTT.sources s dummy capacity radius outcome.1 false) row) ≠
      PackedNTTBinding.row length (AuthenticatedNTT.sources s dummy capacity radius outcome.1 true) row)
    (passes : AuthenticatedNTT.accepted outcome.2.1 = true) :
    OwnedNTTSoundness.OriginalRisk (PackedNTT.scheme length psi primitive s) dummy capacity radius outcome := by
  apply accepted_wrong_transform_implies_original length psi primitive s dummy capacity radius outcome
    (CommittedJointMatrixOpening.snapshots s.tag outcome.1) (fun side => ⟨rfl, ?_⟩) row wrong passes
  exact OwnedNTTSoundness.fresh_recorded (PackedNTT.scheme length psi primitive s) dummy outcome supported side

end
end FormalProof4FHE.HasteBoots.OwnedNTTBindingCoverage
