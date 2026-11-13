module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparison
public import FormalProof4FHE.HasteBoots.RecordedFamilyHistory
@[expose] public section

/-! Original source owners and entire constructed families survive the actual
reached-or-skipped final comparison, including in a complete predecessor bind. -/
namespace FormalProof4FHE.HasteBoots.RetainedComparisonHistory
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {F Before Cfg Input Response Memory CommitMemory : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {d b n : ℕ}
  {Helper Result : Memory → Type}

open RetainedPaddedComparison

variable (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
  (comparison : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (Helper memory) (Result memory) d)
  (get : Before → Option (Reconstruction base))
  (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))


/-- Every predecessor checkpoint survives the actual optional comparison. -/
theorem retains (dummy : Digest) (before : Before)
    (outcome : Before × Option (Sigma (Child base comparison)))
    (supported : outcome ∈ support (finish base comparison get state dummy before))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest H tag)
    (recorded : ⟨tag,saved⟩ ∈ (state before).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ (finalState base comparison state outcome).checkpoints.checkpoints := by
  apply DependentStageContinuation.preserves (select base get) state (child base comparison dummy)
    (fun _ result => result.2.2.2) (fun current => ⟨tag,saved⟩ ∈ current.checkpoints.checkpoints)
    ?_ before outcome supported recorded
  intro reconstructed initial result present incoming
  exact PackedPBSComparisonStage.retains (base reconstructed.1).encoding dummy
    (PaddedReconstructionComparison.stage (base reconstructed.1) (comparison reconstructed.1))
    reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory initial tag saved incoming result present

/-- The complete predecessor remains opaque while its checkpoint is retained
through the comparison selected by that actual predecessor. -/
theorem retains_bind (dummy : Digest) (prior : ProbComp Before)
    (outcome : Before × Option (Sigma (Child base comparison)))
    (supported : outcome ∈ support (prior >>= finish base comparison get state dummy))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest H tag)
    (recorded : ⟨tag,saved⟩ ∈ (state outcome.1).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ (finalState base comparison state outcome).checkpoints.checkpoints := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨_,later⟩ := Set.mem_iUnion.mp present
  have same := DependentStageContinuation.predecessor (select base get) state (child base comparison dummy)
    before outcome later
  exact retains base comparison get state dummy before outcome later tag saved (by simpa only [same] using recorded)

variable {Index : Type} {familyB : ℕ}
/-- A family constructed from an earlier supported prefix remains recorded
through comparison, without reselecting or decoding its anchors. -/
theorem family_retains_bind (dummy : Digest) (prior : ProbComp Before)
    (outcome : Before × Option (Sigma (Child base comparison)))
    (supported : outcome ∈ support (prior >>= finish base comparison get state dummy))
    (world : Before → RecordedPaddedSourceFamily.Family F Cfg Input Digest Index H familyB)
    (recorded : RecordedPaddedSourceFamily.Recorded (world outcome.1) (state outcome.1)) :
    RecordedPaddedSourceFamily.Recorded (world outcome.1) (finalState base comparison state outcome) := by
  intro index
  exact retains_bind base comparison get state dummy prior outcome supported _ _ (recorded index)

end
end FormalProof4FHE.HasteBoots.RetainedComparisonHistory
