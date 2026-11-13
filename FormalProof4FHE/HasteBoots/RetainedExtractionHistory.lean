module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
public import FormalProof4FHE.HasteBoots.RecordedFamilyHistory
public import FormalProof4FHE.HasteBoots.DependentStageSupport
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Recorded original sources survive the actual optional public extraction
and the complete predecessor bind, including rejection and skipped branches. -/
namespace FormalProof4FHE.HasteBoots.RetainedExtractionHistory
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Before Cfg Input Digest Response Memory CommitMemory Term FirstMessage Message : Type}
  [Field F] [DecidableEq F] [Fintype Term] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {b n : ℕ}

variable (base : Before → Memory → PaddedPublicZeroCheck.Scheme F Unit Bool Term FirstMessage Message
  Input Digest Cfg Response Memory CommitMemory H b n)
  (get : Before → Option (Bool × Memory))
  (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))

open RetainedPaddedExtraction

variable [SampleableType Digest] [SampleableType (Fin b → F)]
  [SampleableType (PackedZeroReduction.Points F n b)] [SampleableType (Fin b → Fin b → F)]
  [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^((base before memory).code factor).front) b)]
  [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]


/-- Every predecessor owner survives the actual optional extraction. -/
theorem retains (dummy : Digest) (before : Before)
    (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (finish base get state dummy before))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest H tag)
    (recorded : ⟨tag,saved⟩ ∈ (state before).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ (finalState base state outcome).checkpoints.checkpoints := by
  apply DependentStageContinuation.preserves (select get) state (child base dummy)
    (fun _ result => result.2.2) (fun current => ⟨tag,saved⟩ ∈ current.checkpoints.checkpoints)
    ?_ before outcome supported recorded
  intro selected initial result present incoming
  exact PaddedPublicZeroCheck.retains (base selected.1 selected.2) dummy initial result present tag saved incoming

/-- Retention on the actual complete bind preserves the predecessor family
rather than requiring an independently supplied earlier execution. -/
theorem retains_bind (dummy : Digest) (prior : ProbComp Before)
    (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (prior >>= finish base get state dummy))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest H tag)
    (recorded : ⟨tag,saved⟩ ∈ (state outcome.1).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ (finalState base state outcome).checkpoints.checkpoints := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨_,later⟩ := Set.mem_iUnion.mp present
  have same := DependentStageContinuation.predecessor (select get) state (child base dummy) before outcome later
  exact retains base get state dummy before outcome later tag saved (by simpa only [same] using recorded)

variable {Index : Type} {familyB : ℕ}
/-- Every anchor in the earlier constructed family remains in the final
extraction history. Its decoder and logical values are unchanged. -/
theorem family_retains_bind (dummy : Digest) (prior : ProbComp Before)
    (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (prior >>= finish base get state dummy))
    (world : Before → RecordedPaddedSourceFamily.Family F Cfg Input Digest Index H familyB)
    (recorded : RecordedPaddedSourceFamily.Recorded (world outcome.1) (state outcome.1)) :
    RecordedPaddedSourceFamily.Recorded (world outcome.1) (finalState base state outcome) := by
  intro index
  exact retains_bind base get state dummy prior outcome supported _ _ (recorded index)

/-- The predecessor in the retained return belongs to the actual full prior,
including when the child is skipped or rejects. -/
theorem predecessor_supported_bind (dummy : Digest) (prior : ProbComp Before)
    (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (prior >>= finish base get state dummy)) :
    outcome.1 ∈ support prior :=
  DependentStageSupport.predecessor_supported_bind (RetainedPaddedExtraction.select get) state (RetainedPaddedExtraction.child base dummy) prior outcome supported

/-- Consume the complete predecessor retention proof as one invariant,
without expanding the preceding experiment at this continuation. -/
theorem propagate_retains_bind (dummy : Digest)
    (earlier : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (prior : ProbComp Before)
    (incoming : ∀ before ∈ support prior, CheckpointHistoryChain.Retains (earlier before) (state before))
    (outcome : Before × Option (Sigma (Child base)))
    (supported : outcome ∈ support (prior >>= finish base get state dummy)) :
    CheckpointHistoryChain.Retains (earlier outcome.1) (finalState base state outcome) := by
  apply CheckpointHistoryChain.append_retains (select get) state (child base dummy) (fun _ result => result.2.2) earlier prior incoming ?_ outcome supported
  intro selected initial result present tag saved recorded
  exact PaddedPublicZeroCheck.retains (base selected.1 selected.2) dummy initial result present tag saved recorded

end
end FormalProof4FHE.HasteBoots.RetainedExtractionHistory
