module
public import FormalProof4FHE.HasteBoots.DependentStageSupport
public import FormalProof4FHE.HasteBoots.RecordedFamilyHistory
@[expose] public section

/-! Compose checkpoint retention while keeping complete predecessor experiments
opaque. Only the reached child and its actual incoming state are inspected. -/
namespace FormalProof4FHE.HasteBoots.CheckpointHistoryChain
noncomputable section
variable {Cfg Input Digest Before Memory : Type} {H : Cfg → ℕ} {Result : Memory → Type}

abbrev State (Input Digest : Type) (H : Cfg → ℕ) :=
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)

def Retains (before after : State Input Digest H) : Prop :=
  ∀ tag (saved : AmbientMatrixSource.Snapshot Input Digest H tag),
    ⟨tag,saved⟩ ∈ before.checkpoints.checkpoints → ⟨tag,saved⟩ ∈ after.checkpoints.checkpoints

theorem trans {first second last : State Input Digest H}
    (earlier : Retains first second) (later : Retains second last) : Retains first last := by
  intro tag saved recorded
  exact later tag saved (earlier tag saved recorded)

/-- A predecessor retention invariant and actual child retention compose over
the complete bind, including all skipped and rejected paths. -/
theorem append_retains
    (select : Before → Option Memory) (start : Before → State Input Digest H)
    (child : (memory : Memory) → State Input Digest H → ProbComp (Result memory))
    (finish : (memory : Memory) → Result memory → State Input Digest H)
    (earlier : Before → State Input Digest H) (prior : ProbComp Before)
    (incoming : ∀ before ∈ support prior, Retains (earlier before) (start before))
    (localFact : ∀ memory initial result, result ∈ support (child memory initial) → Retains initial (finish memory result))
    (outcome : Before × Option (Sigma Result))
    (supported : outcome ∈ support (prior >>= DependentStageContinuation.program select start child)) :
    Retains (earlier outcome.1) (DependentStageContinuation.finalState start finish outcome) := by
  rw [support_bind] at supported
  obtain ⟨before,present⟩ := Set.mem_iUnion.mp supported
  obtain ⟨priorSupported,laterSupported⟩ := Set.mem_iUnion.mp present
  have same := DependentStageContinuation.predecessor select start child before outcome laterSupported
  have retained := DependentStageContinuation.preserves select start child finish (Retains (earlier before))
    (fun memory initial result present previous => trans previous (localFact memory initial result present))
    before outcome laterSupported (incoming before priorSupported)
  simpa only [same] using retained

variable {F Index : Type} [Field F] {b : ℕ}
/-- Retaining checkpoints retains every anchor of any constructed family. -/
theorem family_recorded (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index H b)
    (before after : State Input Digest H) (retained : Retains before after)
    (recorded : RecordedPaddedSourceFamily.Recorded world before) :
    RecordedPaddedSourceFamily.Recorded world after := by
  intro index
  exact retained _ _ (recorded index)

/-- Lift a complete checkpoint-retention invariant to arbitrary recorded
families without expanding the experiment at its concrete instantiation. -/
theorem families_of_retains {Outcome : Type}
    (experiment : ProbComp Outcome) (earlier final : Outcome → State Input Digest H)
    (retained : ∀ outcome ∈ support experiment, Retains (earlier outcome) (final outcome))
    (outcome : Outcome) (supported : outcome ∈ support experiment)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index H b)
    (recorded : RecordedPaddedSourceFamily.Recorded world (earlier outcome)) :
    RecordedPaddedSourceFamily.Recorded world (final outcome) :=
  family_recorded world _ _ (retained outcome supported) recorded

end
end FormalProof4FHE.HasteBoots.CheckpointHistoryChain
