module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
@[expose] public section

/-! Recorded source families survive actual shared execution and can be
extended with newly recorded roots. Public metadata/root aliases remain subject
to the same audited collision exclusion, without a source-value premise. -/
namespace FormalProof4FHE.HasteBoots.RecordedFamilyHistory
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Cfg Input Digest Index Extra Result : Type} [Field F]
  {heights : Cfg → ℕ} {b n : ℕ}

/-- Extend the index set while preserving every old anchor and decoder. -/
def append (left : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (right : RecordedPaddedSourceFamily.Family F Cfg Input Digest Extra heights b) :
    RecordedPaddedSourceFamily.Family F Cfg Input Digest (Index ⊕ Extra) heights b where
  parameters := Sum.elim left.parameters right.parameters
  roots := Sum.elim left.roots right.roots
  owners := fun index => match index with
    | .inl index => left.owners index
    | .inr index => right.owners index
  ownerRoots := fun index => match index with
    | .inl index => left.ownerRoots index
    | .inr index => right.ownerRoots index

theorem append_recorded
    (left : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (right : RecordedPaddedSourceFamily.Family F Cfg Input Digest Extra heights b)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) :
    RecordedPaddedSourceFamily.Recorded (append left right) state ↔
      RecordedPaddedSourceFamily.Recorded left state ∧ RecordedPaddedSourceFamily.Recorded right state := by
  constructor
  · intro recorded
    exact ⟨fun index => recorded (.inl index),fun index => recorded (.inr index)⟩
  · rintro ⟨leftRecorded,rightRecorded⟩ index
    cases index with
    | inl index => exact leftRecorded index
    | inr index => exact rightRecorded index

variable [DecidableEq F] [DecidableEq Digest]

theorem append_logical_left
    (left : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (right : RecordedPaddedSourceFamily.Family F Cfg Input Digest Extra heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (index : Index) :
    RecordedPaddedSourceFamily.logical (append left right) enc dummy n (.inl index) =
      RecordedPaddedSourceFamily.logical left enc dummy n index := rfl

theorem append_logical_right
    (left : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (right : RecordedPaddedSourceFamily.Family F Cfg Input Digest Extra heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (index : Extra) :
    RecordedPaddedSourceFamily.logical (append left right) enc dummy n (.inr index) =
      RecordedPaddedSourceFamily.logical right enc dummy n index := rfl

variable [DecidableEq Input]

/-- Distinct slots for one public descriptor/root agree only via recorded
owners and the enclosing audit; matching root digests alone do not suffice. -/
theorem aliases_agree_or_bad
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (left right : Index) (parameters : world.parameters left = world.parameters right)
    (roots : world.roots left = world.roots right)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : RecordedPaddedSourceFamily.Recorded world state) :
    RecordedPaddedSourceFamily.logical world enc dummy n left =
      RecordedPaddedSourceFamily.logical world enc dummy n right ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state :=
  RecordedPaddedSourceFamily.associated_owner_agrees_or_bad world enc dummy n right
    (world.parameters left) parameters state audited recorded (world.owners left) (recorded left)
    ((world.ownerRoots left).trans roots)

variable [SampleableType Digest]

omit [DecidableEq F] in
/-- Every anchor survives a literal shared oracle computation, on every
supported branch including rejection and early return. -/
theorem recorded_run
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (program : OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (recorded : RecordedPaddedSourceFamily.Recorded world initial)
    (outcome : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (supported : outcome ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy (AmbientMatrixSource.Shape heights)) program).run initial)) :
    RecordedPaddedSourceFamily.Recorded world outcome.2 := by
  intro index
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (AmbientMatrixSource.Shape heights) (world.parameters index).tag (world.owners index)
    program initial (recorded index) outcome supported

end
end FormalProof4FHE.HasteBoots.RecordedFamilyHistory
