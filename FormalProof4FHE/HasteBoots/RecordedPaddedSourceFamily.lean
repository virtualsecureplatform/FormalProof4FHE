module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
@[expose] public section

/-! A common original-source interpretation built from actual retained owners.
A family fixes public decoder descriptors and caller roots, then chooses one
recorded owner per root. Its tables are decoded, not supplied as witnesses. -/
namespace FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
noncomputable section
variable {F Cfg Input Digest Index : Type} [Field F] {heights : Cfg → ℕ} {b n m : ℕ}

structure Family (F Cfg Input Digest Index : Type) [Field F] (heights : Cfg → ℕ) (b : ℕ) where
  parameters : Index → RecordedPaddedSource.Parameters F Cfg heights b
  roots : Index → Digest
  owners : ∀ index, RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (parameters index)
  ownerRoots : ∀ index, (owners index).root = roots index

def Recorded (family : Family F Cfg Input Digest Index heights b)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) : Prop :=
  ∀ index, ⟨(family.parameters index).tag,family.owners index⟩ ∈ state.checkpoints.checkpoints

/-- Availability of the actual caller roots constructs a common owner family;
no decoded-table or source-truth certificate is assumed. -/
theorem exists_recorded (parameters : Index → RecordedPaddedSource.Parameters F Cfg heights b)
    (roots : Index → Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (available : ∀ index, ∃ owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (parameters index),
      owner.root = roots index ∧ ⟨(parameters index).tag,owner⟩ ∈ state.checkpoints.checkpoints) :
    ∃ family : Family F Cfg Input Digest Index heights b,
      family.parameters = parameters ∧ family.roots = roots ∧ Recorded family state := by
  classical
  choose owners ownerRoots recorded using available
  exact ⟨⟨parameters,roots,owners,ownerRoots⟩,rfl,rfl,recorded⟩

variable [DecidableEq F] [DecidableEq Digest]

def logical (family : Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (n : ℕ) (index : Index) :=
  RecordedPaddedSource.logical (family.parameters index) enc dummy n (family.owners index)

/-- All logical presentations of an anchored root preserve native addresses. -/
theorem same_address (family : Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (index : Index)
    (left : MatrixFold.Cube n) (right : MatrixFold.Cube m)
    (address : (FlatMatrixFold.index n left).val = (FlatMatrixFold.index m right).val) :
    logical family enc dummy n index left = logical family enc dummy m index right :=
  RecordedPaddedSource.logical_same_address (family.parameters index) enc dummy (family.owners index) left right address

variable [DecidableEq Input]

/-- Any recorded use of the caller root agrees with the anchor selected after
execution, outside the already charged final exception. -/
theorem owner_agrees_or_bad (family : Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (n : ℕ) (index : Index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : Recorded family state)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (family.parameters index))
    (ownerRecorded : ⟨(family.parameters index).tag,owner⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : owner.root = family.roots index) :
    RecordedPaddedSource.logical (family.parameters index) enc dummy n owner = logical family enc dummy n index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state :=
  RecordedPaddedSource.logical_eq_or_bad (family.parameters index) enc dummy n state audited owner (family.owners index)
    ownerRecorded (recorded index) (ownerRoot.trans (family.ownerRoots index).symm)

/-- The literal padded source in a stage is a common family table under the
same final exclusion; dimensions, radius and domain come from one descriptor. -/
theorem padded_agrees_or_bad (family : Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (index : Index)
    (padding : ℕ) (dimensions : padding+n = (family.parameters index).front+(family.parameters index).suffix)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : Recorded family state)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (family.parameters index))
    (ownerRecorded : ⟨(family.parameters index).tag,owner⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : owner.root = family.roots index) :
    QueryHighZeroPadding.source padding (QueryReindex.source dimensions
      (AmbientMatrixSource.source (front := (family.parameters index).front) enc dummy heights
        (family.parameters index).domain (family.parameters index).capacity (family.parameters index).radius
        (family.parameters index).tag owner)) = logical family enc dummy n index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rw [RecordedPaddedSource.padded_eq_logical]
  exact owner_agrees_or_bad family enc dummy n index state audited recorded owner ownerRecorded ownerRoot
/-- Public decoder-parameter association transfers a use to its family slot.
The equality concerns context/code/domain/radius data, not decoded source values. -/
theorem associated_owner_agrees_or_bad (family : Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (n : ℕ) (index : Index)
    (parameters : RecordedPaddedSource.Parameters F Cfg heights b)
    (associated : parameters = family.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : Recorded family state)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) parameters)
    (ownerRecorded : ⟨parameters.tag,owner⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : owner.root = family.roots index) :
    RecordedPaddedSource.logical parameters enc dummy n owner = logical family enc dummy n index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  subst parameters
  exact owner_agrees_or_bad family enc dummy n index state audited recorded owner ownerRecorded ownerRoot

/-- Associate the actual stage's padded source with a common family table using
only public decoder metadata and retained-owner/root facts. -/
theorem associated_padded_agrees_or_bad (family : Family F Cfg Input Digest Index heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (index : Index)
    (parameters : RecordedPaddedSource.Parameters F Cfg heights b)
    (associated : parameters = family.parameters index)
    (padding : ℕ) (dimensions : padding+n = parameters.front+parameters.suffix)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (recorded : Recorded family state)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) parameters)
    (ownerRecorded : ⟨parameters.tag,owner⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : owner.root = family.roots index) :
    QueryHighZeroPadding.source padding (QueryReindex.source dimensions
      (AmbientMatrixSource.source (front := parameters.front) enc dummy heights parameters.domain parameters.capacity parameters.radius
        parameters.tag owner)) = logical family enc dummy n index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  subst parameters
  exact padded_agrees_or_bad family enc dummy index padding dimensions state audited recorded owner ownerRecorded ownerRoot

end
end FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
