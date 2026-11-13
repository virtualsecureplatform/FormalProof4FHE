module
public import FormalProof4FHE.HasteBoots.ConstructedGoldRoleSourceDescriptors
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
@[expose] public section

/-! Native role allocation derives private-source agreement outside the same
audited collision event. Public role routing replaces a caller-supplied decoder
association; recorded snapshots and matching roots remain factual obligations. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldSourceCoherence
open NativeFields (Goldilocks)
open ConstructedGoldSourceDescriptor (Configuration heights)
open ConstructedGoldRoleSourceDescriptors (descriptor)
open ClassicalGoldRoleBundle (Bundle Stage roleIndex)
noncomputable section
variable {Input Digest : Type} [DecidableEq Input] [DecidableEq Digest] {n m : ℕ}

/-- The shared immutable native role determines the decoder association.
Private table equality is derived from the two actual recorded owners. -/
theorem table_agrees_or_bad
    (bundle : Bundle) (left right : Stage)
    (leftSource : roleIndex left = 0 ∨ roleIndex left = 2)
    (rightSource : roleIndex right = 0 ∨ roleIndex right = 2)
    (sameRole : roleIndex left = roleIndex right) (radius : ℕ)
    (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (leftOwner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (descriptor bundle left leftSource radius))
    (rightOwner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (descriptor bundle right rightSource radius))
    (leftRecorded : ⟨(descriptor bundle left leftSource radius).tag,leftOwner⟩ ∈ state.checkpoints.checkpoints)
    (rightRecorded : ⟨(descriptor bundle right rightSource radius).tag,rightOwner⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : leftOwner.root = rightOwner.root) :
    RecordedPaddedSource.logical (descriptor bundle left leftSource radius) enc dummy n leftOwner =
      RecordedPaddedSource.logical (descriptor bundle right rightSource radius) enc dummy n rightOwner ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  let world : RecordedPaddedSourceFamily.Family Goldilocks Configuration Input Digest Unit heights 4 :=
    { parameters := fun _ => descriptor bundle right rightSource radius
      roots := fun _ => rightOwner.root
      owners := fun _ => rightOwner
      ownerRoots := fun _ => rfl }
  exact RecordedPaddedSourceFamily.associated_owner_agrees_or_bad world enc dummy n ()
    (descriptor bundle left leftSource radius)
    (ConstructedGoldRoleSourceDescriptors.descriptor_eq_of_role bundle left right leftSource rightSource sameRole radius)
    state audited (fun _ => rightRecorded) leftOwner leftRecorded sameRoot

/-- Reindexed/padded uses of one native original source agree at the same
native scalar address, even with different logical query arities. -/
theorem address_agrees_or_bad
    (bundle : Bundle) (left right : Stage)
    (leftSource : roleIndex left = 0 ∨ roleIndex left = 2)
    (rightSource : roleIndex right = 0 ∨ roleIndex right = 2)
    (sameRole : roleIndex left = roleIndex right) (radius : ℕ)
    (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (leftOwner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (descriptor bundle left leftSource radius))
    (rightOwner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) (descriptor bundle right rightSource radius))
    (leftRecorded : ⟨(descriptor bundle left leftSource radius).tag,leftOwner⟩ ∈ state.checkpoints.checkpoints)
    (rightRecorded : ⟨(descriptor bundle right rightSource radius).tag,rightOwner⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : leftOwner.root = rightOwner.root)
    (leftCell : MatrixFold.Cube n) (rightCell : MatrixFold.Cube m)
    (sameAddress : (FlatMatrixFold.index n leftCell).val = (FlatMatrixFold.index m rightCell).val) :
    RecordedPaddedSource.logical (descriptor bundle left leftSource radius) enc dummy n leftOwner leftCell =
      RecordedPaddedSource.logical (descriptor bundle right rightSource radius) enc dummy m rightOwner rightCell ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rcases table_agrees_or_bad bundle left right leftSource rightSource sameRole radius enc dummy state audited
    leftOwner rightOwner leftRecorded rightRecorded sameRoot with same | bad
  · left
    exact (congrFun same leftCell).trans
      (RecordedPaddedSource.logical_same_address (descriptor bundle right rightSource radius) enc dummy rightOwner leftCell rightCell sameAddress)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.ConstructedGoldSourceCoherence
