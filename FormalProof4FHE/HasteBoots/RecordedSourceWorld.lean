module
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
@[expose] public section

/-! The final history supplies one canonical decoded owner for every available
public descriptor/root pair. Executed families embed by their literal metadata;
no externally supplied common family or decoded-table association is needed. -/
namespace FormalProof4FHE.HasteBoots.RecordedSourceWorld
noncomputable section
variable {F Cfg Input Digest Source : Type} [Field F] {H : Cfg → ℕ} {b : ℕ}

structure Address (F Cfg Digest : Type) [Field F] (H : Cfg → ℕ) (b : ℕ) where
  parameters : RecordedPaddedSource.Parameters F Cfg H b
  root : Digest

def Available (address : Address F Cfg Digest H b)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) : Prop :=
  ∃ owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) address.parameters,
    owner.root = address.root ∧ ⟨address.parameters.tag,owner⟩ ∈ state.checkpoints.checkpoints

abbrev Index (F : Type) [Field F] (b : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) :=
  {address : Address F Cfg Digest H b // Available address state}

def family
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) :
    RecordedPaddedSourceFamily.Family F Cfg Input Digest (Index F b state) H b where
  parameters := fun index => index.val.parameters
  roots := fun index => index.val.root
  owners := fun index => Classical.choose index.property
  ownerRoots := fun index => (Classical.choose_spec index.property).1

theorem recorded
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H)) :
    RecordedPaddedSourceFamily.Recorded (family (F := F) (b := b) state) state := by
  intro index
  exact (Classical.choose_spec index.property).2

def slot (localFamily : RecordedPaddedSourceFamily.Family F Cfg Input Digest Source H b)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (localRecorded : RecordedPaddedSourceFamily.Recorded localFamily state) (source : Source) : Index F b state :=
  ⟨⟨localFamily.parameters source,localFamily.roots source⟩,
    localFamily.owners source,localFamily.ownerRoots source,localRecorded source⟩

/-- Uses of one public descriptor and caller root receive the same index,
independently of which recorded owner supplied their availability evidence. -/
theorem slot_eq {Other : Type}
    (left : RecordedPaddedSourceFamily.Family F Cfg Input Digest Source H b)
    (right : RecordedPaddedSourceFamily.Family F Cfg Input Digest Other H b)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (leftRecorded : RecordedPaddedSourceFamily.Recorded left state)
    (rightRecorded : RecordedPaddedSourceFamily.Recorded right state)
    (source : Source) (other : Other)
    (parameters : left.parameters source = right.parameters other)
    (roots : left.roots source = right.roots other) :
    slot left state leftRecorded source = slot right state rightRecorded other := by
  apply Subtype.ext
  change Address.mk (left.parameters source) (left.roots source) =
    Address.mk (right.parameters other) (right.roots other)
  rw [parameters,roots]

variable [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]

theorem logical_eq_or_bad
    (localFamily : RecordedPaddedSourceFamily.Family F Cfg Input Digest Source H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (arity : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (localRecorded : RecordedPaddedSourceFamily.Recorded localFamily state) :
    RecordedPaddedSourceFamily.logical localFamily enc dummy arity =
      (fun source => RecordedPaddedSourceFamily.logical (family state) enc dummy arity (slot localFamily state localRecorded source)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state :=
  RecordedFamilyEmbedding.logical_eq_or_bad localFamily (family state) (slot localFamily state localRecorded)
    (fun _ => rfl) (fun _ => rfl) enc dummy arity state audited localRecorded (recorded state)

variable {q c lanes : ℕ} [Fact q.Prime]

theorem cipher_eq_or_bad
    (localFamily : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (localRecorded : RecordedPaddedSourceFamily.Recorded localFamily state) :
    (fun source => PackedCipherSource.familyCipher (c := c) localFamily enc dummy source) =
      (fun source => PackedCipherSource.familyCipher (c := c) (family state) enc dummy (slot localFamily state localRecorded source)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state :=
  RecordedFamilyEmbedding.cipher_eq_or_bad localFamily (family state) (slot localFamily state localRecorded)
    (fun _ => rfl) (fun _ => rfl) enc dummy state audited localRecorded (recorded state)

end
end FormalProof4FHE.HasteBoots.RecordedSourceWorld
