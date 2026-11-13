module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.PackedCipherSource
@[expose] public section

/-! Transfer complete executed families into a common retained family using
public descriptor/root associations and the one final audited history. -/
namespace FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
noncomputable section
variable {F Cfg Input Digest Source Target : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ} {b : ℕ}

theorem logical_eq_or_bad
    (localFamily : RecordedPaddedSourceFamily.Family F Cfg Input Digest Source H b)
    (world : RecordedPaddedSourceFamily.Family F Cfg Input Digest Target H b)
    (slots : Source → Target)
    (parameters : ∀ source, localFamily.parameters source = world.parameters (slots source))
    (roots : ∀ source, localFamily.roots source = world.roots (slots source))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (arity : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (localRecorded : RecordedPaddedSourceFamily.Recorded localFamily state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state) :
    RecordedPaddedSourceFamily.logical localFamily enc dummy arity =
      (fun source => RecordedPaddedSourceFamily.logical world enc dummy arity (slots source)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr bad
  left
  funext source
  exact (RecordedPaddedSourceFamily.associated_owner_agrees_or_bad world enc dummy arity (slots source)
    (localFamily.parameters source) (parameters source) state audited worldRecorded
    (localFamily.owners source) (localRecorded source) ((localFamily.ownerRoots source).trans (roots source))).resolve_right bad

variable {q c lanes : ℕ} [Fact q.Prime]

theorem cipher_eq_or_bad
    (localFamily : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H (2^lanes))
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Target H (2^lanes))
    (slots : Source → Target)
    (parameters : ∀ source, localFamily.parameters source = world.parameters (slots source))
    (roots : ∀ source, localFamily.roots source = world.roots (slots source))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (localRecorded : RecordedPaddedSourceFamily.Recorded localFamily state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state) :
    (fun source => PackedCipherSource.familyCipher (c := c) localFamily enc dummy source) =
      (fun source => PackedCipherSource.familyCipher (c := c) world enc dummy (slots source)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  rcases logical_eq_or_bad localFamily world slots parameters roots enc dummy (c+1) state audited localRecorded worldRecorded with equal | bad
  · exact Or.inl (congrArg (fun tables => fun source => PackedCipherSource.unpack (tables source)) equal)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
