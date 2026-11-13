module
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! A decoded coefficient value can be carried from an earlier canonical source
world into a later retained history, outside the one later collision event. -/
namespace FormalProof4FHE.HasteBoots.RecordedSourceWorldTransport
noncomputable section
variable {q c lanes : ℕ} [Fact q.Prime]
  {Cfg Input Digest Source : Type} [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}

/-- Changing the final state does not change a retained source's decoded
ciphertext, unless the later audited history has a collision exception. -/
theorem cipher_slot_eq_or_bad
    (localFamily : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (recorded : RecordedPaddedSourceFamily.Recorded localFamily before)
    (retained : CheckpointHistoryChain.Retains before after)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) after)
    (source : Source) :
    PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family before) enc dummy
      (RecordedSourceWorld.slot localFamily before recorded source) =
    PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family after) enc dummy
      (RecordedSourceWorld.slot localFamily after
        (CheckpointHistoryChain.family_recorded localFamily before after retained recorded) source) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) after := by
  have earlierRecorded := CheckpointHistoryChain.family_recorded
    (RecordedSourceWorld.family (F := ZMod q) (b := 2^lanes) before) before after retained
    (RecordedSourceWorld.recorded before)
  rcases RecordedSourceWorld.cipher_eq_or_bad (c := c)
      (RecordedSourceWorld.family before) enc dummy after audited earlierRecorded with equal | bad
  · exact Or.inl (congrFun equal (RecordedSourceWorld.slot localFamily before recorded source))
  · exact Or.inr bad

/-- An established increment equality survives all later retained verifier
stages, with only the same later collision exception. -/
theorem equality_persistent
    (localFamily : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (recorded : RecordedPaddedSourceFamily.Recorded localFamily before)
    (retained : CheckpointHistoryChain.Retains before after)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) after)
    (source : Source) (expected : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (correct : PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family before) enc dummy
      (RecordedSourceWorld.slot localFamily before recorded source) = expected) :
    PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family after) enc dummy
      (RecordedSourceWorld.slot localFamily after
        (CheckpointHistoryChain.family_recorded localFamily before after retained recorded) source) = expected ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) after := by
  rcases cipher_slot_eq_or_bad localFamily enc dummy before after recorded retained audited source with equal | bad
  · exact Or.inl (equal.symm.trans correct)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.RecordedSourceWorldTransport
