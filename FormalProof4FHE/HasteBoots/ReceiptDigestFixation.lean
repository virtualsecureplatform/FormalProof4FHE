module
public import FormalProof4FHE.HasteBoots.ReceiptCandidateCompletion
public import FormalProof4FHE.HasteBoots.ReceiptCoefficientCandidates
@[expose] public section

/-! Digest matching after auxiliary completion fixes coefficients unless two
distinct earlier named receipt keys have the same full SHAKE digest. This
collision is an explicit new obligation, not the SHA-512 registry hash event. -/
namespace FormalProof4FHE.HasteBoots.ReceiptDigestFixation
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open ReceiptCandidateCompletion (digest extend)
open scoped Classical
noncomputable section

def Collision (history : List Observation) (world : World) : Prop :=
  ∃ left ∈ ReceiptPayloadView.payloads history, ∃ right ∈ ReceiptPayloadView.payloads history,
    left ≠ right ∧ digest world left = digest world right

def matching (history : List Observation) (world : World) (target : Digest) : Finset Input :=
  (ReceiptPayloadView.payloads history).filter (fun raw => digest world raw = target)

theorem matched_unique (history : List Observation) (world : World) (target : Digest)
    (safe : ¬ Collision history world) (left right : Input)
    (leftMatch : left ∈ matching history world target) (rightMatch : right ∈ matching history world target) : left = right := by
  obtain ⟨leftNamed,leftDigest⟩ := Finset.mem_filter.mp leftMatch
  obtain ⟨rightNamed,rightDigest⟩ := Finset.mem_filter.mp rightMatch
  by_contra different
  exact safe ⟨left,leftNamed,right,rightNamed,different,leftDigest.trans rightDigest.symm⟩

theorem matches_on_fiber {A : Type} {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (target : Digest) (same : (extend past other).run = (extend past world).run) :
    matching (past other).run.2 other target = matching (past world).run.2 world target := by
  have old := ReceiptCandidateCompletion.old_packet past world other same
  simp only [matching,old]
  ext raw
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨named,matchDigest⟩
    exact ⟨named,(ReceiptCandidateCompletion.digest_on_fiber replay world other raw named same).symm.trans matchDigest⟩
  · rintro ⟨named,matchDigest⟩
    exact ⟨named,(ReceiptCandidateCompletion.digest_on_fiber replay world other raw named same).trans matchDigest⟩

/-- Equal native 80-byte receipt messages imply equal full digests, even
when their encoded consumed lengths wrap. No length decoder is used. -/
theorem receipt_digest_equal (world other : World) (left right : Input)
    (same : (NativeTranscript.receipt world left).run.1 = (NativeTranscript.receipt other right).run.1) :
    digest other right = digest world left := by
  change TranscriptFrame.littleEndian 16 left.length ++ InputIndexedOracle.bytes world (NativeReceiptPrefixView.key left) 0 64 =
    TranscriptFrame.littleEndian 16 right.length ++ InputIndexedOracle.bytes other (NativeReceiptPrefixView.key right) 0 64 at same
  have dropped := congrArg (List.drop 16) same.symm
  have leftDrop : (TranscriptFrame.littleEndian 16 left.length ++ InputIndexedOracle.bytes world (NativeReceiptPrefixView.key left) 0 64).drop 16 =
      InputIndexedOracle.bytes world (NativeReceiptPrefixView.key left) 0 64 := by
    conv_lhs => arg 1; rw [← TranscriptFrame.littleEndian_length 16 left.length]
    rw [List.drop_left]
  have rightDrop : (TranscriptFrame.littleEndian 16 right.length ++ InputIndexedOracle.bytes other (NativeReceiptPrefixView.key right) 0 64).drop 16 =
      InputIndexedOracle.bytes other (NativeReceiptPrefixView.key right) 0 64 := by
    conv_lhs => arg 1; rw [← TranscriptFrame.littleEndian_length 16 right.length]
    rw [List.drop_left]
  rw [leftDrop,rightDrop] at dropped
  exact List.ofFn_inj.mp dropped

theorem coefficients_on_fiber {A : Type} {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (p : ℕ) (positive : 0 < CanonicalByteSampler.byteCount p)
    (left right : NativeFieldVector.State)
    (leftTrace : FieldConsumedReplay.Traced p left) (rightTrace : FieldConsumedReplay.Traced p right)
    (leftNamed : left.phase.consumed ∈ ReceiptPayloadView.payloads (past world).run.2)
    (rightNamed : right.phase.consumed ∈ ReceiptPayloadView.payloads (past other).run.2)
    (same : (extend past other).run = (extend past world).run)
    (sameDigest : digest other right.phase.consumed = digest world left.phase.consumed) :
    right.values = left.values ∨ Collision (past world).run.2 world := by
  by_cases bad : Collision (past world).run.2 world
  · exact Or.inr bad
  · apply Or.inl
    have rightNamedOld := rightNamed
    rw [ReceiptCandidateCompletion.old_packet past world other same] at rightNamedOld
    have rightDigest := (ReceiptCandidateCompletion.digest_on_fiber replay world other _ rightNamedOld same).symm.trans sameDigest
    have equal := matched_unique _ world (digest world left.phase.consumed) bad _ _
      (Finset.mem_filter.mpr ⟨rightNamedOld,rightDigest⟩) (Finset.mem_filter.mpr ⟨leftNamed,rfl⟩)
    exact FieldConsumedReplay.values_congr p positive right left rightTrace leftTrace equal

/-- A digest collision is witnessed by two actual full receipt outputs in
the auxiliary completion log, including their distinct raw query keys. -/
theorem collision_outputs {A : Type} (past : World → NativeTranscript.Execution A) (world : World)
    (bad : Collision (past world).run.2 world) :
    ∃ left right : Input, NativeReceiptPrefixView.key left ≠ NativeReceiptPrefixView.key right ∧
      digest world left = digest world right ∧
      .output (NativeReceiptPrefixView.key left) 0 (InputIndexedOracle.bytes world (NativeReceiptPrefixView.key left) 0 64) ∈ (extend past world).run.2 ∧
      .output (NativeReceiptPrefixView.key right) 0 (InputIndexedOracle.bytes world (NativeReceiptPrefixView.key right) 0 64) ∈ (extend past world).run.2 := by
  obtain ⟨left,leftNamed,right,rightNamed,different,equal⟩ := bad
  refine ⟨left,right,?_,equal,ReceiptCandidateCompletion.named_output past world left leftNamed,
    ReceiptCandidateCompletion.named_output past world right rightNamed⟩
  intro same
  exact different (List.append_cancel_left same)

end
end FormalProof4FHE.HasteBoots.ReceiptDigestFixation
