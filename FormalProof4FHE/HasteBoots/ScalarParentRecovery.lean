module
public import FormalProof4FHE.HasteBoots.ScalarExecutionRecovery
public import FormalProof4FHE.HasteBoots.ScalarCompletedOrigin
public import FormalProof4FHE.HasteBoots.ReceiptSequence
@[expose] public section

/-! The strict scalar parser recovers the actual parent of every completed
native reader. Producing ticks and unchanged drive headers are derived from
execution; no parent equality or sampling-state witness is supplied. -/
namespace FormalProof4FHE.HasteBoots.ScalarParentRecovery
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeScalarBatchWire (Statement)
open NativeScalarBatchPreflight (Proof)
open NativeScalarBatchVerifier (CompletedRound)
noncomputable section

structure Completed where
  transcript : Transcript
  statement : Statement
  proof : Proof
  world : World
  fuel : ℕ
  entry : CompletedRound
  framed : ReceiptSequence.Framed transcript
  accepted : ∃ bound, NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok bound
  statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit
  domain : NativeScalarTranscriptExtension.RoundDomain proof
  member : entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
    (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed

theorem recover (reader : Completed) :
    ∃ configuration : ScalarRecoveredReplay.Configuration,
      ScalarRecoveredReplay.recover reader.entry.coefficients.phase.pending.input = some configuration ∧
      TranscriptFrame.encodeMany configuration.view.history.before = reader.transcript.input ∧
      configuration.view.history.statement = reader.statement ∧ configuration.view.packet = reader.entry.packet := by
  obtain ⟨before,decoded⟩ := reader.framed
  obtain ⟨bound,accepted⟩ := reader.accepted
  obtain ⟨index,_,field,after,active,finished,_,_,_⟩ := ScalarCompletedOrigin.initialized reader.transcript reader.statement reader.proof
    reader.fuel reader.world reader.entry reader.member
  obtain ⟨rounds,reconstructed,recovered,_,_,_⟩ := ScalarExecutionRecovery.sampling reader.transcript bound before reader.statement reader.proof
    decoded accepted reader.statementFits reader.domain index reader.world reader.entry.packet field active
  have header := ScalarExecutionTranscript.drive_header NativeFields.goldilocksModulus 1 field reader.world
  rw [finished] at header
  have pending : reader.entry.coefficients.phase.pending = field.phase.pending := header.1
  refine ⟨⟨⟨ScalarExecutionTranscript.history before reader.statement rounds,reader.entry.packet⟩,reconstructed⟩,?_,?_,rfl,rfl⟩
  · rw [pending]
    exact recovered
  · exact (TranscriptFrame.decodeAll_sound _ _ decoded).2.symm

theorem parent_of_found (reader : Completed) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover reader.entry.coefficients.phase.pending.input = some configuration) :
    TranscriptFrame.encodeMany configuration.view.history.before = reader.transcript.input ∧
      configuration.view.history.statement = reader.statement ∧ configuration.view.packet = reader.entry.packet := by
  obtain ⟨actual,recovered,parent,statement,packet⟩ := recover reader
  have same := Option.some.inj (recovered.symm.trans found)
  cases same
  exact ⟨parent,statement,packet⟩

/-- Equal completed-reader inputs bind the actual parents, statements and
round packets, even when contexts, proofs, budgets and worlds differ. -/
theorem compare (left right : Completed)
    (same : left.entry.coefficients.phase.pending.input = right.entry.coefficients.phase.pending.input) :
    left.transcript.input = right.transcript.input ∧ left.statement = right.statement ∧ left.entry.packet = right.entry.packet := by
  obtain ⟨configuration,found,parent,statement,packet⟩ := recover left
  have rightFound : ScalarRecoveredReplay.recover right.entry.coefficients.phase.pending.input = some configuration := by rw [← same]; exact found
  have other := parent_of_found right configuration rightFound
  exact ⟨parent.symm.trans other.1,statement.symm.trans other.2.1,packet.symm.trans other.2.2⟩

end
end FormalProof4FHE.HasteBoots.ScalarParentRecovery
