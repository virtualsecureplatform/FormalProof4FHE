module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFirstFieldSource
public import FormalProof4FHE.HasteBoots.NativeGoldBatchPreparedChallenge
@[expose] public section

/-! Actual later native acceptance uses the source recovered from the old
column history. First-field prefix recovery, not a future source witness,
fixes the common log. Authentication excludes the existing global source
exception; global soundness and physical-work accounting remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredSourceAvailability
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBatchFieldInputView (View)
open NativeRootFamilySourceSelection (Log)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (height shape Height)
open NativeGoldRawRequests (Request)
open NativeGoldBatchRawAvailability (Equations view)
open NativeGoldBatchFamilyAvailability (reconstructed)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Available (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (history : List Observation) (field : View) (sourceLog : Log) : Prop :=
  ∃ requests : List (NativeGoldColumnWorker.Job × Request height),
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some field.data.context ∧
    NativeGoldBatchFamilyRequests.prepare field.data.context work = some requests ∧
    (∀ index : Height, ⟨(field.data.context,index),⟨work.root,sourceLog⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) ∧
    ∀ entry ∈ requests,
      entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,sourceLog⟩ entry.2.position ∧
      Equations (view work requests) (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,sourceLog⟩ entry.2.position) entry.2.position.val

theorem accepted_recovered {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (history : List Observation) (field : View)
    (parsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase work).pending.input = some field)
    (sourceLog : Log) (found : NativeGoldBatchFirstFieldSource.recover dummy history field = some sourceLog)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    Available dummy ctx world work history field sourceLog := by
  obtain ⟨before,offset,values,after,_,positive,split,same⟩ := NativeGoldBatchFirstFieldSource.recover_sound dummy history field sourceLog found
  have inputEq := (NativeGoldBatchFieldInputView.parse_sound _ field parsed ctx.parent.profile).1
  rw [NativeGoldBatchFieldInputView.phase_input] at inputEq
  change NativeGoldBatchFirstFieldSource.input field = (NativeGoldBatchRandomLaw.phase work).pending.input at inputEq
  rw [inputEq] at split
  rw [split] at accepted truthful noDisagreement ⊢
  rw [same]
  exact NativeGoldBatchSelectedSource.accepted_selected dummy ctx world work choose fuel memory before after field parsed offset values positive accepted truthful noDisagreement

/-- The source is computed from the original column prefix. A later suffix
may contain all native verification queries, but cannot replace that source. -/
theorem accepted_column_history {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (columnHistory suffix : List Observation)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (sourceLog : Log) (found : NativeGoldBatchFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (columnHistory++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (columnHistory++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy (columnHistory++suffix))) :
    Available dummy ctx world work (columnHistory++suffix) decoded.field sourceLog := by
  have nativeAccepted := accepted
  obtain ⟨⟨before,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  have fieldParsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase work).pending.input = some decoded.field := by
    rw [← origin.2.1,NativeGoldBatchFieldInputView.phase_input]
    exact NativeGoldBatchFirstFieldSource.linked_field_parsed _ decoded parsed
  exact accepted_recovered dummy ctx world work choose fuel memory _ decoded.field fieldParsed sourceLog
    (NativeGoldBatchFirstFieldSource.recover_append dummy columnHistory suffix decoded.field sourceLog found) nativeAccepted truthful noDisagreement
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredSourceAvailability
