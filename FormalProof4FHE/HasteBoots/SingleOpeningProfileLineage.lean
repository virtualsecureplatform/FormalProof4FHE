module
public import FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
public import FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
@[expose] public section

/-! Profile preservation along the actual single-opening sampler and accepted
PCS program. No framing, freshness, or successful worker assumption is needed
for the sampler lineage; acceptance is used only to identify the final state. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningProfileLineage
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open OracleProgram (run)
noncomputable section

theorem index_profile (parent : Transcript) (label : InputIndexedOracle.Input)
    (domain count : NativeUsizeMessage.Usize) (world : World) (sample : NativeIndexRequest.Result)
    (drawn : (run (NativeIndexRequest.request parent label domain count) world).run.1 = some sample) :
    sample.transcript.profile = parent.profile := by
  have valid := NativeIndexRequest.accepted_check parent label domain count world sample drawn
  rw [NativeIndexRequest.run_request parent label domain count world valid] at drawn
  cases Option.some.inj drawn
  rfl

theorem receipt_profile {ctx : NativeGoldPcsExecution.Context} {world : World}
    {work : NativeGoldPcsWorkers.Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) :
    receipt.bound.profile = ctx.transcript.profile ∧ receipt.next.profile = ctx.transcript.profile ∧
      sample.transcript.profile = ctx.transcript.profile ∧ work.transcript.profile = ctx.transcript.profile := by
  obtain ⟨context,_,boundEq⟩ := SingleOpeningExposure.binding_origin ctx world receipt.bound receipt.binding
  have boundProfile : receipt.bound.profile = ctx.transcript.profile := by rw [boundEq]; rfl
  have header := SingleOpeningPreparedChallenge.prepared_header receipt
  have pendingProfile : receipt.state.phase.pending.profile = receipt.bound.profile :=
    (congrArg Transcript.profile header.1).trans (by rfl)
  have nextProfile : receipt.next.profile = ctx.transcript.profile := by
    rw [receipt.finished_parent]
    exact pendingProfile.trans boundProfile
  have sampleProfile := index_profile _ _ _ _ world sample receipt.drawn
  change sample.transcript.profile = receipt.next.profile at sampleProfile
  have finalProfile := sampleProfile.trans nextProfile
  exact ⟨boundProfile,nextProfile,finalProfile,by rw [receipt.transcript]; exact finalProfile⟩

theorem prepared_profile (ctx : NativeGoldPcsExecution.Context) (world : World)
    (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    work.transcript.profile = ctx.transcript.profile := by
  obtain ⟨sample,⟨receipt⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation ctx world work prepared
  exact (receipt_profile receipt).2.2.2

theorem accepted_profile {Memory : Type} (ctx : NativeGoldPcsExecution.Context)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : NativeGoldPcsWorkers.Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (next : Transcript) (accepted : completion.status = .accepted next) :
    next.profile = ctx.transcript.profile := by
  have origin := NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  rw [(NativeGoldPcsProgram.accepted_flags ctx choose fuel memory world work completion executed next accepted).2.2]
  exact prepared_profile ctx world work origin.prepared

end
end FormalProof4FHE.HasteBoots.SingleOpeningProfileLineage
