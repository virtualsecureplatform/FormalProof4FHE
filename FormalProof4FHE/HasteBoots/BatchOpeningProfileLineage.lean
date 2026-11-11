module
public import FormalProof4FHE.HasteBoots.SingleOpeningProfileLineage
public import FormalProof4FHE.HasteBoots.NativeGoldBatchPreparedChallenge
@[expose] public section

/-! The original native batch sampler and accepted PCS preserve the parent's
profile, including rejected candidates inside the completed collector. -/
namespace FormalProof4FHE.HasteBoots.BatchOpeningProfileLineage
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (description)
open OracleProgram (run)
noncomputable section

theorem prepared_profile (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    work.sample.transcript.profile = ctx.parent.profile := by
  have header := NativeGoldBatchChallengeOrigin.prepared_header ctx world work prepared
  have drawn := NativeGoldBatchColumnRequestLaw.prepared_request ctx world work prepared
  have sampleProfile := SingleOpeningProfileLineage.index_profile _ _ _ _ world work.sample drawn
  change work.sample.transcript.profile = work.state.phase.pending.profile at sampleProfile
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,same⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening
    ctx.fieldFuel world geometry binding state weights sample prior
  have bound := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening
    ctx.fieldFuel world geometry binding (.finished state next) prelude).2.1
  obtain ⟨_,_,_,boundEq,_⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  have pending := congrArg Transcript.profile header.1
  have bindingProfile : work.binding.parent.profile = ctx.parent.profile := by rw [same,boundEq]; rfl
  exact sampleProfile.trans (pending.trans bindingProfile)

theorem accepted_profile {Memory : Type} (ctx : Context) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (next : Transcript) (accepted : completion.status = .accepted next) : next.profile = ctx.parent.profile := by
  have origin := NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  rw [(NativeGoldBatchPcsProgram.accepted_flags ctx choose fuel memory world work completion executed next accepted).2.2]
  exact prepared_profile ctx world work origin.prepared

end
end FormalProof4FHE.HasteBoots.BatchOpeningProfileLineage
