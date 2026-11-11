module
public import FormalProof4FHE.HasteBoots.BatchOpeningProfileLineage
public import FormalProof4FHE.HasteBoots.SourceClaimProfileLineage
public import FormalProof4FHE.HasteBoots.HelperProfileLineage
@[expose] public section

/-! Source batch receipts retain the original lookup parent's profile through
helper completion, source insertion, sealing and every dispatch stop mode. -/
namespace FormalProof4FHE.HasteBoots.DeferredBatchProfileLineage
open InputIndexedOracle (World Byte)
open NativeTranscript (Observation)
open NativeDeferredBatchVerification
open OracleProgram (run)
noncomputable section

def Consistent {Memory : Type} (profile : Fin 64 → Byte) (progress : Progress Memory) : Prop :=
  progress.parent.profile = profile ∧ ∀ receipt ∈ progress.receipts,
    receipt.before.profile = profile ∧ receipt.after.profile = profile

theorem trace_profiles {Memory : Type} {tables : NativeGoldBlockCode.Tables}
    {registry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored)}
    {state : NativeDeferredOpeningBatch.State} {fieldFuel : ℕ}
    {choose : NativeGoldBatchPcsProgram.Scheduler Memory} {workerFuel : ℕ} {world : World}
    {groups : List (Fin (NativeSourceRegistry.groupCount state.sources))} {openings : List NativeGoldBatchOpening.Opening}
    {before : Progress Memory} {result : Result Memory} {log : List Observation}
    (trace : Trace tables registry state fieldFuel choose workerFuel world groups openings before result log)
    (profile : Fin 64 → Byte) (consistent : Consistent profile before) : Consistent profile result.progress := by
  induction trace with
  | done before => exact consistent
  | packets groups openings before mismatch => exact consistent
  | index group rest opening openings before missing => exact consistent
  | stopped group rest opening openings before planned outcome log computed executed failed => exact consistent
  | passed group rest opening openings before after planned outcome log result later computed executed advanced tail ih =>
    obtain ⟨work,completion,next,outcomeEq,accepted,same⟩ := advance_spec before planned outcome after advanced
    have completed := (congrArg Prod.fst executed).trans outcomeEq
    have nextProfile := BatchOpeningProfileLineage.accepted_profile (planned.context tables fieldFuel before.parent)
      choose workerFuel before.memory world work completion completed next accepted
    change next.profile = before.parent.profile at nextProfile
    apply ih
    rw [same]
    refine ⟨nextProfile.trans consistent.1,?_⟩
    intro receipt member
    rcases List.mem_append.mp member with old | added
    · exact consistent.2 receipt old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨consistent.1,nextProfile.trans consistent.1⟩

theorem program_profiles {Memory : Type} (ctx : Context) (choose : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (result : Result Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .verification result) :
    Consistent ctx.state.parent.profile result.progress := by
  have trace := (program_trace ctx choose memory world result executed).2
  exact trace_profiles trace _ ⟨SourceClaimProfileLineage.seal_profile _ _,by intro receipt member; cases member⟩

theorem lookup_profiles {Memory : Type}
    (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches prepared progress (.verification result)) : Consistent ctx.parent.profile result.progress := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have spec := (NativeGoldLookupVerification.prepare_spec _ prepared origin.1).1
  have erased : (run (NativeRegisteredLookup.helpers ctx chooseHelper memory) world).run.1.1 =
      (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.1 :=
    congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx chooseHelper memory world)
  have selected : (run (NativeRegisteredLookup.helpers ctx chooseHelper memory) world).run.1.1 =
      .helpers prepared.body prepared.plan (.done prepared.helpers) := congrArg Prod.fst spec
  have helperRun := erased.symm.trans selected
  have helperProfile := (HelperProfileLineage.helpers_profiles ctx chooseHelper memory world prepared.body prepared.plan (.done prepared.helpers) helperRun).1
  have sourceProfile := SourceClaimProfileLineage.program_profile NativeGoldBlockCode.description.row ctx.registry ctx.requests
    prepared.query ctx.proof.sources (NativeGoldLookupVerification.initial prepared) world
  change (run (NativeGoldLookupVerification.sourceProgram ctx prepared) world).run.1.progress.state.parent.profile = prepared.helpers.lastAccepted.profile at sourceProfile
  rw [origin.2.1] at sourceProfile
  have initialProfile := sourceProfile.trans helperProfile
  have batch := program_profiles (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch prepared.helpers.memory world result origin.2.2.1
  exact ⟨batch.1.trans initialProfile,fun receipt member =>
    ⟨(batch.2 receipt member).1.trans initialProfile,(batch.2 receipt member).2.trans initialProfile⟩⟩

end
end FormalProof4FHE.HasteBoots.DeferredBatchProfileLineage
