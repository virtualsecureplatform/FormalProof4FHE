module
public import FormalProof4FHE.HasteBoots.SingleOpeningProfileLineage
public import FormalProof4FHE.HasteBoots.LookupProfileLineage
public import FormalProof4FHE.HasteBoots.NativeGoldLookupVerification
@[expose] public section

/-! Every recorded helper belongs to the original lookup parent's profile.
The invariant includes retained receipts when a later call stops. -/
namespace FormalProof4FHE.HasteBoots.HelperProfileLineage
open InputIndexedOracle (World Byte)
open NativeTranscript (Observation)
open NativeGoldHelperVerification
open OracleProgram (run)
noncomputable section

def Consistent {Memory : Type} (profile : Fin 64 → Byte) (progress : Progress Memory) : Prop :=
  progress.lastAccepted.profile = profile ∧ ∀ receipt ∈ progress.receipts,
    receipt.before.profile = profile ∧ receipt.after.profile = profile

theorem trace_profiles {Memory : Type} {tables : NativeGoldBlockCode.Tables}
    {parameters : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored} {fieldFuel : ℕ}
    {choose : NativeGoldPcsProgram.Scheduler Memory} {workerFuel : ℕ} {world : World}
    {calls : List (NativeSharedLookupHelpers.Call NativeGoldPcsOpening.Opening)} {before : Progress Memory}
    {result : Result Memory} {log : List Observation}
    (trace : Trace tables parameters fieldFuel choose workerFuel world calls before result log)
    (profile : Fin 64 → Byte) (consistent : Consistent profile before) : Consistent profile result.progress := by
  induction trace with
  | done before => exact consistent
  | stopped before call rest outcome log executed stopped => exact consistent
  | passed before after call rest outcome log result later executed advanced tail ih =>
    obtain ⟨work,completion,next,outcomeEq,accepted,same⟩ := advance_spec before call outcome after advanced
    have completed := (congrArg Prod.fst executed).trans outcomeEq
    have nextProfile := SingleOpeningProfileLineage.accepted_profile
      (context tables parameters fieldFuel before.lastAccepted call) choose workerFuel before.memory world work completion completed next accepted
    change next.profile = before.lastAccepted.profile at nextProfile
    apply ih
    rw [same]
    refine ⟨nextProfile.trans consistent.1,?_⟩
    intro receipt member
    rcases List.mem_append.mp member with old | added
    · exact consistent.2 receipt old
    · obtain rfl := List.mem_singleton.mp added
      exact ⟨consistent.1,nextProfile.trans consistent.1⟩

theorem helpers_profiles {B Memory : Type} (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : Result Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .helpers bound plan status) :
    Consistent ctx.parent.profile status.progress := by
  have origin := helpers_origin ctx choose memory world bound plan status executed
  have native := congrArg Prod.fst origin.native
  simp only [Context.native,NativeSharedLookupHelpers.run_protocol] at native
  have parentProfile := LookupProfileLineage.bound_profile NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world bound native
  have trace := loop_trace ctx.tables ctx.helper ctx.fieldFuel choose ctx.workerFuel plan.calls ⟨bound.parent,memory,[]⟩ world
  rw [origin.helpers] at trace
  exact trace_profiles trace ctx.parent.profile ⟨parentProfile,by intro receipt member; cases member⟩

theorem receipt_profiles {B Memory : Type} (ctx : Context B) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : Result Memory)
    (executed : (run (program ctx choose memory) world).run.1 = .helpers bound plan status)
    (receipt : Receipt Memory) (member : receipt ∈ status.progress.receipts) :
    receipt.before.profile = ctx.parent.profile ∧ receipt.after.profile = ctx.parent.profile :=
  (helpers_profiles ctx choose memory world bound plan status executed).2 receipt member

/-- The same invariant survives the enclosing lookup's source verification,
including a source failure after helpers have already completed. -/
theorem lookup_profiles {Memory : Type}
    (ctx : Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (bound : NativeSharedLookupBody.Bound)
    (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening) (status : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx choose chooseBatch memory) world).run.1.helpers.1 = .helpers bound plan status) :
    Consistent ctx.parent.profile status.progress := by
  exact helpers_profiles ctx choose memory world bound plan status
    ((NativeGoldLookupVerification.program_helpers_value ctx choose chooseBatch memory world).symm.trans executed)

end
end FormalProof4FHE.HasteBoots.HelperProfileLineage
