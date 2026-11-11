module
import all FormalProof4FHE.HasteBoots.HelperProfileLineage
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke
import all FormalProof4FHETest.HasteBootsCausalPcsSmoke

namespace FormalProof4FHE.HasteBoots.ProfileLineageSmoke
open InputIndexedOracle (World Byte)
open NativeTranscript (Transcript)
open OracleProgram (run)
noncomputable section

/-- The original single-opening fixture retains all four sampler profiles. -/
example : ∃ sample, ∃ receipt : SingleOpeningSamplingReceipt.Receipt SingleSelectedSmoke.ctx
    SingleSelectedSmoke.world SingleSelectedSmoke.work sample,
    receipt.bound.profile = SingleSelectedSmoke.ctx.transcript.profile ∧
    receipt.next.profile = SingleSelectedSmoke.ctx.transcript.profile ∧
    sample.transcript.profile = SingleSelectedSmoke.ctx.transcript.profile ∧
    SingleSelectedSmoke.work.transcript.profile = SingleSelectedSmoke.ctx.transcript.profile := by
  obtain ⟨sample,⟨receipt⟩⟩ := SingleOpeningSamplingReceipt.ofPreparation _ _ _ SingleSelectedSmoke.prepared
  exact ⟨sample,receipt,SingleOpeningProfileLineage.receipt_profile receipt⟩

example : SingleSelectedSmoke.work.transcript.profile = SingleSelectedSmoke.ctx.transcript.profile :=
  SingleOpeningProfileLineage.prepared_profile _ _ _ SingleSelectedSmoke.prepared

open HasteBootsCausalPcsSmoke (calls select repeated repeatedCancelled)
open NativePcsClaimSmoke (blockTables retainedParameters parent)

/-- The real repeated-call fixture stops after its first accepted helper. -/
example : (match repeated.1 with | .stopped _ _ _ => true | _ => false) = true ∧
    repeated.1.progress.receipts.length = 1 ∧
    HelperProfileLineage.Consistent parent.profile repeated.1.progress := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  exact HelperProfileLineage.trace_profiles
    (NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select false) 6
      (calls ++ calls) ⟨parent,(),[]⟩ NativePcsClaimSmoke.Canonical.world) _
    ⟨rfl,by intro receipt member; cases member⟩

/-- Scheduler cancellation retains the profile without requiring acceptance. -/
example : HelperProfileLineage.Consistent parent.profile repeatedCancelled.1.progress :=
  HelperProfileLineage.trace_profiles
    (NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select true) 6
      (calls ++ calls) ⟨parent,(),[]⟩ NativePcsClaimSmoke.Canonical.world) _
    ⟨rfl,by intro receipt member; cases member⟩

/-- Arbitrary, possibly nonconstant profiles are covered in every oracle world. -/
example (profile : Fin 64 → Byte) (world : World) (fuel : ℕ) :
    HelperProfileLineage.Consistent profile
      (run (NativeGoldHelperVerification.loop blockTables retainedParameters 18 (select false) fuel
        (calls ++ calls) ⟨{parent with profile := profile},(),[]⟩) world).run.1.progress :=
  HelperProfileLineage.trace_profiles
    (NativeGoldHelperVerification.loop_trace blockTables retainedParameters 18 (select false) fuel
      (calls ++ calls) ⟨{parent with profile := profile},(),[]⟩ world) _
    ⟨rfl,by intro receipt member; cases member⟩

/-- Even rejected detached finishes keep the parent's original metadata. -/
example (world : World) (parent : Transcript) (child : TypedTranscriptChild.Child) :
    ((TypedTranscriptChild.finishExecute world (some parent) child).1.parent.map Transcript.profile) = some parent.profile :=
  LookupProfileLineage.finish_parent_profile world parent child

end
end FormalProof4FHE.HasteBoots.ProfileLineageSmoke
