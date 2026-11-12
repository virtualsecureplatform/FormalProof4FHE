module
import all FormalProof4FHE.HasteBoots.CallerDerivedIdentityWork
import all FormalProof4FHETest.HasteBootsClaimReceiptCoverageSmoke
import all FormalProof4FHETest.HasteBootsDeferredRegistrySmoke

namespace HasteBootsSourceFramingRecoverySmoke
open FormalProof4FHE.HasteBoots
open NativePrefixCodec (Vector)
open OracleProgram (run)
noncomputable section

open HasteBootsRegistryAncestrySmoke (description registry world contexts_computed)
open HasteBootsDeferredRegistrySmoke (allRequests values query initial)

def collected := (HasteBootsDeferredRegistrySmoke.collected allRequests values).1.progress

theorem collector_keys_unique : (collected.state.claims.val.map SourceClaimGroupCardinality.claimKey).Nodup := by
  have invariant := NativeSourceClaimInvariant.program_invariants description registry allRequests query values initial world rfl
  have computed := NativeRegistryAncestry.contexts_order description registry.val world HasteBootsRegistryAncestrySmoke.expected.val contexts_computed
  have sources := NativeSharedSourceClaims.loop_sources description registry allRequests query values (List.finRange registry.val.length) ⟨initial,[]⟩ world
  change collected.state.sources = HasteBootsRegistryAncestrySmoke.expected at sources
  rw [← sources] at computed
  exact SourceClaimGroupCardinality.keys_nodup query collected invariant.2.1 invariant.1
    (SourceClaimGroupCardinality.represented_of_origins description registry allRequests values world collected computed invariant.2.2.2)

theorem every_collected_group_singleton (group : Fin (NativeSourceRegistry.groupCount collected.state.sources)) :
    (NativeDeferredOpeningBatch.groupClaims collected.state group).length ≤ 1 :=
  SourceClaimGroupCardinality.group_le_one collected.state collector_keys_unique group

theorem original_aliases_retained : collected.state.claims.val.map (fun claim => claim.slot.val) = [0,2] ∧
    (NativeDeferredOpeningBatch.usedGroups collected.state).map Fin.val = [0,1] := by decide +kernel

theorem collector_registry_small : AllocatedSourceClaimFraming.RegistrySmall registry := by
  intro slot
  fin_cases slot <;> decide +kernel

theorem collected_parent_framed : NativeTranscriptFraming.Framed collected.state.parent :=
  NativeTranscriptFraming.of_extension (NativeTranscriptFraming.new [] _ (by decide))
    (AllocatedSourceClaimFraming.program description registry collector_registry_small allRequests query values initial world)

open HasteBootsDeferredAvailabilitySmoke (native)

def firstQuery := native.queries.val[0]'(by decide +kernel)
def firstValue := native.values.val[0]'(by decide +kernel)
def singletonState := (NativeDeferredOpeningBatch.push HasteBootsDeferredAvailabilitySmoke.registry
  (NativeDeferredOpeningBatch.initial HasteBootsDeferredAvailabilitySmoke.metadata) ⟨1,by decide⟩ firstQuery firstValue).1

def singletonOpening : NativeGoldBatchOpening.Opening :=
  {native.opening with evaluations := ⟨native.opening.evaluations.val.take 1,by
    exact lt_of_le_of_lt (List.length_take_le _ _) (by decide : 1 < 2^64)⟩}

def singletonCtx : NativeDeferredBatchVerification.Context :=
  {HasteBootsDeferredAvailabilitySmoke.ctx with state := singletonState, proof := ⟨[singletonOpening],by decide⟩}

def execution := (run (NativeDeferredBatchVerification.program singletonCtx (HasteBootsBatchPcsSmoke.choose false) ())
  HasteBootsDeferredAvailabilitySmoke.world).run.1

theorem singleton_completed : (FormalProof4FHE.HasteBoots.ClaimReceiptCoverageSmoke.done? execution).isSome = true := by decide +kernel

def after := (FormalProof4FHE.HasteBoots.ClaimReceiptCoverageSmoke.done? execution).get singleton_completed

theorem executed : (run (NativeDeferredBatchVerification.program singletonCtx (HasteBootsBatchPcsSmoke.choose false) ())
    HasteBootsDeferredAvailabilitySmoke.world).run.1 = .verification (.done after) := by
  have present := singleton_completed
  cases equal : execution with
  | sealRejected state reason => simp [equal,ClaimReceiptCoverageSmoke.done?] at present
  | verification result =>
    cases result with
    | done actual => change execution = _; simp only [after,equal,ClaimReceiptCoverageSmoke.done?,Option.get_some]
    | stopped progress call outcome => simp [equal,ClaimReceiptCoverageSmoke.done?] at present
    | indexingUnavailable progress group slot => simp [equal,ClaimReceiptCoverageSmoke.done?] at present
    | packetUnavailable progress => simp [equal,ClaimReceiptCoverageSmoke.done?] at present

theorem singleton_registry_small : AllocatedSourceClaimFraming.RegistrySmall singletonCtx.registry := by
  intro slot
  fin_cases slot <;> decide +kernel

theorem singleton_groups (group : Fin (NativeSourceRegistry.groupCount singletonCtx.state.sources)) :
    (NativeDeferredOpeningBatch.groupClaims singletonCtx.state group).length ≤ 1 := by
  apply SourceClaimGroupCardinality.group_le_one
  decide +kernel

theorem singleton_responses : ∀ opening ∈ singletonCtx.proof.val,
    (NativeGoldBatchResponseBinding.payload opening).length < TranscriptFrame.lengthLimit := by
  intro opening member
  have same : opening = singletonOpening := by simpa only [singletonCtx,List.mem_singleton] using member
  subst opening
  decide +kernel

theorem singleton_parent_framed : NativeTranscriptFraming.Framed singletonCtx.state.parent := by
  rw [NativeTranscriptFraming.framed_iff_decode]
  decide +kernel

theorem actual_batch_receipts_framed : NativeDeferredBatchFraming.ValidProgress singletonCtx.tables singletonCtx.fieldFuel after :=
  CollectedBatchFramingRecovery.program_framed singletonCtx (HasteBootsBatchPcsSmoke.choose false) ()
    HasteBootsDeferredAvailabilitySmoke.world after executed singleton_registry_small singleton_groups singleton_responses singleton_parent_framed

theorem accepted_receipt_retained : after.receipts.length = 1 := by decide +kernel

theorem raw_dispatcher_can_have_multiple_claims :
    (NativeDeferredOpeningBatch.groupClaims HasteBootsDeferredAvailabilitySmoke.ctx.state ⟨0,by decide +kernel⟩).length = 4 := by decide +kernel

theorem alias_rejection_parent_framed : NativeTranscriptFraming.Framed
    (HasteBootsDeferredRegistrySmoke.collected allRequests HasteBootsDeferredRegistrySmoke.badValues).1.progress.state.parent :=
  NativeTranscriptFraming.of_extension (NativeTranscriptFraming.new [] _ (by decide))
    (AllocatedSourceClaimFraming.program description registry collector_registry_small allRequests query HasteBootsDeferredRegistrySmoke.badValues initial world)

theorem alias_rejection_retains_prefix : HasteBootsDeferredRegistrySmoke.stopped
    (HasteBootsDeferredRegistrySmoke.collected allRequests HasteBootsDeferredRegistrySmoke.badValues).1 = true := by decide +kernel

theorem invalid_query_emits_no_claim_frame :
    (NativeDeferredOpeningBatch.push registry initial ⟨0,by decide⟩ ⟨[],by decide⟩ (HasteBootsDeferredRegistrySmoke.row 0)).1.parent.input =
      initial.parent.input := by decide +kernel

end
end HasteBootsSourceFramingRecoverySmoke
