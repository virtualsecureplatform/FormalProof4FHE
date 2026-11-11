module
public import FormalProof4FHE.HasteBoots.LookupWrongReceipts
public import FormalProof4FHE.HasteBoots.NativeGoldScalarQueryMeaning
@[expose] public section

/-! Actual accepted source/helper query pairs read as the original terminal
fold queries. The local extension post-map is separate from the PCS pairs,
including when the row point is empty. -/
namespace FormalProof4FHE.HasteBoots.LookupReceiptQueryMeaning
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
open NativeScalarQueryShape (laneBits)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem pairs_of_interpret {width n : ℕ} (raw : NativeGoldCoefficientsQuery.Query)
    (semantic : ExtensionQuery.Broadcast NativeFields.Goldilocks width n)
    (found : NativeGoldCoefficientsQuery.interpret width n raw = some semantic) :
    NativeGoldCoefficientsQuery.readPairs width n raw.pairs = some semantic.query := by
  unfold NativeGoldCoefficientsQuery.interpret at found
  cases pairs : NativeGoldCoefficientsQuery.readPairs width n raw.pairs with
  | none => simp only [pairs,Option.bind_none] at found; contradiction
  | some query =>
    cases post : NativeGoldCoefficientsQuery.readPost width raw.post with
    | none => simp only [pairs,post,Option.bind_some,Option.map_none] at found; contradiction
    | some matrix =>
      simp only [pairs,post,Option.bind_some,Option.map_some] at found
      cases Option.some.inj found
      rfl

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
include executed

theorem source_pairs :
    NativeGoldCoefficientsQuery.readPairs (3+origin.padding) lookup.body.sourceVariables lookup.query.models =
      some (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query := by
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).1
  have models := NativeGoldPcsWire.fromPairs_spec _ _ (NativeGoldLookupVerification.prepare_spec _ lookup prepared).2
  have guarded := (NativeSharedLookupGuard.guard_spec _ _ _ _ _ origin.guarded).query
  rw [origin.width,← job.view.pointEq] at guarded
  have interpreted := NativeGoldScalarQueryMeaning.scalarQuery_sourceQuery lookup.body.sourceVariables (List.ofFn job.view.point) job.view.shape
  rw [guarded,Option.bind_some] at interpreted
  have point : NativeGoldScalarQueryMeaning.fullPoint lookup.body.sourceVariables (List.ofFn job.view.point) job.view.shape =
      fun j => goldExtensionValue (job.view.point j) := by
    funext j
    simp only [NativeGoldScalarQueryMeaning.fullPoint,List.getElem_ofFn]
  rw [point] at interpreted
  rw [models]
  exact pairs_of_interpret _ _ interpreted

theorem helper_pairs :
    NativeGoldCoefficientsQuery.readPairs (3+AllocatedLookupTables.helperPadding (ctx := ctx))
      (laneBits (3+origin.padding)+lookup.body.sourceVariables) lookup.plan.query.models =
      some (ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query := by
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) executed).1
  have done := LookupHelperClaimMeaning.prepared_helpers ctx chooseHelper memory world lookup prepared
  have native := LookupHelperClaimMeaning.native_body ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers done
  have geometry := NativeSharedLookupHelpers.completed_geometry NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native
  have shape := geometry.1
  rw [AllocatedLookupTables.helperWidth origin] at shape
  have models := LookupHelperClaimMeaning.query_models ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers done
  rw [AllocatedLookupTables.helperWidth origin,← job.view.pointEq] at models
  rw [models]
  exact NativeGoldCoefficientsQuery.readPairs_built job.view.point shape

end
end FormalProof4FHE.HasteBoots.LookupReceiptQueryMeaning
