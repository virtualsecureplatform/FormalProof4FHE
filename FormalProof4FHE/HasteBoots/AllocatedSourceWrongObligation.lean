module
public import FormalProof4FHE.HasteBoots.AllocatedSourceCube
public import FormalProof4FHE.HasteBoots.QueryPairFoldTransport
@[expose] public section

/-! A mismatch against an original complete source family is an actual
native batch Wrong obligation for its compatible accepted owner. Native
query decoding and the original pair index are retained. -/
namespace FormalProof4FHE.HasteBoots.AllocatedSourceWrongObligation
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeFieldRepresentation (goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
noncomputable section

variable {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (OracleProgram.run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ)
    (column : Fin (origin.ready.jobs.get index).tag.request.columns)

include executed

theorem wrong (candidate : NativeGoldBatchPcsProgram.Context) (owner : CacheBackedCodeOrigin.Origin candidate)
    (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram candidate) world).run.1 = .prepared work)
    (parameters : candidate.parameters = (ctx.registry.val.get (job.slots.slot column)).parameters)
    (root : candidate.root = (ctx.registry.val.get (job.slots.slot column)).root)
    (small : 3*radius < (ctx.registry.val.get (job.slots.slot column)).parameters.code.blocks.val-
      (ctx.registry.val.get (job.slots.slot column)).parameters.code.messageBlocks.val+1)
    (framed : NativeGoldBatchSourceRisk.Framed candidate)
    (responseFits : (NativeGoldBatchResponseBinding.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input candidate work world) = some decoded)
    (pair : Fin work.binding.queries.val.length) (row : NativeLookupRequestWire.Row)
    (queryAt : work.binding.queries.val[pair.val]? = some lookup.query)
    (rowAt : work.binding.values.val[pair.val]? = some row)
    (different : row.val.map goldValue ≠ List.ofFn
      ((ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ job.view.shape)
        (fun j => goldExtensionValue (job.view.point j))).query.fold
        (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius column))) :
    BatchOpeningNativeObligation.Wrong dummy candidate (owner.primitiveAt _ rfl) (owner.capacityAt _ rfl)
      world work prepared decoded history radius := by
  intro sourceLog recovered
  have cube := AllocatedSourceCube.owner_cube origin index job entries reachable helperHandle references template assembled geometry dummy history radius column
    candidate owner work prepared parameters root small framed responseFits decoded parsed sourceLog recovered
  have width : candidate.parameters.width.val = 3+origin.padding :=
    (congrArg (fun p => p.width.val) parameters).trans (origin.registry_dimensions (job.slots.slot column)).2
  have rows : candidate.parameters.numVariables.val = lookup.body.sourceVariables :=
    (congrArg (fun p => p.numVariables.val) parameters).trans (origin.registry_dimensions (job.slots.slot column)).1
  have nativeRead := LookupReceiptQueryMeaning.pairs_of_interpret _ _ (BatchOpeningNativeObligation.query_read candidate world work prepared pair)
  have rawQuery : work.binding.queries.val.get pair = lookup.query := by
    simpa only [List.get_eq_getElem] using Option.some.inj ((List.getElem?_eq_getElem pair.isLt).symm.trans queryAt)
  rw [rawQuery] at nativeRead
  have originalRead := LookupReceiptQueryMeaning.source_pairs ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
  have query := QueryPairFoldTransport.pairs_heq width rows _ _ _ nativeRead originalRead
  have folded := QueryPairFoldTransport.fold_list width rows _ _ _ _ query cube
  have encoded := BatchClaimShape.row_encoding candidate.parameters.width.val row
    (BatchClaimShape.prepared_width candidate world work prepared pair row rowAt)
  have claimed : row.val.map goldValue = List.ofFn (fun lane : Fin candidate.parameters.width.val =>
      NativeGoldBatchFixedResponseData.claimed work.binding.values pair.val lane.val) := by
    simpa only [NativeGoldBatchFixedResponseData.claimed,rowAt,Option.map_some,Option.getD_some] using encoded
  refine ⟨pair,?_⟩
  intro equal
  exact different (claimed.trans ((congrArg List.ofFn equal).trans folded))

end
end FormalProof4FHE.HasteBoots.AllocatedSourceWrongObligation
