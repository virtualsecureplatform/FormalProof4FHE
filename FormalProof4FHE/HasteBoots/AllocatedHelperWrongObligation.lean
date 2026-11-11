module
public import FormalProof4FHE.HasteBoots.AllocatedHelperCube
public import FormalProof4FHE.HasteBoots.QueryPairFoldTransport
@[expose] public section

/-! A wrong original helper row is a native single-opening Wrong obligation
on the same complete extracted cube and actual query matrices. -/
namespace FormalProof4FHE.HasteBoots.AllocatedHelperWrongObligation
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
open NativeScalarQueryShape (laneBits)
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
include executed

theorem wrong (candidate : NativeGoldPcsExecution.Context) (owner : CacheBackedSingleOpening.Origin candidate)
    (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (OracleProgram.run candidate.prefix world).run.1 = .prepared work)
    (same : candidate.parameters = (AllocatedHelperCube.reference origin index entries reachable helperHandle references template assembled).parameters)
    (root : candidate.root = ctx.proof.roots.val.get (AllocatedLookupTables.helperIndex origin index))
    (small : 3*radius < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1)
    (framed : SingleOpeningAvailability.Framed candidate)
    (responseFits : (SingleOpeningColumnLaw.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (sample : NativeIndexRequest.Result) (sampler : SingleOpeningSamplingReceipt.Receipt candidate world work sample)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded)
    (queryEq : candidate.query = lookup.plan.query)
    (expected : Fin candidate.parameters.width.val → NativeFields.Goldilocks)
    (encoded : candidate.claimed.val.map goldValue = List.ofFn expected)
    (different : candidate.claimed.val.map goldValue ≠ List.ofFn
      ((ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query.fold
        (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius))) :
    SingleOpeningNativeObligation.Wrong dummy candidate owner world work prepared decoded history radius expected := by
  intro sourceLog recovered
  have cube := AllocatedHelperCube.owner_cube origin index job entries reachable helperHandle references template assembled geometry dummy history radius
    candidate owner work prepared same root small framed responseFits sample sampler decoded parsed sourceLog recovered
  have parameters := same.trans (AllocatedHelperCube.parameters origin index entries reachable helperHandle references template assembled)
  have width : candidate.parameters.width.val = 3+AllocatedLookupTables.helperPadding (ctx := ctx) :=
    (congrArg (fun p => p.width.val) parameters).trans (AllocatedLookupTables.helperWidth origin)
  have rows : candidate.parameters.numVariables.val = laneBits (3+origin.padding)+lookup.body.sourceVariables :=
    (congrArg (fun p => p.numVariables.val) parameters).trans ((congrArg Fin.val origin.helper_dimensions.1).trans job.view.dimension)
  have nativeRead := LookupReceiptQueryMeaning.pairs_of_interpret _ _ (SingleOpeningNativeObligation.query_read candidate world work prepared)
  rw [queryEq] at nativeRead
  have originalRead := LookupReceiptQueryMeaning.helper_pairs ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
  have query := QueryPairFoldTransport.pairs_heq width rows _ _ _ nativeRead originalRead
  have folded := QueryPairFoldTransport.fold_list width rows _ _ _ _ query cube
  intro equal
  exact different (encoded.trans ((congrArg List.ofFn equal).trans folded))

end
end FormalProof4FHE.HasteBoots.AllocatedHelperWrongObligation
