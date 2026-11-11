module
public import FormalProof4FHE.HasteBoots.AllocatedSourceCube
@[expose] public section

/-! The original helper allocation and proof-root ordinal determine the whole
public cube, with its independent width and native full-dimension row cast. -/
namespace FormalProof4FHE.HasteBoots.AllocatedHelperCube
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)

abbrev reference := AllocatedScalarHelper.reference entries reachable helperHandle references template ctx assembled
  (AllocatedLookupTables.helperIndex origin index)

theorem parameters : (reference origin index entries reachable helperHandle references template assembled).parameters = ctx.helper :=
  (AllocatedScalarHelper.entry_spec entries reachable helperHandle references template ctx assembled).2.2.symm

theorem sizes (geometry : AllocatedLookupTables.Geometry origin index job) :
    GoldHistorySourceTable.Geometry (reference origin index entries reachable helperHandle references template assembled).parameters := by
  change GoldHistorySourceTable.Geometry (AllocatedScalarHelper.entry entries reachable helperHandle references template ctx assembled).initialized.parameters
  exact (AllocatedScalarHelper.entry_spec entries reachable helperHandle references template ctx assembled).2.2 ▸ geometry.helper

variable (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ)

theorem helper_cube :
    HEq (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius)
      (GoldHistoryPublicExtraction.cube (reference origin index entries reachable helperHandle references template assembled) dummy
        (InputIndexedOracle.sha512 world (GoldContextInput.bytes (reference origin index entries reachable helperHandle references template assembled).parameters))
        (ctx.proof.roots.val.get (AllocatedLookupTables.helperIndex origin index)) history radius
        ((AllocatedScalarHelper.origin entries reachable helperHandle references template ctx assembled (AllocatedLookupTables.helperIndex origin index)).capacityAt _ rfl)
        (sizes origin index job entries reachable helperHandle references template assembled geometry)) := by
  have digest := congrArg (fun p => InputIndexedOracle.sha512 world (GoldContextInput.bytes p))
    (parameters origin index entries reachable helperHandle references template assembled)
  rw [digest]
  unfold AllocatedLookupTables.helpers ScalarPublicSourceModel.publicPacked
  exact AllocatedSourceCube.cast_table
    ((congrArg (fun p => p.numVariables.val) (parameters origin index entries reachable helperHandle references template assembled)).trans
      ((congrArg Fin.val origin.helper_dimensions.1).trans job.view.dimension))
    ((congrArg (fun p => p.width.val) (parameters origin index entries reachable helperHandle references template assembled)).trans
      (AllocatedLookupTables.helperWidth origin)) _

theorem owner_cube (candidate : NativeGoldPcsExecution.Context) (owner : CacheBackedSingleOpening.Origin candidate)
    (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (OracleProgram.run candidate.prefix world).run.1 = .prepared work)
    (same : candidate.parameters = (reference origin index entries reachable helperHandle references template assembled).parameters)
    (root : candidate.root = ctx.proof.roots.val.get (AllocatedLookupTables.helperIndex origin index))
    (small : 3*radius < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1)
    (framed : SingleOpeningAvailability.Framed candidate)
    (responseFits : (SingleOpeningColumnLaw.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (sample : NativeIndexRequest.Result) (sampler : SingleOpeningSamplingReceipt.Receipt candidate world work sample)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (recovered : SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog) :
    HEq (SingleOpeningNativeObligation.source dummy candidate owner world work prepared decoded sourceLog radius)
      (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template assembled geometry dummy history radius) := by
  have compatible := HelperPublicSource.compatible candidate (reference origin index entries reachable helperHandle references template assembled) owner
    (AllocatedScalarHelper.origin entries reachable helperHandle references template ctx assembled (AllocatedLookupTables.helperIndex origin index))
    same root world work prepared dummy history
  have admitted : 3*radius < (reference origin index entries reachable helperHandle references template assembled).parameters.code.blocks.val-
      (reference origin index entries reachable helperHandle references template assembled).parameters.code.messageBlocks.val+1 := by
    rw [parameters origin index entries reachable helperHandle references template assembled]
    exact small
  exact (compatible radius admitted framed responseFits sample sampler decoded parsed sourceLog recovered).trans
    (helper_cube origin index job entries reachable helperHandle references template assembled geometry dummy history radius).symm

end
end FormalProof4FHE.HasteBoots.AllocatedHelperCube
