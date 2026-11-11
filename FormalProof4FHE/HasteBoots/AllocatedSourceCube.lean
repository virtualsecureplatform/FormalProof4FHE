module
public import FormalProof4FHE.HasteBoots.LookupReceiptQueryMeaning
@[expose] public section

/-! The selected original packed source is the executable public cube up to
only its native row/width transports. An accepted owner's extracted cube
therefore agrees with that complete function under original compatibility. -/
namespace FormalProof4FHE.HasteBoots.AllocatedSourceCube
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldParameterStore (Entry Reference)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open MatrixFold (Cube)
noncomputable section

theorem cast_table {n m width packed : ℕ} (rows : n = m) (lanes : width = packed)
    (table : Cube n → Fin width → NativeFields.Goldilocks) :
    HEq (fun cell : Cube m => fun lane : Fin packed => table (cast (congrArg Cube rows.symm) cell) (Fin.cast lanes.symm lane)) table := by
  cases rows
  cases lanes
  rfl

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (history : List Observation) (radius : ℕ)
    (column : Fin (origin.ready.jobs.get index).tag.request.columns)

theorem source_cube :
    HEq (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius column)
      (GoldHistoryPublicExtraction.cube (RegistryPublicSource.context ctx (job.slots.slot column)) dummy
        (InputIndexedOracle.sha512 world (GoldContextInput.bytes (ctx.registry.val.get (job.slots.slot column)).parameters))
        (ctx.registry.val.get (job.slots.slot column)).root history radius
        ((AllocatedScalarSource.origin entries reachable helperHandle references template ctx assembled (job.slots.slot column)).capacityAt _ rfl)
        (geometry.source column)) := by
  unfold AllocatedLookupTables.sources AllocatedLookupTables.sourceAt ScalarPublicSourceModel.publicPacked
  exact cast_table (origin.registry_dimensions (job.slots.slot column)).1 (origin.registry_dimensions (job.slots.slot column)).2 _

theorem owner_cube (candidate : NativeGoldBatchPcsProgram.Context) (owner : CacheBackedCodeOrigin.Origin candidate)
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
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (recovered : NativeGoldBatchFirstFieldSource.recover dummy history decoded.field = some sourceLog) :
    HEq (BatchOpeningNativeObligation.source dummy candidate (owner.primitiveAt _ rfl) (owner.capacityAt _ rfl)
        world work prepared decoded radius sourceLog)
      (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template assembled geometry dummy history radius column) := by
  have compatible := RegistryPublicSource.compatible candidate (RegistryPublicSource.context ctx (job.slots.slot column)) owner
    (AllocatedScalarSource.origin entries reachable helperHandle references template ctx assembled (job.slots.slot column))
    parameters root world work prepared dummy history
  exact (compatible radius small framed responseFits decoded parsed sourceLog recovered).trans
    (source_cube origin index job entries reachable helperHandle references template assembled geometry dummy history radius column).symm

end
end FormalProof4FHE.HasteBoots.AllocatedSourceCube
