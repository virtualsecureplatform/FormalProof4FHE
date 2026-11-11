module
public import FormalProof4FHE.HasteBoots.GoldCommonSourceBinding
public import FormalProof4FHE.HasteBoots.SourceHistoryOwnerLog
@[expose] public section

/-! One complete-history analysis table per retained parameter/context/root.
An observed native opening uses this same table, with its exact old log
computed by immutable public snapshot lookup rather than supplied by a caller. -/
namespace FormalProof4FHE.HasteBoots.GoldHistorySourceTable
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativeRootFamilySourceSelection (Log)
open GoldCommonSourceTable (Primitive Capacity)
open InputIndexedOracle (World sha512)
open OracleProgram (run)
noncomputable section

abbrev Geometry (parameters : Parameters Stored) :=
  parameters.numVariables.val = parameters.leftVariables.val+(parameters.numVariables.val-parameters.leftVariables.val) ∧
    parameters.code.messageLength.val = 2^(parameters.numVariables.val-parameters.leftVariables.val)

def table (parameters : Parameters Stored) (primitive : Primitive parameters) (capacity : Capacity parameters)
    (dummy context root : Digest) (history : List Observation) (radius : ℕ) (geometry : Geometry parameters) :=
  GoldCommonSourceTable.table parameters primitive capacity dummy context root
    (SourceHistoryOwnerLog.selected history context root) radius geometry

theorem table_append (parameters : Parameters Stored) (primitive : Primitive parameters) (capacity : Capacity parameters)
    (dummy context root : Digest) (before after : List Observation) (radius : ℕ) (geometry : Geometry parameters)
    (height : NativeMerkleShapeFamily.Height) (sourceLog : Log)
    (present : ⟨(context,height),⟨root,sourceLog⟩⟩ ∈
      (NativeGoldBatchFamilyAvailability.reconstructed dummy before).checkpoints.checkpoints) :
    table parameters primitive capacity dummy context root (before++after) radius geometry =
      table parameters primitive capacity dummy context root before radius geometry := by
  unfold table
  rw [SourceHistoryOwnerLog.selected_append dummy before after context root height sourceLog present]

theorem batch_table (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : Primitive ctx.parameters) (capacity : Capacity ctx.parameters)
    (world : World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (framed : NativeGoldBatchSourceRisk.Framed ctx)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (history : List Observation) (sourceLog : Log)
    (recovered : NativeGoldBatchFirstFieldSource.recover dummy history decoded.field = some sourceLog) (radius : ℕ) :
    BatchOpeningNativeObligation.source dummy ctx primitive capacity world work prepared decoded radius sourceLog =
      table ctx.parameters primitive capacity dummy (sha512 world (GoldContextInput.bytes ctx.parameters)) ctx.root history radius
        (BatchOpeningNativeObligation.dimensions ctx world work prepared) := by
  have owner := SourceHistoryOwnerLog.batch_recovered dummy history decoded.field
    (NativeGoldBatchFirstFieldSource.linked_field_parsed _ decoded parsed) sourceLog recovered
  obtain ⟨context,root⟩ := GoldCommonSourceBinding.batch_binding ctx world work prepared framed responseFits decoded parsed
  rw [context,root] at owner
  rw [GoldCommonSourceBinding.batch_table dummy ctx primitive capacity world work prepared framed responseFits decoded parsed]
  unfold table
  rw [owner]

theorem single_table (dummy : Digest) {ctx : NativeGoldPcsExecution.Context} (origin : CacheBackedSingleOpening.Origin ctx)
    {world : World} {work : NativeGoldPcsWorkers.Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (framed : SingleOpeningAvailability.Framed ctx)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (history : List Observation) (sourceLog : Log)
    (recovered : SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog) (radius : ℕ) :
    SingleOpeningNativeObligation.source dummy ctx origin world work prepared decoded sourceLog radius =
      table ctx.parameters origin.primitive origin.capacity dummy (sha512 world (GoldContextInput.bytes ctx.parameters)) ctx.root history radius
        (SingleOpeningExtractedTableMeaning.prepared_dimensions ctx world work prepared) := by
  have owner := SourceHistoryOwnerLog.single_recovered dummy history decoded.field
    (SingleOpeningFirstFieldSource.linked_field_parsed _ decoded parsed) sourceLog recovered
  obtain ⟨context,root⟩ := GoldCommonSourceBinding.single_binding receipt prepared framed responseFits decoded parsed
  rw [context,root] at owner
  rw [GoldCommonSourceBinding.single_table dummy origin receipt prepared framed responseFits decoded parsed]
  unfold table
  rw [owner]

end
end FormalProof4FHE.HasteBoots.GoldHistorySourceTable
