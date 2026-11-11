module
public import FormalProof4FHE.HasteBoots.GoldCommonSourceBinding
public import FormalProof4FHE.HasteBoots.SourceSnapshotLogIdentity
@[expose] public section

/-! Actual parsed native calls with the same full parameters and root use
one analysis table, even when their first field reads occur at different
points in the containing history. Exact recovered-log equality is derived. -/
namespace FormalProof4FHE.HasteBoots.GoldRecoveredSourceTableIdentity
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open GoldCommonSourceTable (Primitive Capacity)
noncomputable section

theorem batches (dummy : Digest) (history : List Observation)
    (first second : NativeGoldBatchPcsProgram.Context)
    (firstPrimitive : Primitive first.parameters) (secondPrimitive : Primitive second.parameters)
    (firstCapacity : Capacity first.parameters) (secondCapacity : Capacity second.parameters)
    (world : World) (firstWork secondWork : NativeGoldBatchPcsProgram.Prepared)
    (firstPrepared : (run (NativeGoldBatchPcsProgram.prepareProgram first) world).run.1 = .prepared firstWork)
    (secondPrepared : (run (NativeGoldBatchPcsProgram.prepareProgram second) world).run.1 = .prepared secondWork)
    (firstFramed : NativeGoldBatchSourceRisk.Framed first) (secondFramed : NativeGoldBatchSourceRisk.Framed second)
    (firstFits : (NativeGoldBatchResponseBinding.payload first.opening).length < TranscriptFrame.lengthLimit)
    (secondFits : (NativeGoldBatchResponseBinding.payload second.opening).length < TranscriptFrame.lengthLimit)
    (firstView secondView : NativeGoldBatchChallengeLink.View)
    (firstParsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input first firstWork world) = some firstView)
    (secondParsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input second secondWork world) = some secondView)
    (parameters : first.parameters = second.parameters) (root : first.root = second.root)
    (firstLog secondLog : Log)
    (firstRecovered : NativeGoldBatchFirstFieldSource.recover dummy history firstView.field = some firstLog)
    (secondRecovered : NativeGoldBatchFirstFieldSource.recover dummy history secondView.field = some secondLog) (radius : ℕ) :
    HEq (BatchOpeningNativeObligation.source dummy first firstPrimitive firstCapacity world firstWork firstPrepared firstView radius firstLog)
      (BatchOpeningNativeObligation.source dummy second secondPrimitive secondCapacity world secondWork secondPrepared secondView radius secondLog) := by
  obtain ⟨firstContext,firstRoot⟩ := GoldCommonSourceBinding.batch_binding first world firstWork firstPrepared firstFramed firstFits firstView firstParsed
  obtain ⟨secondContext,secondRoot⟩ := GoldCommonSourceBinding.batch_binding second world secondWork secondPrepared secondFramed secondFits secondView secondParsed
  have context : firstView.field.data.context = secondView.field.data.context := by rw [firstContext,secondContext,parameters]
  have roots := firstRoot.trans (root.trans secondRoot.symm)
  have logs := SourceSnapshotLogIdentity.batches dummy history firstView.field secondView.field
    (NativeGoldBatchFirstFieldSource.linked_field_parsed _ firstView firstParsed)
    (NativeGoldBatchFirstFieldSource.linked_field_parsed _ secondView secondParsed)
    context roots firstLog secondLog firstRecovered secondRecovered
  rw [logs]
  exact GoldCommonSourceTable.batches_same dummy first second firstPrimitive secondPrimitive firstCapacity secondCapacity
    world firstWork secondWork firstPrepared secondPrepared firstView secondView parameters context roots secondLog radius

theorem single_batch (dummy : Digest) (history : List Observation)
    (single : NativeGoldPcsExecution.Context) (origin : CacheBackedSingleOpening.Origin single)
    (batch : NativeGoldBatchPcsProgram.Context) (primitive : Primitive batch.parameters) (capacity : Capacity batch.parameters)
    (world : World) (singleWork : NativeGoldPcsWorkers.Prepared) (batchWork : NativeGoldBatchPcsProgram.Prepared)
    (singlePrepared : (run single.prefix world).run.1 = .prepared singleWork)
    (batchPrepared : (run (NativeGoldBatchPcsProgram.prepareProgram batch) world).run.1 = .prepared batchWork)
    {sample : NativeIndexRequest.Result} (receipt : SingleOpeningSamplingReceipt.Receipt single world singleWork sample)
    (singleFramed : SingleOpeningAvailability.Framed single) (batchFramed : NativeGoldBatchSourceRisk.Framed batch)
    (singleFits : (SingleOpeningColumnLaw.payload single.opening).length < TranscriptFrame.lengthLimit)
    (batchFits : (NativeGoldBatchResponseBinding.payload batch.opening).length < TranscriptFrame.lengthLimit)
    (singleView : SingleOpeningChallengeLink.View) (batchView : NativeGoldBatchChallengeLink.View)
    (singleParsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some singleView)
    (batchParsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input batch batchWork world) = some batchView)
    (parameters : single.parameters = batch.parameters) (root : single.root = batch.root)
    (singleLog batchLog : Log)
    (singleRecovered : SingleOpeningFirstFieldSource.recover dummy history singleView.field = some singleLog)
    (batchRecovered : NativeGoldBatchFirstFieldSource.recover dummy history batchView.field = some batchLog) (radius : ℕ) :
    HEq (SingleOpeningNativeObligation.source dummy single origin world singleWork singlePrepared singleView singleLog radius)
      (BatchOpeningNativeObligation.source dummy batch primitive capacity world batchWork batchPrepared batchView radius batchLog) := by
  obtain ⟨singleContext,singleRoot⟩ := GoldCommonSourceBinding.single_binding receipt singlePrepared singleFramed singleFits singleView singleParsed
  obtain ⟨batchContext,batchRoot⟩ := GoldCommonSourceBinding.batch_binding batch world batchWork batchPrepared batchFramed batchFits batchView batchParsed
  have context : singleView.field.data.context = batchView.field.data.context := by rw [singleContext,batchContext,parameters]
  have roots := singleRoot.trans (root.trans batchRoot.symm)
  have logs := SourceSnapshotLogIdentity.single_batch dummy history singleView.field batchView.field
    (SingleOpeningFirstFieldSource.linked_field_parsed _ singleView singleParsed)
    (NativeGoldBatchFirstFieldSource.linked_field_parsed _ batchView batchParsed)
    context roots singleLog batchLog singleRecovered batchRecovered
  rw [logs]
  exact GoldCommonSourceTable.single_batch_same dummy single origin batch primitive capacity world singleWork batchWork
    singlePrepared batchPrepared singleView batchView parameters context roots batchLog radius

end
end FormalProof4FHE.HasteBoots.GoldRecoveredSourceTableIdentity
