module
import all FormalProof4FHE.HasteBoots.GoldHistoryPublicExtraction
import all FormalProof4FHETest.HasteBootsSourceLogIdentitySmoke
import all FormalProof4FHETest.HasteBootsRecoveredChallengeSmoke

namespace FormalProof4FHE.HasteBoots.HistorySourceSmoke
open HasteBootsBatchMeaningSmoke (root)
open SourceLogIdentitySmoke (history batch original firstRecovered batchParsed)
open NativeTranscript (Observation)
noncomputable section

/-- Lookup from the complete history returns the original one-entry log. -/
theorem selected_original : SourceHistoryOwnerLog.selected history batch.data.context batch.data.root = original :=
  SourceHistoryOwnerLog.batch_recovered root history batch batchParsed original firstRecovered

/-- Later observations cannot move a recorded source owner's exact log. -/
example (suffix : List Observation) : SourceHistoryOwnerLog.selected (history++suffix) batch.data.context batch.data.root = original := by
  rw [SourceHistoryOwnerLog.selected_append root history suffix batch.data.context batch.data.root 0 original
    (NativeGoldBatchFirstFieldSource.recover_snapshot root history batch batchParsed original firstRecovered 0)]
  exact selected_original

/-- Before recording, the fallback can change with the hash log. Stability
requires an actual recorded key or successful canonical field recovery. -/
example : (SourceHistoryOwnerLog.selected [] root root).length = 0 ∧
    (SourceHistoryOwnerLog.selected [.hash [10] (List.ofFn root)] root root).length = 1 := by decide +kernel

/-- Full root bytes remain part of the owner key. -/
example : SourceHistoryOwnerLog.key root root ≠ SourceHistoryOwnerLog.key root (fun _ => 1) := by
  intro same
  have views := congrArg StoredSourceVectorReadCost.sourceView same
  rw [SourceHistoryOwnerLog.key_view,SourceHistoryOwnerLog.key_view] at views
  have bytes := congrArg (fun key : NativeCanonicalLookupWire.Source => key.2 0) views
  change (0 : InputIndexedOracle.Byte) = 1 at bytes
  contradiction

section Native
open HasteBootsBatchOrderedSmoke (ctx world work prepared)
open HasteBootsEarlyReceiptSmoke (view)
open HasteBootsRecoveredChallengeSmoke (parent parentValid batchFits responseFits)
open HasteBootsFieldInputSmoke (parentFrames)

theorem field_same : view.field = batch := by
  have parsed := NativeGoldBatchFirstFieldSource.linked_field_parsed _ view HasteBootsFieldColumnSmoke.parsed
  have inputSame : NativeGoldBatchFirstFieldSource.input view.field = SourceLogIdentitySmoke.firstInput := by decide +kernel
  rw [inputSame] at parsed
  exact Option.some.inj (parsed.symm.trans batchParsed)

/-- Actual preparation, parsing and field recovery identify the executable
public cube under the original reachable constructor, with no selected-log or
parsed-context association certificate. -/
example (origin : CacheBackedCodeOrigin.Origin ctx) :
    BatchOpeningNativeObligation.source root ctx (origin.primitiveAt ctx rfl) (origin.capacityAt ctx rfl)
        world work prepared view 0 original =
      GoldHistoryPublicExtraction.cube ctx root (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.parameters)) ctx.root
        history 0 (origin.capacityAt ctx rfl) (BatchOpeningNativeObligation.dimensions ctx world work prepared) := by
  have recovered : NativeGoldBatchFirstFieldSource.recover root history view.field = some original := by rw [field_same]; exact firstRecovered
  exact GoldHistoryPublicExtraction.batch_source_eq_public root ctx origin world work prepared
    ⟨parentFrames,parent,parentValid,batchFits⟩ responseFits view HasteBootsFieldColumnSmoke.parsed history original recovered 0 (by decide +kernel)

/-- Removing original queries and values and changing verifier fuel cannot
change the executable table for the same public source identity. -/
example (origin : CacheBackedCodeOrigin.Origin ctx) :
    GoldHistoryPublicExtraction.cube ctx root batch.data.context batch.data.root history 0
        (origin.capacityAt ctx rfl) (BatchOpeningNativeObligation.dimensions ctx world work prepared) =
      GoldHistoryPublicExtraction.cube {ctx with queries := ⟨[],by decide⟩,values := ⟨[],by decide⟩,fieldFuel := 0}
        root batch.data.context batch.data.root history 0 (origin.capacityAt ctx rfl)
        (BatchOpeningNativeObligation.dimensions ctx world work prepared) :=
  eq_of_heq (GoldHistoryPublicExtraction.cube_congr ctx _ rfl root batch.data.context batch.data.root history 0
    (origin.capacityAt ctx rfl) (origin.capacityAt ctx rfl)
    (BatchOpeningNativeObligation.dimensions ctx world work prepared) (BatchOpeningNativeObligation.dimensions ctx world work prepared))

/-- The public extractor remains fixed under arbitrary later history. -/
example (origin : CacheBackedCodeOrigin.Origin ctx) (suffix : List Observation) :
    GoldHistoryPublicExtraction.cube ctx root batch.data.context batch.data.root (history++suffix) 0
        (origin.capacityAt ctx rfl) (BatchOpeningNativeObligation.dimensions ctx world work prepared) =
      GoldHistoryPublicExtraction.cube ctx root batch.data.context batch.data.root history 0
        (origin.capacityAt ctx rfl) (BatchOpeningNativeObligation.dimensions ctx world work prepared) :=
  GoldHistoryPublicExtraction.cube_append ctx origin root batch.data.context batch.data.root history suffix 0 (by decide +kernel)
    _ 0 original (NativeGoldBatchFirstFieldSource.recover_snapshot root history batch batchParsed original firstRecovered 0)

end Native
end
end FormalProof4FHE.HasteBoots.HistorySourceSmoke
