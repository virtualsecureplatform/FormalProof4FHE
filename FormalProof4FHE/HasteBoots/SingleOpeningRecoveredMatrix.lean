module
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldColumnLaw
public import FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
public import FormalProof4FHE.HasteBoots.SingleOpeningRectangularAcceptance
@[expose] public section

/-! Recover the native single-opening rectangular random matrix from fixed
public dimensions and the actual collector state. The matrix definition has
no future Prepared work or oracle-world argument. Parsing the actual column
nonce recovers the state used by the native accepted checks. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningRecoveredMatrix
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open SingleOpeningRectangularData (Row Weights rowEquiv)
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

def random (ctx : Context) (state : NativeFieldVector.State)
    (lane : Fin ctx.parameters.width.val) (row : Row ctx) : NativeFields.Goldilocks :=
  ((state.values[lane.val*(2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)+
    (row.1.val*ctx.parameters.width.val+row.2.val)]?).getD 0 : ℕ)

theorem prepared_random {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    Weights ctx world work prepared work.random = random ctx receipt.state := by
  funext lane row
  have count := SingleOpeningRandomLaw.count prepared
  have dimensions := (SingleOpeningRectangularData.dimensions ctx world work prepared).2.2
  have bounded : lane.val*work.geometry.rows+(rowEquiv ctx world work prepared row).val < work.geometry.randomCount.val := by
    rw [count]
    have a := lane.isLt
    have b := (rowEquiv ctx world work prepared row).isLt
    nlinarith
  have word := SingleOpeningRandomLaw.prepared_word receipt ⟨_,bounded⟩
  change NativeGoldColumnChecks.view work.random
    (lane.val*work.geometry.rows+(rowEquiv ctx world work prepared row).val) = _
  rw [word]
  simp only [random,SingleOpeningRectangularData.rowEquiv_val,dimensions]

/-- Full pointwise nonce recovery identifies the same native random matrix;
this is not a claim that the future Prepared value is past-measurable. -/
theorem parsed_random {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    Weights ctx world work prepared work.random =
      random ctx (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 := by
  have origin := SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed
  have same : (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 = receipt.state := origin.2.2.1
  rw [same]
  exact prepared_random receipt prepared

/-- Actual accepted random checks use the recovered collector matrix and
retain the native ordered draw vector. No new test response is selected. -/
theorem acceptance_random_checks {dummy : NativeRootMessage.Digest} {ctx : Context} {world : World}
    {work : Prepared} {history : List NativeTranscript.Observation} {origin : CacheBackedSingleOpening.Origin ctx}
    (accepted : SingleOpeningRectangularAcceptance.View dummy ctx world work history origin)
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work accepted.sample)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
      (NTTButterfly.domain (NativeGoldBlockCode.logSize ctx.parameters.code)
        (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) origin.primitive)
      (SingleOpeningRectangularChecks.source ctx world work accepted.prepared
        (SingleOpeningRectangularChecks.Frozen dummy accepted.context work accepted.log))
      (random ctx (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1)
      (SingleOpeningRectangularData.messages ctx ctx.opening.test.val) accepted.draw := by
  rw [← parsed_random receipt accepted.prepared before parent valid fits responseFits decoded parsed]
  exact accepted.randomChecks

end
end FormalProof4FHE.HasteBoots.SingleOpeningRecoveredMatrix
