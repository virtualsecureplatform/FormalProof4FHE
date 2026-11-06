module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredCollector
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRectangularAcceptance
@[expose] public section

/-! The rectangular native random matrix is a function of fixed context
parameters and the retained collector state. Its definition does not inspect
future Prepared work, source logs, scheduler state or oracle worlds. Source
ownership and the false-claim disagreement reduction remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredMatrix
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchRectangularWeights (Row rowEquiv)
open NativeGoldBatchRectangularChecks (lane)
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

def random (ctx : Context) (state : NativeFieldVector.State)
    (index : Fin ctx.parameters.width.val) (row : Row ctx) : NativeFields.Goldilocks :=
  ((state.values[index.val*(2^ctx.parameters.leftVariables.val*ctx.parameters.width.val)+
    (row.1.val*ctx.parameters.width.val+row.2.val)]?).getD 0 : ℕ)

theorem prepared_random (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    NativeGoldBatchRectangularChecks.random ctx world work prepared = random ctx work.state := by
  funext index row
  have count := NativeGoldBatchRandomLaw.prepared_count ctx world work prepared
  have dimensions := (NativeGoldBatchWeightMeaning.prepared_dimensions ctx world work prepared).2.2
  have bounded : (lane ctx world work prepared index).val*work.geometry.rows+(rowEquiv ctx world work prepared row).val < work.geometry.randomCount.val := by
    rw [count]
    have a : (lane ctx world work prepared index).val < ctx.parameters.width.val := by
      simpa only [lane,Fin.val_cast] using index.isLt
    have b := (rowEquiv ctx world work prepared row).isLt
    nlinarith
  have word := NativeGoldBatchRandomLaw.prepared_word ctx world work prepared ⟨_,bounded⟩
  change NativeGoldColumnChecks.view work.random
    ((lane ctx world work prepared index).val*work.geometry.rows+(rowEquiv ctx world work prepared row).val) = _
  rw [word]
  simp only [random,lane,Fin.val_cast,NativeGoldBatchRectangularWeights.rowEquiv_val,dimensions]

/-- This supplies precisely the matrix argument used by native accepted
random checks, using the actual parsed input's collected state. -/
theorem parsed_random (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    NativeGoldBatchRectangularChecks.random ctx world work prepared =
      random ctx (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1 := by
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  rw [origin.2.2.1]
  exact prepared_random ctx world work prepared

/-- The actual acceptance view retains the identical random checks after
replacing the future-work matrix by the recovered-state definition. -/
theorem acceptance_random_checks (dummy : NativeRootMessage.Digest) (ctx : Context) (world : World) (work : Prepared)
    (history : List NativeTranscript.Observation)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (accepted : NativeGoldBatchRectangularAcceptance.View dummy ctx world work history primitive)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
      (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      (NativeGoldBatchRectangularWeights.source ctx world work accepted.prepared
        (NativeGoldBatchLinearEquations.Frozen dummy accepted.context work accepted.log))
      (random ctx (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel decoded world).1)
      (NativeGoldBatchRectangularData.testMessages ctx work) accepted.draw := by
  rw [← parsed_random ctx world work accepted.prepared before parent valid fits responseFits decoded parsed]
  exact accepted.randomChecks
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredMatrix
