module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchRecoveredMatrix
import all FormalProof4FHETest.HasteBootsFieldColumnSmoke
import all FormalProof4FHETest.HasteBootsFreshReceiptSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (run)
namespace HasteBootsRecoveredChallengeSmoke
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchOrderedSmoke (ctx work world prepared)
open HasteBootsBatchMeaningSmoke (root)
open HasteBootsEarlyReceiptSmoke (view columnInput step)
open HasteBootsFieldInputSmoke (parentFrames parentDecoded)

theorem parent : ctx.parent.input = TranscriptFrame.encodeMany parentFrames :=
  (TranscriptFrame.decodeAll_sound _ _ parentDecoded).2
theorem parentValid : ∀ frame ∈ parentFrames, TranscriptFrame.Valid frame :=
  (TranscriptFrame.decodeAll_sound _ _ parentDecoded).1
theorem batchFits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
    (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit := by decide +kernel
theorem responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit := by decide +kernel

theorem state : (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel view world).1 = work.state := by
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared parentFrames parent parentValid batchFits responseFits
    view HasteBootsFieldColumnSmoke.parsed
  exact origin.2.2.1
example : view.receipt = (NativeTranscript.receipt world work.state.phase.consumed).run.1 := by
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared parentFrames parent parentValid batchFits responseFits
    view HasteBootsFieldColumnSmoke.parsed
  exact origin.2.2.2.1
example : view.column.opening.test = ctx.opening.test ∧ view.column.opening.evaluations = ctx.opening.evaluations := by
  have origin := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared parentFrames parent parentValid batchFits responseFits
    view HasteBootsFieldColumnSmoke.parsed
  exact ⟨origin.2.2.2.2.1,origin.2.2.2.2.2.1⟩
example : view.column.opening.columns.val = [] := by decide +kernel
example : work.width = 3 ∧ work.geometry.blockWidth = 4 := by decide +kernel
example : NativeGoldBatchRectangularChecks.random ctx world work prepared =
    NativeGoldBatchRecoveredMatrix.random ctx (NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel view world).1 :=
  NativeGoldBatchRecoveredMatrix.parsed_random ctx world work prepared parentFrames parent parentValid batchFits responseFits view HasteBootsFieldColumnSmoke.parsed
example (index : Fin work.geometry.randomCount.val) : NativeGoldColumnChecks.view work.random index.val =
    (((NativeGoldBatchFieldColumnLaw.collected ctx.parent.profile ctx.fieldFuel view world).1.values[index.val]?).getD 0 : NativeFields.Goldilocks) :=
  NativeGoldBatchRecoveredCollector.parsed_word ctx world work prepared parentFrames parent parentValid batchFits responseFits view HasteBootsFieldColumnSmoke.parsed index

-- Actual native preparation supplies completion and true receipt matching:
-- neither is a caller premise in the first-column case split.
example : NativeEarlyReceiptBound.event ctx.parent.profile step (HasteBootsFreshReceiptSmoke.cleanPast world).run world := by
  have first : CausalStreamExposure.firstRead step (HasteBootsFreshReceiptSmoke.cleanPast world).run = some columnInput := by decide +kernel
  have split := NativeGoldBatchRecoveredCollector.first_column_cases ctx world work prepared parentFrames parent parentValid batchFits responseFits
    (by decide +kernel) step (HasteBootsFreshReceiptSmoke.cleanPast world).run first
  rcases split with seen | event
  · have unseen : CausalStreamExposure.seen (HasteBootsFreshReceiptSmoke.cleanPast world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = false := rfl
    rw [unseen] at seen
    contradiction
  · exact event

-- A single earlier receipt byte still gives the native matching event.
example : NativeEarlyReceiptBound.event ctx.parent.profile step (HasteBootsEarlyReceiptSmoke.past world).run world := by
  have first : CausalStreamExposure.firstRead step (HasteBootsEarlyReceiptSmoke.past world).run = some columnInput := by decide +kernel
  have split := NativeGoldBatchRecoveredCollector.first_column_cases ctx world work prepared parentFrames parent parentValid batchFits responseFits
    (by decide +kernel) step (HasteBootsEarlyReceiptSmoke.past world).run first
  rcases split with seen | event
  · have unseen : CausalStreamExposure.seen (HasteBootsEarlyReceiptSmoke.past world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = false := by decide +kernel
    rw [unseen] at seen
    contradiction
  · exact event

-- An earlier field byte takes the other branch, without a Known receipt.
example : CausalStreamExposure.seen (HasteBootsFieldColumnSmoke.past world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true ∨
    NativeEarlyReceiptBound.event ctx.parent.profile step (HasteBootsFieldColumnSmoke.past world).run world :=
  NativeGoldBatchRecoveredCollector.first_column_cases ctx world work prepared parentFrames parent parentValid batchFits responseFits
    (by decide +kernel) step (HasteBootsFieldColumnSmoke.past world).run HasteBootsFieldColumnSmoke.first
example : CausalStreamExposure.seen (HasteBootsFieldColumnSmoke.past world).run.2 (NativeGoldBatchRandomLaw.phase work).pending.input = true := by decide +kernel

-- Structural receipt quotes still do not certify native receipt validity.
def fakeInput := NativeGoldBatchChallengeOrigin.input view.field root ctx.opening NativeGoldBatchColumns.label
  ctx.parameters.code.blocks ctx.parameters.queries (List.replicate 80 17)
example : (NativeGoldBatchChallengeLink.parse fakeInput).isSome = true := by decide +kernel
example : fakeInput ≠ columnInput := by decide +kernel

-- The state-only matrix definition responds to collected coefficients.
def changed : NativeFieldVector.State := {work.state with values := 1 :: work.state.values.drop 1}
example : NativeGoldBatchRecoveredMatrix.random ctx changed ⟨0,by decide +kernel⟩ (⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩) = 1 := by decide +kernel
example : NativeGoldBatchRecoveredMatrix.random ctx work.state ⟨0,by decide +kernel⟩ (⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩) = 0 := by decide +kernel
end
end HasteBootsRecoveredChallengeSmoke
