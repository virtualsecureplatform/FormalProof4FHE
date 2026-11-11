module
import all FormalProof4FHE.HasteBoots.CalibratedJointWorkBound
import all FormalProof4FHETest.HasteBootsFieldColumnSmoke

namespace HasteBootsAdaptiveColumnWorkSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
open HasteBootsEarlyReceiptSmoke (columnInput view)
open HasteBootsBatchOrderedSmoke (world)
open HasteBootsBatchMeaningSmoke (root)
noncomputable section

-- The context is recovered from the linked field prefix in the complete
-- column input; correctness of the quoted receipt is not a premise.
theorem named_context : view.field.data.context ∈ ContextDigestTargets.fromInput columnInput :=
  BatchColumnContextName.context _ _ HasteBootsFieldColumnSmoke.parsed

theorem complete_frames : TranscriptFrame.decodeAll columnInput = some view.column.index.frames ∧
    view.fieldFrames = view.field.frames :=
  BatchColumnContextName.frames _ _ HasteBootsFieldColumnSmoke.parsed

def farRead : Program Unit := .read columnInput 999 1 (fun _ => .pure ())
def nearRead : Program Unit := .read columnInput 0 1 (fun _ => .pure ())

-- The pending input at an adversarial far-offset first read selects the
-- same complete linked column view as the native parser.
theorem far_selected : BatchColumnParameterCandidate.select (runPrefix 0 farRead world).run = some view := by
  have first : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix 0 farRead world).run = some columnInput := rfl
  simp only [BatchColumnParameterCandidate.select,first,Option.bind_some,HasteBootsFieldColumnSmoke.parsed]

-- Receipt exposure depends on the selected input and past, including when
-- the first positive read is far beyond its initial seed window.
theorem receipt_offset :
    NativeEarlyReceiptBound.event root OracleProgramMachine.step (runPrefix 0 farRead world).run world ↔
    NativeEarlyReceiptBound.event root OracleProgramMachine.step (runPrefix 0 nearRead world).run world :=
  ProgramEarlyReceiptContinuation.event_congr _ _ _ _
    (ProgramEarlyReceiptContinuation.select_congr _ _ _ _ rfl rfl) root world

-- Completed packets create neither a column charge nor an early receipt.
theorem completed_column (history : List NativeTranscript.Observation) :
    AdaptiveBatchColumnKernel.score (((.inr ()) : Program Unit ⊕ Unit),history) = 0 := rfl

theorem completed_receipt (history : List NativeTranscript.Observation) :
    ¬NativeEarlyReceiptBound.event root OracleProgramMachine.step (((.inr ()) : Program Unit ⊕ Unit),history) world :=
  ProgramEarlyReceiptContinuation.absent _ _ rfl root world

end
end HasteBootsAdaptiveColumnWorkSmoke
