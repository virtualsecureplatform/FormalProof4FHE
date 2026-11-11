module
import all FormalProof4FHE.HasteBoots.ScalarReceiptFrames
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ReceiptLineageSmoke
open HasteBootsSamplerAncestrySmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

/-- All ten native draws, including nine rejected offsets, keep their actual
receipt in the active transcript, rather than only the most recent receipt. -/
theorem rejected_receipts (draw : NativeLookupChallenge.Draw (ZMod 17)) (member : draw ∈ selection.draws) :
    NativeTranscriptExtension.Extends (NativeTranscript.finishField worldZero draw.coefficients.phase).run.1
      (LookupReceiptLineage.current selection) :=
  (LookupReceiptLineage.execute basis 1 4 10 [[0]] _ worldZero (by decide +kernel)
    (LookupReceiptLineage.initial 17 1 1 child worldZero)).2.2 draw member

/-- Later jobs do not erase receipts from the first completed request. -/
theorem batch_receipts (completed : NativeLookupBatch.Completed 17 (ZMod 17)) (member : completed ∈ batch.completed)
    (draw : NativeLookupChallenge.Draw (ZMod 17)) (drawn : draw ∈ completed.selection.draws) :
    NativeTranscriptExtension.Extends (NativeTranscript.finishField worldOne draw.coefficients.phase).run.1
      (LookupReceiptBatchLineage.current batch) :=
  (LookupReceiptBatchLineage.execute basis 1 30 _ worldOne (by decide +kernel)
    (LookupReceiptBatchLineage.initial actions child worldOne)).2.2 completed member draw drawn

/-- The first equality receipt survives the second completed point. -/
theorem equality_receipts (draw : NativeLookupEquality.Draw 2 (ZMod 17)) (member : draw ∈ equality.1.draws) :
    NativeTranscriptExtension.Extends (NativeTranscript.finishField worldOne draw.coefficients.phase).run.1 equality.1.transcript :=
  (EqualityReceiptLineage.request basis 1 2 10 child roots rootsFits worldOne (by decide +kernel)).2 draw member

example : (ReceiptFrameView.frames (LookupReceiptLineage.current selection).input).length = 10 := by
  unfold ReceiptFrameView.frames LookupReceiptLineage.current selection
  decide +kernel

example : (ReceiptFrameView.frames equality.1.transcript.input).length = 2 := by
  unfold ReceiptFrameView.frames equality
  decide +kernel

example : (ReceiptFrameView.frames (LookupReceiptBatchLineage.current batch).input).length = 4 := by
  unfold ReceiptFrameView.frames LookupReceiptBatchLineage.current batch
  decide +kernel

end
end FormalProof4FHE.HasteBoots.ReceiptLineageSmoke
