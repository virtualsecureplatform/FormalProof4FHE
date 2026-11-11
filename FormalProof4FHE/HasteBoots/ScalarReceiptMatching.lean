module
public import FormalProof4FHE.HasteBoots.ScalarReceiptSegmentation
public import FormalProof4FHE.HasteBoots.ReceiptDigestFixation
@[expose] public section

/-! Outer scalar inputs fix original-position receipt messages. Compression
and accepted-offset positions use the first/last frame of the recovered job,
so no equal rejection count is supplied. Named-key fixation retains its
explicit refined-history and SHAKE receipt-collision obligations. -/
namespace FormalProof4FHE.HasteBoots.ScalarReceiptMatching
open ScalarReceiptSegmentation (View)
open InputIndexedOracle (World)
open NativeTranscript (FieldPhase)
noncomputable section

inductive Position where
  | compression (job : ℕ)
  | offset (job : ℕ)
  | draw (job index : ℕ)
  | equalityPoint (index : ℕ)

def receiptAt (view : View) : Position → Option TranscriptFrame.Frame
  | .compression job => (view.prelude.groups[job]?).bind List.head?
  | .offset job => (view.prelude.groups[job]?).bind List.getLast?
  | .draw job index => (view.prelude.groups[job]?).bind (fun entries => entries[index]?)
  | .equalityPoint index => view.prelude.equality[index]?

theorem at_equal (left right : View)
    (same : left.reader.entry.coefficients.phase.pending.input = right.reader.entry.coefficients.phase.pending.input)
    (position : Position) : receiptAt left position = receiptAt right position := by
  have ordered := ScalarReceiptSegmentation.compare left right same
  cases position <;> simp only [receiptAt,ordered.1,ordered.2]

theorem message_equal (left right : View)
    (same : left.reader.entry.coefficients.phase.pending.input = right.reader.entry.coefficients.phase.pending.input)
    (position : Position) (leftPhase rightPhase : FieldPhase)
    (leftAt : receiptAt left position = some (ReceiptFrameView.frame left.reader.world leftPhase))
    (rightAt : receiptAt right position = some (ReceiptFrameView.frame right.reader.world rightPhase)) :
    (NativeTranscript.receipt left.reader.world leftPhase.consumed).run.1 =
      (NativeTranscript.receipt right.reader.world rightPhase.consumed).run.1 := by
  have equal := at_equal left right same position
  rw [leftAt,rightAt] at equal
  exact congrArg TranscriptFrame.Frame.message (Option.some.inj equal)

theorem coefficients_on_fiber {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (left right : View)
    (same : left.reader.entry.coefficients.phase.pending.input = right.reader.entry.coefficients.phase.pending.input)
    (position : Position) (p : ℕ) (positive : 0 < CanonicalByteSampler.byteCount p)
    (leftState rightState : NativeFieldVector.State)
    (leftTrace : FieldConsumedReplay.Traced p leftState) (rightTrace : FieldConsumedReplay.Traced p rightState)
    (leftAt : receiptAt left position = some (ReceiptFrameView.frame left.reader.world leftState.phase))
    (rightAt : receiptAt right position = some (ReceiptFrameView.frame right.reader.world rightState.phase))
    (leftNamed : leftState.phase.consumed ∈ ReceiptPayloadView.payloads (past left.reader.world).run.2)
    (rightNamed : rightState.phase.consumed ∈ ReceiptPayloadView.payloads (past right.reader.world).run.2)
    (fiber : (ReceiptCandidateCompletion.extend past right.reader.world).run = (ReceiptCandidateCompletion.extend past left.reader.world).run) :
    rightState.values = leftState.values ∨ ReceiptDigestFixation.Collision (past left.reader.world).run.2 left.reader.world :=
  ReceiptDigestFixation.coefficients_on_fiber replay left.reader.world right.reader.world p positive leftState rightState
    leftTrace rightTrace leftNamed rightNamed fiber
    (ReceiptDigestFixation.receipt_digest_equal _ _ _ _ (message_equal left right same position _ _ leftAt rightAt))

end
end FormalProof4FHE.HasteBoots.ScalarReceiptMatching
