module
public import FormalProof4FHE.HasteBoots.IndexedScalarReceiptPosition
@[expose] public section

/-! Original-position field samples fix raw lookup words and raw EQ point
lists on refined replay fibers, modulo the explicit SHAKE receipt collision.
Receipt bindings and coefficient traces are carried by actual sample packages. -/
namespace FormalProof4FHE.HasteBoots.LookupFactorFixation
open InputIndexedOracle (World)
open NativeGoldExtensionArithmetic (Word)
noncomputable section

structure Sample where
  view : ScalarReceiptSegmentation.View
  position : ScalarReceiptMatching.Position
  state : NativeFieldVector.State
  traced : FieldConsumedReplay.Traced NativeFields.goldilocksModulus state
  atReceipt : ScalarReceiptMatching.receiptAt view position = some (ReceiptFrameView.frame view.reader.world state.phase)

structure Scalar extends Sample where
  word : Word
  decoded : NativeGoldLookupProducer.decode state.values = some word

structure Point extends Sample where
  count : ℕ
  point : List Word
  complete : state.values.length = count * 3
  evidence : NativeGoldLookupEquality.PointEvidence count state.values point

theorem coefficients {A : Type} {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past)
    (left right : Sample)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (leftNamed : left.state.phase.consumed ∈ ReceiptPayloadView.payloads (past left.view.reader.world).run.2)
    (rightNamed : right.state.phase.consumed ∈ ReceiptPayloadView.payloads (past right.view.reader.world).run.2)
    (fiber : (ReceiptCandidateCompletion.extend past right.view.reader.world).run = (ReceiptCandidateCompletion.extend past left.view.reader.world).run) :
    right.state.values = left.state.values ∨ ReceiptDigestFixation.Collision (past left.view.reader.world).run.2 left.view.reader.world := by
  apply ScalarReceiptMatching.coefficients_on_fiber replay left.view right.view sameInput left.position NativeFields.goldilocksModulus
    (by decide +kernel) left.state right.state left.traced right.traced left.atReceipt _ leftNamed rightNamed fiber
  rw [samePosition]
  exact right.atReceipt

theorem scalar_on_fiber {A : Type} {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past)
    (left right : Scalar)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (leftNamed : left.state.phase.consumed ∈ ReceiptPayloadView.payloads (past left.view.reader.world).run.2)
    (rightNamed : right.state.phase.consumed ∈ ReceiptPayloadView.payloads (past right.view.reader.world).run.2)
    (fiber : (ReceiptCandidateCompletion.extend past right.view.reader.world).run = (ReceiptCandidateCompletion.extend past left.view.reader.world).run) :
    right.word = left.word ∨ ReceiptDigestFixation.Collision (past left.view.reader.world).run.2 left.view.reader.world := by
  rcases coefficients replay left.toSample right.toSample sameInput samePosition leftNamed rightNamed fiber with equal | bad
  · exact Or.inl (Option.some.inj (right.decoded.symm.trans ((congrArg NativeGoldLookupProducer.decode equal).trans left.decoded)))
  · exact Or.inr bad

theorem point_on_fiber {A : Type} {past : World → NativeTranscript.Execution A} (replay : ObservationReplay.Replayable past)
    (left right : Point)
    (sameInput : left.view.reader.entry.coefficients.phase.pending.input = right.view.reader.entry.coefficients.phase.pending.input)
    (samePosition : left.position = right.position)
    (leftNamed : left.state.phase.consumed ∈ ReceiptPayloadView.payloads (past left.view.reader.world).run.2)
    (rightNamed : right.state.phase.consumed ∈ ReceiptPayloadView.payloads (past right.view.reader.world).run.2)
    (fiber : (ReceiptCandidateCompletion.extend past right.view.reader.world).run = (ReceiptCandidateCompletion.extend past left.view.reader.world).run) :
    right.point = left.point ∨ ReceiptDigestFixation.Collision (past left.view.reader.world).run.2 left.view.reader.world := by
  rcases coefficients replay left.toSample right.toSample sameInput samePosition leftNamed rightNamed fiber with equal | bad
  · apply Or.inl
    have counts := congrArg List.length equal
    rw [right.complete,left.complete] at counts
    have countEqual : right.count = left.count := by omega
    have lengthEqual : right.point.length = left.point.length := by rw [right.evidence.length,left.evidence.length,countEqual]
    apply List.ext_getElem lengthEqual
    intro index rightBound leftBound
    funext coordinate
    apply Fin.ext
    have rightValue := (right.evidence.coefficients index rightBound coordinate).1
    have leftValue := (left.evidence.coefficients index leftBound coordinate).1
    exact rightValue.trans ((congrArg (fun values : List ℕ => (values[coordinate.val+3*index]?).getD 0) equal).trans leftValue.symm)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.LookupFactorFixation
