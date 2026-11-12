module
public import FormalProof4FHE.HasteBoots.EqualityLookupReceiptView
@[expose] public section

/-! Earlier lookup endpoint receipts fix original raw compression/offset
words on receipt-completed fibers. Equality samples and later scalar inputs
are absent; named-payload and receipt-collision obligations stay explicit. -/
namespace FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation
open InputIndexedOracle (World)
open NativeGoldExtensionArithmetic (Word)
noncomputable section

inductive Side where
  | compression | offset
  deriving DecidableEq

def receiptAt (view : EqualityLookupReceiptView.View) (ordinal : ℕ) : Side → Option TranscriptFrame.Frame
  | .compression => (view.prelude.groups[ordinal]?).bind List.head?
  | .offset => (view.prelude.groups[ordinal]?).bind List.getLast?

structure Scalar where
  view : EqualityLookupReceiptView.View
  world : World
  ordinal : ℕ
  side : Side
  field : NativeFieldVector.State
  traced : FieldConsumedReplay.Traced NativeFields.goldilocksModulus field
  atReceipt : receiptAt view ordinal side = some (ReceiptFrameView.frame world field.phase)
  word : Word
  decoded : NativeGoldLookupProducer.decode field.values = some word

theorem receipt_equal (left right : Scalar) (input : left.view.input = right.view.input)
    (ordinal : left.ordinal = right.ordinal) (side : left.side = right.side) :
    (NativeTranscript.receipt left.world left.field.phase.consumed).run.1 =
      (NativeTranscript.receipt right.world right.field.phase.consumed).run.1 := by
  have groups := EqualityLookupReceiptView.compare left.view right.view input
  have same : receiptAt left.view left.ordinal left.side = receiptAt right.view right.ordinal right.side := by
    cases selected : left.side <;> simp only [receiptAt,selected,← side,← ordinal,groups]
  rw [left.atReceipt,right.atReceipt] at same
  exact congrArg TranscriptFrame.Frame.message (Option.some.inj same)

theorem coefficients {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (left right : Scalar)
    (input : left.view.input = right.view.input) (ordinal : left.ordinal = right.ordinal) (side : left.side = right.side)
    (leftNamed : left.field.phase.consumed ∈ ReceiptPayloadView.payloads (past left.world).run.2)
    (rightNamed : right.field.phase.consumed ∈ ReceiptPayloadView.payloads (past right.world).run.2)
    (fiber : (ReceiptCandidateCompletion.extend past right.world).run = (ReceiptCandidateCompletion.extend past left.world).run) :
    right.field.values = left.field.values ∨ ReceiptDigestFixation.Collision (past left.world).run.2 left.world :=
  ReceiptDigestFixation.coefficients_on_fiber replay left.world right.world NativeFields.goldilocksModulus
    (by decide +kernel) left.field right.field left.traced right.traced leftNamed rightNamed fiber
    (ReceiptDigestFixation.receipt_digest_equal _ _ _ _ (receipt_equal left right input ordinal side))

theorem scalar_on_fiber {A : Type} {past : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable past) (left right : Scalar)
    (input : left.view.input = right.view.input) (ordinal : left.ordinal = right.ordinal) (side : left.side = right.side)
    (leftNamed : left.field.phase.consumed ∈ ReceiptPayloadView.payloads (past left.world).run.2)
    (rightNamed : right.field.phase.consumed ∈ ReceiptPayloadView.payloads (past right.world).run.2)
    (fiber : (ReceiptCandidateCompletion.extend past right.world).run = (ReceiptCandidateCompletion.extend past left.world).run) :
    right.word = left.word ∨ ReceiptDigestFixation.Collision (past left.world).run.2 left.world := by
  rcases coefficients replay left right input ordinal side leftNamed rightNamed fiber with same | collision
  · exact Or.inl (Option.some.inj (right.decoded.symm.trans ((congrArg NativeGoldLookupProducer.decode same).trans left.decoded)))
  · exact Or.inr collision

end
end FormalProof4FHE.HasteBoots.EqualityLookupFactorFixation
