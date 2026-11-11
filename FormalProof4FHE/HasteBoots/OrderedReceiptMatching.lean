module
public import FormalProof4FHE.HasteBoots.LookupReceiptOrder
public import FormalProof4FHE.HasteBoots.EqualityReceiptOrder
public import FormalProof4FHE.HasteBoots.ReceiptDigestFixation
@[expose] public section

/-! Equal transcript inputs identify same-position retained receipt messages
once their earlier receipt counts agree. No independent digest equality is
supplied, and equality of byte offsets or rejected-value normalization is not
assumed. Original job segmentation remains a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.OrderedReceiptMatching
open InputIndexedOracle (World)
open ReceiptFrameView (frames frame)
noncomputable section

theorem suffix_equal {α : Type} (leftEarlier rightEarlier left right : List α)
    (sameLength : leftEarlier.length = rightEarlier.length) (same : leftEarlier ++ left = rightEarlier ++ right) : left = right := by
  have dropped := congrArg (List.drop leftEarlier.length) same
  rw [List.drop_left] at dropped
  rw [sameLength,List.drop_left] at dropped
  exact dropped

theorem selection {K : Type} (world other : World) (leftEarlier rightEarlier : List TranscriptFrame.Frame)
    (left right : NativeLookupChallenge.Machine K)
    (leftOrder : LookupReceiptOrder.Ordered world leftEarlier left) (rightOrder : LookupReceiptOrder.Ordered other rightEarlier right)
    (sameLength : leftEarlier.length = rightEarlier.length)
    (sameInput : (LookupReceiptLineage.current left).input = (LookupReceiptLineage.current right).input)
    (index : ℕ) (leftDraw rightDraw : NativeLookupChallenge.Draw K)
    (leftAt : left.draws[index]? = some leftDraw) (rightAt : right.draws[index]? = some rightDraw) :
    (NativeTranscript.receipt world leftDraw.coefficients.phase.consumed).run.1 =
      (NativeTranscript.receipt other rightDraw.coefficients.phase.consumed).run.1 := by
  have equal := suffix_equal leftEarlier rightEarlier _ _ sameLength
    (leftOrder.2.2.symm.trans ((congrArg frames sameInput).trans rightOrder.2.2))
  have atIndex := congrArg (fun values => values[index]?) equal
  simp only [List.getElem?_map,leftAt,rightAt,Option.map_some] at atIndex
  exact congrArg TranscriptFrame.Frame.message (Option.some.inj atIndex)

theorem equality {count : ℕ} {K : Type} (world other : World) (leftEarlier rightEarlier : List TranscriptFrame.Frame)
    (left right : NativeLookupEquality.Machine count K)
    (leftOrder : EqualityReceiptOrder.Ordered world leftEarlier left) (rightOrder : EqualityReceiptOrder.Ordered other rightEarlier right)
    (sameLength : leftEarlier.length = rightEarlier.length) (sameInput : left.transcript.input = right.transcript.input)
    (index : ℕ) (leftDraw rightDraw : NativeLookupEquality.Draw count K)
    (leftAt : left.draws[index]? = some leftDraw) (rightAt : right.draws[index]? = some rightDraw) :
    (NativeTranscript.receipt world leftDraw.coefficients.phase.consumed).run.1 =
      (NativeTranscript.receipt other rightDraw.coefficients.phase.consumed).run.1 := by
  have equal := suffix_equal leftEarlier rightEarlier _ _ sameLength
    (leftOrder.2.2.2.symm.trans ((congrArg frames sameInput).trans rightOrder.2.2.2))
  have atIndex := congrArg (fun values => values[index]?) equal
  simp only [List.getElem?_map,leftAt,rightAt,Option.map_some] at atIndex
  exact congrArg TranscriptFrame.Frame.message (Option.some.inj atIndex)

end
end FormalProof4FHE.HasteBoots.OrderedReceiptMatching
