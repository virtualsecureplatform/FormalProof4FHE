module

public import FormalProof4FHE.HasteBoots.NativeGoldResponseMeaning
public import FormalProof4FHE.HasteBoots.RectangularMatrixResponse
@[expose] public section

/-! Native encoded response lanes have the padded messages used by rectangular
finishing. Raw lazy words are projected only after their original chunk address
is fixed. Missing coordinates totalize to zero; no input/output certificate is
added to the verifier. Native backend and Rust refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldResponseMessages
open NativeGoldRowEncoding (Code)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFields (Goldilocks)
noncomputable section

def message (code : Code) (input : List GoldWord) (lane : ℕ) : Fin code.messageLength → Goldilocks :=
  fun index => goldValue (input[lane*code.messageLength+index.val]?.getD 0)

theorem coefficients_chunk (code : Code) (m : ℕ) (input : List GoldWord) (lane : ℕ) :
    NativeGoldRowMeaning.coefficients code m ((input.drop (lane*code.messageLength)).take code.messageLength) =
      RowLayout.padded (m := m) (b := code.blockWidth) (message code input lane) := by
  funext block component
  unfold NativeGoldRowMeaning.coefficients RowLayout.padded message
  rw [RowLayout.address]
  by_cases present : block.val*code.blockWidth+component.val < code.messageLength
  · simp only [present,dite_true,List.getElem?_take,List.getElem?_drop,ite_true]
  · simp only [present,dite_false,List.getElem?_take,ite_false,Option.getD_none,goldValue,Fin.val_zero,Nat.cast_zero]

theorem lanes_padded (code : Code) (m width : ℕ) (input result : List GoldWord)
    (encoded : NativeGoldRowEncoding.encodeResponses code width input = some result)
    (enough : m ≤ 2^code.logSize) (padding : code.messageLength ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(code.logSize+1))) :
    ∀ lane : Fin width, NativeGoldResponseMeaning.laneWord code result lane.val =
      BlockEncoder.encode (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive)
        (RowLayout.padded (m := m) (b := code.blockWidth) (message code input lane.val)) := by
  intro lane
  have value := (NativeGoldResponseMeaning.encodeResponses_retained_lanes code m width input result encoded enough padding primitive lane.val lane.isLt).1
  rw [coefficients_chunk] at value
  exact value

theorem finish_encoded (code : Code) (m width : ℕ) (input result : List GoldWord)
    (encoded : NativeGoldRowEncoding.encodeResponses code width input = some result)
    (enough : m ≤ 2^code.logSize) (padding : code.messageLength ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(code.logSize+1)))
    (right : Fin code.messageLength → Matrix (Fin width) (Fin width) Goldilocks) :
    RectangularMatrixResponse.finishEncoded (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive) padding right
      (fun lane => NativeGoldResponseMeaning.laneWord code result lane.val) =
      RectangularMatrixResponse.finishMessage right (fun lane => message code input lane.val) := by
  have same := funext (lanes_padded code m width input result encoded enough padding primitive)
  rw [same]
  exact RectangularMatrixResponse.finishEncoded_padded _ (by simpa only [Fintype.card_fin] using enough) padding right _
end
end FormalProof4FHE.HasteBoots.NativeGoldResponseMessages
