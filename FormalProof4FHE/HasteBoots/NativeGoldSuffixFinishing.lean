module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsClaim
public import FormalProof4FHE.HasteBoots.NativeGoldResponseMessages
@[expose] public section

/-! Native suffix acceptance equals rectangular right-matrix finishing.
The low-bit-first fold order is retained. Encoder/message-size facts are
explicit here and are derived from actual batch preparation by the caller. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldSuffixFinishing
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeGoldRowEncoding (Code)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFields (Goldilocks)
open Matrix
noncomputable section

def suffix {C : Type} (parameters : Parameters C) (query : Query) :=
  (query.models.drop parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue parameters.width.val)

def right {C : Type} (parameters : Parameters C) (query : Query) := FlatMatrixFold.weights (suffix parameters query)

def messages {C : Type} (parameters : Parameters C) (query : Query) (response : List GoldWord) :
    Fin parameters.width.val → Fin (2^(suffix parameters query).length) → Goldilocks :=
  fun lane index => goldValue (response[lane.val*2^(parameters.numVariables.val-parameters.leftVariables.val)+index.val]?.getD 0)

theorem finish_message {C : Type} (parameters : Parameters C) (query : Query) (response : List GoldWord) :
    RectangularMatrixResponse.finishMessage (right parameters query) (messages parameters query response) =
      FlatMatrixFold.foldAll (suffix parameters query) (fun index lane => messages parameters query response lane index) :=
  FlatMatrixFold.finishMessage_eq_fold (suffix parameters query) (messages parameters query response)

theorem claim_message {C : Type} (parameters : Parameters C) (query : Query) (response : List GoldWord) (claimed : Row)
    (valid : NativeGoldMatrixWeights.QueryValid parameters.width.val query.models)
    (accepted : NativeGoldPcsClaim.verify parameters query response claimed = .ok ()) :
    claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishMessage (right parameters query) (messages parameters query response)) := by
  rw [finish_message]
  exact NativeGoldPcsClaim.accepted_value parameters query response claimed valid accepted

theorem suffix_length {C : Type} (parameters : Parameters C) (query : Query)
    (size : query.models.length = parameters.numVariables.val) :
    (suffix parameters query).length = parameters.numVariables.val-parameters.leftVariables.val := by
  simp only [suffix,List.length_map,List.length_drop,size]

/-- The right-query matrix domain is the original response message length,
not the padded code capacity or the code-symbol width. -/
def encodedRight {C : Type} (parameters : Parameters C) (query : Query) (code : Code)
    (size : query.models.length = parameters.numVariables.val)
    (shape : code.messageLength = 2^(parameters.numVariables.val-parameters.leftVariables.val)) :
    Fin code.messageLength → Matrix (Fin parameters.width.val) (Fin parameters.width.val) Goldilocks :=
  fun index => right parameters query (Fin.cast (shape.trans (congrArg (fun n => 2^n) (suffix_length parameters query size).symm)) index)

theorem transport_message {C : Type} (parameters : Parameters C) (query : Query) (code : Code) (response : List GoldWord)
    (size : query.models.length = parameters.numVariables.val)
    (shape : code.messageLength = 2^(parameters.numVariables.val-parameters.leftVariables.val)) :
    RectangularMatrixResponse.finishMessage (encodedRight parameters query code size shape)
      (fun lane => NativeGoldResponseMessages.message code response lane.val) =
      RectangularMatrixResponse.finishMessage (right parameters query) (messages parameters query response) := by
  let equal := shape.trans (congrArg (fun n => 2^n) (suffix_length parameters query size).symm)
  have same (index : Fin code.messageLength) :
      (fun lane : Fin parameters.width.val => NativeGoldResponseMessages.message code response lane.val index) =
      fun lane => messages parameters query response lane (Fin.cast equal index) := by
    funext lane
    simp only [NativeGoldResponseMessages.message,messages,shape,Fin.val_cast]
  unfold RectangularMatrixResponse.finishMessage
  simp only [same,encodedRight]
  exact (finCongr equal).sum_comp (fun index => right parameters query index *ᵥ (fun lane => messages parameters query response lane index))

/-- Successful native claim checking and actual response encoding supply the
analysis finishing equation, with independent packing and code widths. -/
theorem claim_encoded {C : Type} (parameters : Parameters C) (query : Query) (response encoded : List GoldWord) (claimed : Row)
    (valid : NativeGoldMatrixWeights.QueryValid parameters.width.val query.models)
    (accepted : NativeGoldPcsClaim.verify parameters query response claimed = .ok ())
    (code : Code) (m : ℕ) (computed : NativeGoldRowEncoding.encodeResponses code parameters.width.val response = some encoded)
    (enough : m ≤ 2^code.logSize) (padding : code.messageLength ≤ m*code.blockWidth)
    (primitive : IsPrimitiveRoot (goldValue code.domainRoot) (2^(code.logSize+1)))
    (size : query.models.length = parameters.numVariables.val)
    (shape : code.messageLength = 2^(parameters.numVariables.val-parameters.leftVariables.val)) :
    claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishEncoded
      (NTTButterfly.domain code.logSize (goldValue code.domainRoot) primitive) padding (encodedRight parameters query code size shape)
      (fun lane => NativeGoldResponseMeaning.laneWord code encoded lane.val)) := by
  rw [NativeGoldResponseMessages.finish_encoded code m parameters.width.val response encoded computed enough padding primitive,
    transport_message parameters query code response size shape]
  exact claim_message parameters query response claimed valid accepted
end
end FormalProof4FHE.HasteBoots.NativeGoldSuffixFinishing
