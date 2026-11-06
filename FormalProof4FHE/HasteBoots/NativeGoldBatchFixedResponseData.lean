module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedChecks
@[expose] public section

/-! Raw response messages and ordered query weights are functions of fixed
parameters and original serialized data. Total indexing is analysis only;
matching native projections below uses their original validated bounds.
No oracle world, Prepared work or scheduler is an argument to these data. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFixedResponseData
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativePrefixCodec (Vector)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def queryAt (queries : Vector NativeGoldPcsWire.Query) (index : ℕ) : NativeGoldPcsWire.Query :=
  (queries.val[index]?).getD ⟨[],by decide⟩

def left (parameters : Parameters Stored) (query : NativeGoldPcsWire.Query)
    (cell : Fin (2^parameters.leftVariables.val)) : Matrix (Fin parameters.width.val) (Fin parameters.width.val) Goldilocks :=
  let pairs := (query.models.take parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue parameters.width.val)
  FlatMatrixFold.weights pairs (Fin.ofNat (2^pairs.length) cell.val)

def leftAt (parameters : Parameters Stored) (queries : Vector NativeGoldPcsWire.Query) (index : ℕ) :=
  left parameters (queryAt queries index)

def owner (parameters : Parameters Stored) (queries : Vector NativeGoldPcsWire.Query) (group : ℕ) : ℕ :=
  if bounded : group < NativeGoldQueryGroups.groupCount parameters.leftVariables.val queries then
    (NativeGoldQueryGroups.representative parameters.leftVariables.val queries ⟨group,bounded⟩).val
  else 0

def groupLeft (parameters : Parameters Stored) (queries : Vector NativeGoldPcsWire.Query) (group : ℕ) :=
  leftAt parameters queries (owner parameters queries group)

def right (parameters : Parameters Stored) (query : NativeGoldPcsWire.Query)
    (index : Fin parameters.code.messageLength.val) : Matrix (Fin parameters.width.val) (Fin parameters.width.val) Goldilocks :=
  NativeGoldSuffixFinishing.right parameters query
    (Fin.ofNat (2^(NativeGoldSuffixFinishing.suffix parameters query).length) index.val)

def rightAt (parameters : Parameters Stored) (queries : Vector NativeGoldPcsWire.Query) (index : ℕ) :=
  right parameters (queryAt queries index)

def message (parameters : Parameters Stored) (input : List GoldWord) (lane : ℕ)
    (index : Fin parameters.code.messageLength.val) : Goldilocks :=
  goldValue (input[lane*parameters.code.messageLength.val+index.val]?.getD 0)

def messages (parameters : Parameters Stored) (opening : NativeGoldBatchOpening.Opening) (group lane : ℕ) :=
  message parameters (((opening.evaluations.val[group]?).map (fun row => row.val)).getD []) lane

def testMessages (parameters : Parameters Stored) (opening : NativeGoldBatchOpening.Opening) (lane : ℕ) :=
  message parameters opening.test.val lane

def claimed (values : Vector NativeLookupRequestWire.Row) (query lane : ℕ) : Goldilocks :=
  goldValue ((((values.val[query]?).map (fun row => row.val)).getD [])[lane]?.getD 0)

theorem queryAt_get (queries : Vector NativeGoldPcsWire.Query) (index : Fin queries.val.length) :
    queryAt queries index.val = queries.val.get index := by
  simp only [queryAt,List.getElem?_eq_getElem index.isLt,Option.getD_some,List.get_eq_getElem]

theorem left_native (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (query : Fin work.binding.queries.val.length) :
    leftAt ctx.parameters work.binding.queries query.val = NativeGoldBatchRectangularWeights.left ctx world work prepared query := by
  rw [leftAt,queryAt_get]
  unfold left NativeGoldBatchRectangularWeights.left
  funext cell
  apply congrArg (FlatMatrixFold.weights _)
  apply Fin.ext
  simp only [Fin.val_ofNat,Fin.val_cast]
  rw [NativeGoldBatchRectangularWeights.prefix_length ctx world work prepared query]
  exact Nat.mod_eq_of_lt cell.isLt

theorem groupLeft_native (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (group : NativeGoldBatchRectangularData.Group ctx work) :
    groupLeft ctx.parameters work.binding.queries group.val = NativeGoldBatchRectangularData.left ctx world work prepared group := by
  unfold groupLeft owner
  rw [dite_eq_left group.isLt]
  exact left_native ctx world work prepared _

theorem right_native (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (query : Fin work.binding.queries.val.length) :
    rightAt ctx.parameters work.binding.queries query.val = NativeGoldBatchRectangularData.right ctx world work prepared query := by
  rw [rightAt,queryAt_get]
  unfold right NativeGoldBatchRectangularData.right NativeGoldSuffixFinishing.encodedRight
  funext index
  apply congrArg (NativeGoldSuffixFinishing.right _ _)
  apply Fin.ext
  simp only [Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  have length := NativeGoldSuffixFinishing.suffix_length ctx.parameters (work.binding.queries.val.get query)
    (NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work prepared query)
  have size := NativeGoldBatchFinishingMeaning.prepared_message_length ctx world work prepared
  simpa only [length,← size] using index.isLt

theorem messages_native (ctx : Context) (work : Prepared)
    (group : NativeGoldBatchRectangularData.Group ctx work) :
    (fun lane : Fin ctx.parameters.width.val => messages ctx.parameters ctx.opening group.val lane.val) =
      NativeGoldBatchRectangularData.messages ctx work group := rfl

theorem testMessages_native (ctx : Context) (work : Prepared) :
    (fun lane : Fin ctx.parameters.width.val => testMessages ctx.parameters ctx.opening lane.val) =
      NativeGoldBatchRectangularData.testMessages ctx work := rfl

theorem claimed_native (ctx : Context) (work : Prepared) (query : Fin work.binding.queries.val.length) :
    (fun lane : Fin ctx.parameters.width.val => claimed work.binding.values query.val lane.val) =
      NativeGoldBatchRectangularData.claimed ctx work query := rfl
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFixedResponseData
