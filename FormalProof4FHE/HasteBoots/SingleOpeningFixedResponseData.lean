module
public import FormalProof4FHE.HasteBoots.SingleOpeningSelectedWord
@[expose] public section

/-! Query weights and response messages from original raw single-opening
data and fixed parameters. Total indexing defines analysis values; native
validated dimensions below identify them with actual prepared projections. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFixedResponseData
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativeFieldRepresentation (goldValue)
open NativeFields (Goldilocks)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def left (parameters : Parameters Stored) (query : NativeGoldPcsWire.Query)
    (cell : Fin (2^parameters.leftVariables.val)) : Matrix (Fin parameters.width.val) (Fin parameters.width.val) Goldilocks :=
  let pairs := (query.models.take parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue parameters.width.val)
  FlatMatrixFold.weights pairs (Fin.ofNat (2^pairs.length) cell.val)

def right (parameters : Parameters Stored) (query : NativeGoldPcsWire.Query)
    (index : Fin parameters.code.messageLength.val) : Matrix (Fin parameters.width.val) (Fin parameters.width.val) Goldilocks :=
  NativeGoldSuffixFinishing.right parameters query
    (Fin.ofNat (2^(NativeGoldSuffixFinishing.suffix parameters query).length) index.val)

def messages (ctx : Context) (opening : NativeGoldPcsOpening.Opening) := SingleOpeningRectangularData.messages ctx opening.evaluation.val

def testMessages (ctx : Context) (opening : NativeGoldPcsOpening.Opening) := SingleOpeningRectangularData.messages ctx opening.test.val

def claimed (ctx : Context) (value : NativeLookupRequestWire.Row) (lane : Fin ctx.parameters.width.val) :=
  goldValue (value.val[lane.val]?.getD 0)

theorem left_native (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    left ctx.parameters ctx.query = SingleOpeningRectangularData.left ctx world work prepared := by
  unfold left SingleOpeningRectangularData.left
  funext cell
  apply congrArg (FlatMatrixFold.weights _)
  apply Fin.ext
  simp only [Fin.val_ofNat,Fin.val_cast]
  rw [SingleOpeningRectangularData.prefix_length ctx world work prepared]
  exact Nat.mod_eq_of_lt cell.isLt

theorem right_native (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    right ctx.parameters ctx.query = SingleOpeningRectangularData.right ctx world work prepared := by
  unfold right SingleOpeningRectangularData.right
  funext index
  apply congrArg (NativeGoldSuffixFinishing.right _ _)
  apply Fin.ext
  simp only [Fin.val_ofNat,Fin.val_cast]
  apply Nat.mod_eq_of_lt
  have length := NativeGoldSuffixFinishing.suffix_length ctx.parameters ctx.query
    (SingleOpeningRectangularData.query_length ctx world work prepared)
  have size := SingleOpeningRectangularData.message_length ctx world work prepared
  simpa only [length,← size] using index.isLt

theorem messages_native (ctx : Context) : messages ctx ctx.opening = SingleOpeningRectangularData.messages ctx ctx.opening.evaluation.val := rfl

theorem testMessages_native (ctx : Context) : testMessages ctx ctx.opening = SingleOpeningRectangularData.messages ctx ctx.opening.test.val := rfl

theorem claimed_native (ctx : Context) : claimed ctx ctx.claimed = SingleOpeningRectangularData.claimed ctx := rfl

end
end FormalProof4FHE.HasteBoots.SingleOpeningFixedResponseData
