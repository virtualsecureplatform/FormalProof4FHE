module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchInteractiveSoundness
import all FormalProof4FHETest.HasteBootsBatchOrderedSmoke
import all FormalProof4FHETest.HasteBootsNativeFinishingSmoke
open FormalProof4FHE.HasteBoots
open NativeGoldBatchRectangularData (Group groupOf left right claimed)
open NativeGoldBatchRectangularWeights (Row source)
open NativeGoldBatchResponseMeaning (Domain)
open NativeFields (Goldilocks)
open OracleComp
namespace HasteBootsNativeRectangularSmoke
noncomputable section

section Ordered
open HasteBootsBatchOrderedSmoke (ctx world work prepared draw all_agree constructed)
open HasteBootsBatchMeaningSmoke (usize primitive)
example : Fintype.card (Group ctx work) = 1 ∧ work.binding.queries.val.length = 2 ∧ ctx.parameters.width.val = 3 ∧ ctx.parameters.code.blockWidth.val = 4 := by decide +kernel
example (group : Group ctx work) : groupOf ctx work (NativeGoldBatchRectangularData.owner ctx work group) = group :=
  NativeGoldBatchRectangularData.owner_group ctx work group
example : (List.ofFn draw).map Fin.val = [7,1,7] := by decide +kernel
example : RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive)
    (source ctx world work prepared (fun _ _ => 0)) (NativeGoldBatchRectangularChecks.random ctx world work prepared)
    (NativeGoldBatchRectangularData.testMessages ctx work) draw ∧
    ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
      (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test)
        (source ctx world work prepared (fun _ _ => 0)))
      (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (NativeGoldBatchRectangularData.messages ctx work test.1 test.2))) draw :=
  NativeGoldBatchRectangularChecks.checks ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2) constructed primitive
    (fun _ _ => 0) draw all_agree.1 all_agree.2
end Ordered

section Accepted
open HasteBootsBatchMeaningSmoke (ctx world)
open HasteBootsNativeFinishingSmoke (work completion choose executed parent accepted)
theorem acceptedPrepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work := (NativeGoldBatchPcsProgram.completed_origin ctx choose 6 () world work completion executed).prepared
example (query : NativeGoldBatchRectangularData.Query work) :
    claimed ctx work query = RectangularBatchOpeningKernel.finishMessage (groupOf ctx work) (right ctx world work acceptedPrepared)
      (NativeGoldBatchRectangularData.messages ctx work) query :=
  NativeGoldBatchRectangularData.accepted_claim ctx world work acceptedPrepared choose 6 () completion executed parent accepted query
end Accepted

namespace Probability
open HasteBootsBatchMeaningSmoke (world usize identity matrix prepared? prepared_get)
def first : NativeGoldPcsWire.Query := ⟨[(identity,identity),(matrix,matrix)],by decide⟩
def second : NativeGoldPcsWire.Query := ⟨[(identity,identity),(identity,identity)],by decide⟩
def ctx : NativeGoldBatchPcsProgram.Context := {HasteBootsBatchMeaningSmoke.ctx with queries := ⟨[first,second],by decide⟩}
def result := (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1
theorem present : (prepared? result).isSome = true := by decide +kernel
def work := (prepared? result).get present
theorem prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work := prepared_get result present
theorem constructed : NativeGoldBlockCode.build ctx.tables (usize 2) (usize 4) (usize 2) = .ok ctx.parameters.code := by decide +kernel
theorem primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)) := HasteBootsBatchMeaningSmoke.primitive
theorem log_value : NativeGoldBlockCode.logSize ctx.parameters.code = 5 := by decide +kernel
theorem blocks_value : ctx.parameters.code.messageBlocks.val = 1 := by decide +kernel
theorem width_value : ctx.parameters.width.val = 3 := by decide +kernel
theorem queries_value : ctx.parameters.queries.val = 1 := by decide +kernel
open NativeGoldBatchInteractiveSoundness (messages testMessages)
local instance : NeZero ctx.parameters.width.val := ⟨by decide +kernel⟩
local instance : NeZero ctx.parameters.code.blockWidth.val := ⟨by decide +kernel⟩
abbrev Position := Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code))
abbrev Coins := Fin ctx.parameters.width.val → Row ctx → Goldilocks
abbrev State := Coins × Fin 2
-- The adaptive response retains the full earlier matrix and a private coin.
def respond (matrix : Coins) : ProbComp State := do
  let coin ← $ᵗ (Fin 2)
  pure (matrix,coin)
def badOpening : NativeGoldBatchOpening.Opening :=
  {ctx.opening with evaluations := ⟨[⟨HasteBootsNativeFinishingSmoke.raw,by decide +kernel⟩],by decide⟩}
def opening (state : State) : NativeGoldBatchOpening.Opening :=
  if state.2.val = 0 ∨ state.1 0 (0,0) = 0 then ctx.opening else badOpening
example : NativeGoldPcsClaim.verify ctx.parameters (work.binding.queries.val.get ⟨0,by decide +kernel⟩)
    HasteBootsNativeFinishingSmoke.raw (HasteBootsBatchMeaningSmoke.zeros 3 (by decide)) = .ok () := by decide +kernel
-- The second original right query rejects the same shared raw response.
example : NativeGoldBatchPcsProgram.finish ctx.parameters work.binding badOpening = .error (.claim .claim) := by decide +kernel
example : NativeGoldBatchPcsProgram.finish ctx.parameters work.binding ctx.opening = .ok () := by decide +kernel

def table : Fin (2^ctx.parameters.leftVariables.val) → Fin (NativeGoldBlockCode.encoding ctx.parameters.code work.planRoot).messageLength → Fin ctx.parameters.width.val → Goldilocks :=
  fun left right lane => if left.val = 0 ∧ right.val = 0 ∧ lane.val = 0 then 1 else 0
def word : Position → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks :=
  fun symbol row => BlockEncoder.encode (Domain ctx primitive)
    (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (fun right => table row.1 right row.2)) symbol
abbrev capacity : (NativeGoldBlockCode.encoding ctx.parameters.code work.planRoot).messageLength ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val := (NativeGoldBlockCodeMeaning.constructor_dimensions ctx.tables (usize 2) (usize 4) (usize 2) ctx.parameters.code constructed).2.2.1

theorem extracted : RectangularMatrixOpeningKernel.extract (Domain ctx primitive) capacity 0 word = table :=
  RectangularMatrixOpeningKernel.extract_encoded (Domain ctx primitive) (by decide +kernel) capacity table
-- The false-query event is inhabited: the first right query is zero, while
-- the second original query should return a nonzero lane from this table.
example : claimed ctx work ⟨1,by decide +kernel⟩ ≠ matrixEvaluation
    (NativeGoldBatchRectangularWeights.left ctx world work prepared ⟨1,by decide +kernel⟩)
    (right ctx world work prepared ⟨1,by decide +kernel⟩)
    (RectangularMatrixOpeningKernel.extract (Domain ctx primitive) capacity 0 word) := by
  rw [extracted]
  decide +kernel

theorem distance : Code.minDist (BlockCode.code (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set (Position → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) = 32 := by
  simpa only [Fintype.card_fin,log_value,blocks_value,Nat.reducePow,Nat.reduceSub,Nat.reduceAdd] using BlockCode.minDist (Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val (by decide +kernel)

example : Pr{let pair ← RectangularOpeningKernel.experiment (F := Goldilocks) (Row := Row ctx) (Position := Position) ctx.parameters.width.val ctx.parameters.queries.val respond}[
    (∃ query : NativeGoldBatchRectangularData.Query work, claimed ctx work query ≠ matrixEvaluation
      (NativeGoldBatchRectangularWeights.left ctx world work prepared query) (right ctx world work prepared query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx primitive) capacity 0 word)) ∧
    NativeGoldBatchPcsProgram.finish ctx.parameters work.binding (opening pair.1.2) = .ok () ∧
    RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val) (Domain ctx primitive) word pair.1.1
      (testMessages ctx work (opening pair.1.2)) pair.2 ∧
    ∀ test : Group ctx work × Fin ctx.parameters.width.val, ColumnOpening.Agrees
      (StructuredOpening.combine (RectangularBatchOpeningKernel.weights (left ctx world work prepared) test) word)
      (BlockEncoder.encode (Domain ctx primitive) (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (messages ctx work (opening pair.1.2) test.1 test.2))) pair.2] ≤
    (32 / (Fintype.card Goldilocks : ENNReal))^3 + max (ColumnOpening.missBound Position 1 32) (ColumnOpening.missBound Position 1 1) := by
  classical
  let : Fintype (Submodule.span Goldilocks (Set.range (RectangularBaseProximity.stack word))) := Fintype.ofFinite _
  let : SampleableType (Submodule.span Goldilocks (Set.range (RectangularBaseProximity.stack word))) := SampleableType.ofFintype _
  let : Fintype (ModuleCodeProximity.toSpan (F := Goldilocks) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker := Fintype.ofFinite _
  let : SampleableType (ModuleCodeProximity.toSpan (F := Goldilocks) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker := SampleableType.ofFintype _
  have bound := NativeGoldBatchInteractiveSoundness.soundness_bound ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2)
    constructed primitive 0 word respond opening Fintype.card_pos (by rw [distance]; decide)
  simpa +instances only [distance,width_value,queries_value,Nat.cast_ofNat,Nat.sub_zero,Nat.reduceAdd] using bound
end Probability
end
end HasteBootsNativeRectangularSmoke
