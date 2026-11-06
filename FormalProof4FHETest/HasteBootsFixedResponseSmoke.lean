module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchFalseClaimWitness
import all FormalProof4FHETest.HasteBootsRecoveredChallengeSmoke
import all FormalProof4FHETest.HasteBootsNativeWeightsSmoke
import all FormalProof4FHETest.HasteBootsNativeRectangularSmoke
open FormalProof4FHE.HasteBoots
open NativeGoldBatchFixedResponseData
open NativeFields (Goldilocks)
open OracleProgram (run)
namespace HasteBootsFixedResponseSmoke
noncomputable section
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
open HasteBootsBatchMeaningSmoke (usize root)

section Ordered
open HasteBootsNativeWeightsSmoke (first aliasedQuery reversed queries)
def parameters := {HasteBootsBatchMeaningSmoke.ctx.parameters with leftVariables := usize 2}
def zeroLane : Fin parameters.width.val := ⟨0,by decide +kernel⟩
example : left parameters first ⟨0,by decide +kernel⟩ zeroLane zeroLane = 1 := by decide +kernel
example : left parameters reversed ⟨0,by decide +kernel⟩ zeroLane zeroLane = 2 := by decide +kernel
example : left parameters aliasedQuery ⟨0,by decide +kernel⟩ zeroLane zeroLane = 1 := by decide +kernel
example : owner parameters queries 0 = 0 ∧ owner parameters queries 1 = 2 := by decide +kernel
example : groupLeft parameters queries 0 ⟨0,by decide +kernel⟩ zeroLane zeroLane = 1 := by decide +kernel
example : groupLeft parameters queries 1 ⟨0,by decide +kernel⟩ zeroLane zeroLane = 2 := by decide +kernel
end Ordered

section Parsed
open HasteBootsBatchOrderedSmoke (ctx world work prepared)
open HasteBootsEarlyReceiptSmoke (view)
theorem binding : NativeGoldBatchParsedResponseData.Binding ctx work view :=
  NativeGoldBatchParsedResponseData.binding_of_native ctx world work prepared HasteBootsFieldInputSmoke.parentFrames
    HasteBootsRecoveredChallengeSmoke.parent HasteBootsRecoveredChallengeSmoke.parentValid
    HasteBootsRecoveredChallengeSmoke.batchFits HasteBootsRecoveredChallengeSmoke.responseFits view HasteBootsFieldColumnSmoke.parsed
example (query : Fin work.binding.queries.val.length) :
    leftAt ctx.parameters view.field.data.queries query.val = NativeGoldBatchRectangularWeights.left ctx world work prepared query :=
  NativeGoldBatchParsedResponseData.left_native ctx world work view prepared binding query
example (query : Fin work.binding.queries.val.length) :
    rightAt ctx.parameters view.field.data.queries query.val = NativeGoldBatchRectangularData.right ctx world work prepared query :=
  NativeGoldBatchParsedResponseData.right_native ctx world work view prepared binding query
example (group : NativeGoldBatchRectangularData.Group ctx work) :
    (fun lane : Fin ctx.parameters.width.val => messages ctx.parameters view.column.opening group.val lane.val) = NativeGoldBatchRectangularData.messages ctx work group :=
  NativeGoldBatchParsedResponseData.messages_native ctx work view binding group
example : (fun lane : Fin ctx.parameters.width.val => testMessages ctx.parameters view.column.opening lane.val) = NativeGoldBatchRectangularData.testMessages ctx work :=
  NativeGoldBatchParsedResponseData.testMessages_native ctx work view binding
example : ctx.parameters.width.val = 3 ∧ ctx.parameters.code.blockWidth.val = 4 := by decide +kernel
end Parsed

namespace Witness
open HasteBootsNativeRectangularSmoke.Probability (ctx primitive constructed)
open HasteBootsBatchMeaningSmoke (world)
open HasteBootsNativeFinishingSmoke (completed? completed_spec choose parent? parent_spec)
local instance : NeZero ctx.parameters.code.blockWidth.val := ⟨by decide +kernel⟩
abbrev capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val :=
  (NativeGoldBlockCodeMeaning.constructor_dimensions ctx.tables (usize 2) (usize 4) (usize 2) ctx.parameters.code constructed).2.2.1
def table : Fin (2^ctx.parameters.leftVariables.val) → Fin ctx.parameters.code.messageLength.val → Fin ctx.parameters.width.val → Goldilocks :=
  fun left right lane => if left.val = 0 ∧ right.val = 0 ∧ lane.val = 0 then 1 else 0
def word : Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)) → NativeGoldBatchRectangularWeights.Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks :=
  fun symbol row => BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
    (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val) (fun right => table row.1 right row.2)) symbol
theorem extracted : RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity 0 word = table :=
  RectangularMatrixOpeningKernel.extract_encoded _ (by decide +kernel) capacity table
def result := (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.1
def packet := (completed? result).get (by decide +kernel)
def work := packet.1
def completion := packet.2
def next := (parent? completion.status).get (by decide +kernel)
theorem executed : (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.1 = .completed work completion := completed_spec _ _
theorem accepted : completion.status = .accepted next := parent_spec _ _
def history := (run (NativeGoldBatchPcsProgram.program ctx choose 6 ()) world).run.2
theorem nativeAccepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose 6 () work := by
  exact ⟨⟨HasteBootsFieldInputSmoke.parentFrames,by decide +kernel,HasteBootsRecoveredChallengeSmoke.parentValid,by decide +kernel⟩,
    completion,next,executed,accepted,List.Sublist.refl _⟩
def decodedOption := NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world)
theorem present : decodedOption.isSome = true := by decide +kernel
def decoded := decodedOption.get present
theorem parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded := (Option.some_get present).symm

theorem near : ∃ source, CommonSource.RowsIn (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) source ∧ hammingDist word source ≤ 0 := by
  refine ⟨word,?_,by simp⟩
  intro row
  exact BlockEncoder.encode_mem_code _ _

theorem falseSecond : (fun lane : Fin ctx.parameters.width.val => claimed decoded.field.data.values 1 lane.val) ≠
    matrixEvaluation (leftAt ctx.parameters decoded.field.data.queries 1) (rightAt ctx.parameters decoded.field.data.queries 1)
      (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity 0 word) := by
  rw [extracted]
  decide +kernel

example : ∃ group : ℕ, group < NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val decoded.field.data.queries ∧
    ∃ lane : Fin ctx.parameters.width.val, Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val : Set
        (Fin (2^(NativeGoldBlockCode.logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) - 0 ≤
      hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights
        (groupLeft ctx.parameters decoded.field.data.queries group) lane) word)
        (BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (messages ctx.parameters decoded.column.opening group lane.val))) := by
  apply NativeGoldBatchFalseClaimWitness.near_witness ctx world work ctx.tables (usize 2) (usize 4) (usize 2)
    constructed primitive history choose 6 () nativeAccepted (by decide +kernel) decoded parsed capacity 0 word near
  exact ⟨⟨1,by decide +kernel⟩,falseSecond⟩

-- The same original prefix group keeps both distinct finishing suffixes.
example : rightAt ctx.parameters decoded.field.data.queries 0 ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ = 0 := by decide +kernel
example : rightAt ctx.parameters decoded.field.data.queries 1 ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ ⟨0,by decide +kernel⟩ = 1 := by decide +kernel
end Witness
end
end HasteBootsFixedResponseSmoke
