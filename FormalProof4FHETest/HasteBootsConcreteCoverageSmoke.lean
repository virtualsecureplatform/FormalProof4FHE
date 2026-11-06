module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteExposureCoverage
import all FormalProof4FHETest.HasteBootsParsedDrawsSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (World)
open OracleProgram (run)
namespace HasteBootsConcreteCoverageSmoke
noncomputable section
open HasteBootsBatchMeaningSmoke (root usize)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
section Native
open HasteBootsBatchOrderedSmoke (ctx world work prepared)
open HasteBootsEarlyReceiptSmoke (step view columnInput)
open HasteBootsRecoveredChallengeSmoke (parent parentValid batchFits responseFits)
open HasteBootsFieldColumnSmoke (past first parsed)

theorem selected : NativeGoldBatchConcreteColumnExposure.select ctx step (past world).run = some view :=
  NativeGoldBatchConcreteExposureCoverage.selected_native ctx world work prepared HasteBootsFieldInputSmoke.parentFrames
    parent parentValid batchFits responseFits view parsed ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchOrderedSmoke.constructed step (past world).run first

-- No old field source: native preparation supplies the actual early receipt.
example : NativeEarlyReceiptBound.event ctx.parent.profile step (HasteBootsFreshReceiptSmoke.cleanPast world).run world := by
  have cleanFirst : CausalStreamExposure.firstRead step (HasteBootsFreshReceiptSmoke.cleanPast world).run = some columnInput := by decide +kernel
  obtain available | early := NativeGoldBatchConcreteExposureCoverage.source_or_early root ctx world work prepared
    HasteBootsFieldInputSmoke.parentFrames parent parentValid batchFits responseFits view parsed (by decide +kernel)
    step (HasteBootsFreshReceiptSmoke.cleanPast world).run cleanFirst
  · obtain ⟨sourceLog,found⟩ := available
    have absent : NativeGoldBatchFirstFieldSource.recover root (HasteBootsFreshReceiptSmoke.cleanPast world).run.2 view.field = none := rfl
    rw [absent] at found
    contradiction
  · exact early

-- A one-byte old field read fixes a source even without a complete receipt.
example : (∃ sourceLog, NativeGoldBatchFirstFieldSource.recover root (past world).run.2 view.field = some sourceLog) ∨
    NativeEarlyReceiptBound.event ctx.parent.profile step (past world).run world :=
  NativeGoldBatchConcreteExposureCoverage.source_or_early root ctx world work prepared
    HasteBootsFieldInputSmoke.parentFrames parent parentValid batchFits responseFits view parsed (by decide +kernel) step (past world).run first
end Native
section Accepted
open HasteBootsBatchMeaningSmoke (ctx world primitive)
open HasteBootsNativeFinishingSmoke (work choose)
open HasteBootsFirstFieldSourceSmoke (decoded columnHistory suffix history parsed recovered nativeAccepted truthful)
def step (_ : Unit) : OracleMachine.Command Unit Unit := .read (NativeGoldBatchColumnRequestLaw.input ctx work world) 999 1 (fun _ => ())
def packet : NativeIndexExposureRisk.Packet Unit Unit := (.inl (),columnHistory)
theorem first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world) := by decide +kernel
abbrev capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val := by decide +kernel

example (safe : ¬CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding root NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed root history))
    (falseClaim : ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover root packet.2 decoded.field = some sourceLog →
      ∃ query : NativeGoldBatchRectangularData.Query work,
        (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
          matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
            (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
            (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity 0
              (NativeGoldBatchConcreteColumnFamily.source root ctx decoded sourceLog))) :
    NativeEarlyReceiptBound.event ctx.parent.profile step packet world ∨
      ∃ sourceLog, NativeGoldBatchFirstFieldSource.recover root packet.2 decoded.field = some sourceLog ∧
        (NativeGoldBatchConcreteCoverage.Proximity root ctx primitive decoded sourceLog work.state 0 ∨
          NativeGoldBatchConcreteColumnExposure.event root ctx primitive ctx.parent.profile step packet 0 world) :=
  NativeGoldBatchConcreteExposureCoverage.accepted_first_column_cases root ctx world work ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchMeaningSmoke.constructed primitive choose 6 () step packet first suffix decoded parsed (by decide +kernel)
    nativeAccepted truthful safe capacity 0 (by decide +kernel) falseClaim
-- The full cover retains source disagreement as a charged alternative.
example    (falseClaim : ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover root packet.2 decoded.field = some sourceLog →
      ∃ query : NativeGoldBatchRectangularData.Query work,
        (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
          matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
            (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
            (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity 0
              (NativeGoldBatchConcreteColumnFamily.source root ctx decoded sourceLog))) :
    CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding root NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed root history) ∨
    NativeEarlyReceiptBound.event ctx.parent.profile step packet world ∨
      ∃ sourceLog, NativeGoldBatchFirstFieldSource.recover root packet.2 decoded.field = some sourceLog ∧
        (NativeGoldBatchConcreteCoverage.Proximity root ctx primitive decoded sourceLog work.state 0 ∨
          NativeGoldBatchConcreteColumnExposure.event root ctx primitive ctx.parent.profile step packet 0 world) :=
  NativeGoldBatchConcreteExposureCoverage.accepted_first_column_cover root ctx world work ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchMeaningSmoke.constructed primitive choose 6 () step packet first suffix decoded parsed (by decide +kernel)
    nativeAccepted truthful capacity 0 (by decide +kernel) falseClaim
end Accepted
end
end HasteBootsConcreteCoverageSmoke
