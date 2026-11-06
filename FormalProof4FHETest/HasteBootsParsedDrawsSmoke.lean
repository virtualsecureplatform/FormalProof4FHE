module
import all FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteAcceptedChecks
import all FormalProof4FHETest.HasteBootsConcreteColumnSmoke
open FormalProof4FHE.HasteBoots
namespace HasteBootsParsedDrawsSmoke
noncomputable section
open HasteBootsBatchOrderedSmoke (ctx work world prepared)
open HasteBootsEarlyReceiptSmoke (view)
open HasteBootsRecoveredChallengeSmoke (parent parentValid batchFits responseFits)
open HasteBootsBatchMeaningSmoke (usize)

theorem sampled : ∃ draw,
    NativeIndexFirstReadLaw.values (NativeGoldBlockCode.logSize ctx.parameters.code)
      (view.column.index.request ctx.parent.profile).transcript view.column.index.label
      view.column.index.domain view.column.index.count world = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws :=
  NativeGoldBatchParsedDraws.draws ctx world work prepared ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchOrderedSmoke.constructed HasteBootsFieldInputSmoke.parentFrames parent parentValid batchFits responseFits
    view HasteBootsFieldColumnSmoke.parsed

-- Three original draws survive unchanged even though deduplication leaves two jobs.
example : ∃ draw,
    NativeIndexFirstReadLaw.values (NativeGoldBlockCode.logSize ctx.parameters.code)
      (view.column.index.request ctx.parent.profile).transcript view.column.index.label
      view.column.index.domain view.column.index.count world = some draw ∧
      (List.ofFn draw).map Fin.val = [7,1,7] := by
  obtain ⟨draw,values,ordered⟩ := sampled
  exact ⟨draw,values,ordered.trans (by decide +kernel)⟩
example : work.sample.indices.length = 2 := by decide +kernel
section Accepted
open HasteBootsBatchMeaningSmoke (root)
open HasteBootsFirstFieldSourceSmoke (decoded columnHistory suffix history parsed recovered nativeAccepted truthful)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq
example (safe : ¬CheckpointAvailability.Disagreement NativeGoldColumnAuthentication.encoding root NativeMerkleShapeFamily.shape
    (NativeGoldBatchFamilyAvailability.reconstructed root history)) :
    ∃ draw, NativeIndexFirstReadLaw.values (NativeGoldBlockCode.logSize HasteBootsBatchMeaningSmoke.ctx.parameters.code)
      (decoded.column.index.request HasteBootsBatchMeaningSmoke.ctx.parent.profile).transcript decoded.column.index.label
      decoded.column.index.domain decoded.column.index.count HasteBootsBatchMeaningSmoke.world = some draw ∧
      (List.ofFn draw).map Fin.val = HasteBootsNativeFinishingSmoke.work.sample.draws ∧
      ∀ test : NativeGoldBatchConcreteColumnFamily.Test HasteBootsBatchMeaningSmoke.ctx decoded, ColumnOpening.Agrees
        (NativeGoldBatchConcreteColumnFamily.raw root HasteBootsBatchMeaningSmoke.ctx decoded [] HasteBootsNativeFinishingSmoke.work.state test)
        (NativeGoldBatchConcreteColumnFamily.claim HasteBootsBatchMeaningSmoke.ctx HasteBootsBatchMeaningSmoke.primitive decoded HasteBootsNativeFinishingSmoke.work.state test) draw :=
  NativeGoldBatchConcreteAcceptedChecks.accepted_checks root HasteBootsBatchMeaningSmoke.ctx HasteBootsBatchMeaningSmoke.world
    HasteBootsNativeFinishingSmoke.work HasteBootsBatchMeaningSmoke.ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchMeaningSmoke.constructed HasteBootsBatchMeaningSmoke.primitive HasteBootsNativeFinishingSmoke.choose 6 ()
    columnHistory suffix decoded parsed (by decide +kernel) [] recovered nativeAccepted truthful safe
end Accepted
end
end HasteBootsParsedDrawsSmoke
