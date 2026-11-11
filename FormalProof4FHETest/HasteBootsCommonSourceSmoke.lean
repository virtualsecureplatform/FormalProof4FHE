module
import all FormalProof4FHE.HasteBoots.GoldCommonSourceBinding
import all FormalProof4FHETest.HasteBootsRecoveredChallengeSmoke
import all FormalProof4FHETest.HasteBootsBatchMeaningSmoke
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke

namespace FormalProof4FHE.HasteBoots.CommonSourceSmoke
open HasteBootsBatchMeaningSmoke (ctx world work prepared primitive root)
open NativeRootFamilySourceSelection (Log)
noncomputable section

theorem capacity : GoldCommonSourceTable.Capacity ctx.parameters := by decide +kernel

/-- Original queries can differ and share a response group; neither selects
its own source table. -/
example : work.binding.queries.val[0]? ≠ work.binding.queries.val[1]? ∧
    NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨0,by decide +kernel⟩ =
      NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries ⟨1,by decide +kernel⟩ := by decide +kernel

/-- Different response/nonce records preserve the entire actual batch cube
when their source binding and exact old log agree. -/
example (first second : NativeGoldBatchChallengeLink.View) (sourceLog : Log) (radius : ℕ)
    (context : first.field.data.context = second.field.data.context)
    (sameRoot : first.field.data.root = second.field.data.root) :
    BatchOpeningNativeObligation.source root ctx primitive capacity world work prepared first radius sourceLog =
      BatchOpeningNativeObligation.source root ctx primitive capacity world work prepared second radius sourceLog :=
  eq_of_heq (GoldCommonSourceTable.batches_same root ctx ctx primitive primitive capacity capacity world work work
    prepared prepared first second rfl context sameRoot sourceLog radius)

/-- The fixture's actual prepared split is sufficient to expose the common
parameter-indexed table, without an extra geometry certificate. -/
example (view : NativeGoldBatchChallengeLink.View) (sourceLog : Log) (radius : ℕ) :
    BatchOpeningNativeObligation.source root ctx primitive capacity world work prepared view radius sourceLog =
      GoldCommonSourceTable.table ctx.parameters primitive capacity root view.field.data.context view.field.data.root sourceLog radius
        (BatchOpeningNativeObligation.dimensions ctx world work prepared) :=
  GoldCommonSourceTable.batch_cube root ctx primitive capacity world work prepared view sourceLog radius

/-- Source addresses use independent packing and code widths, here 3 and 4. -/
example (sourceLog : Log) : GoldCommonSourceTable.word ctx.parameters root root root sourceLog
      ⟨0,by decide⟩ (⟨1,by decide⟩,⟨2,by decide⟩) ⟨3,by decide⟩ =
    NativeGoldBatchSelectedWord.values root root root ctx.parameters.code sourceLog 0 23 := rfl

/-- Equal stored code does not erase the full context's different quota. -/
example : SingleSelectedSmoke.ctx.parameters.code = ctx.parameters.code ∧
    SingleSelectedSmoke.ctx.parameters ≠ ctx.parameters := by
  refine ⟨rfl,?_⟩
  intro same
  have quota := congrArg (fun p : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored => p.queries.val) same
  change 3 = 1 at quota
  contradiction

/-- The original single protocol uses the same parameter-indexed construction;
its retained query quota differs from the batch fixture's quota. -/
example (origin : CacheBackedSingleOpening.Origin SingleSelectedSmoke.ctx)
    (view : SingleOpeningChallengeLink.View) (sourceLog : Log) (radius : ℕ) :
    SingleOpeningNativeObligation.source root SingleSelectedSmoke.ctx origin SingleSelectedSmoke.world
        SingleSelectedSmoke.work SingleSelectedSmoke.prepared view sourceLog radius =
      GoldCommonSourceTable.table SingleSelectedSmoke.ctx.parameters origin.primitive origin.capacity root
        view.field.data.context view.field.data.root sourceLog radius
        (SingleOpeningExtractedTableMeaning.prepared_dimensions SingleSelectedSmoke.ctx SingleSelectedSmoke.world
          SingleSelectedSmoke.work SingleSelectedSmoke.prepared) :=
  GoldCommonSourceTable.single_cube root SingleSelectedSmoke.ctx origin SingleSelectedSmoke.world
    SingleSelectedSmoke.work SingleSelectedSmoke.prepared view sourceLog radius

section Parsed
open HasteBootsRecoveredChallengeSmoke (parent parentValid batchFits responseFits)
open HasteBootsFieldInputSmoke (parentFrames)
open HasteBootsEarlyReceiptSmoke (view)

/-- A real parsed native input supplies its computed context and original
root, without a caller-provided digest or binding equality. -/
example : view.field.data.context = InputIndexedOracle.sha512 HasteBootsBatchOrderedSmoke.world (GoldContextInput.bytes HasteBootsBatchOrderedSmoke.ctx.parameters) ∧
    view.field.data.root = HasteBootsBatchOrderedSmoke.ctx.root :=
  GoldCommonSourceBinding.batch_binding HasteBootsBatchOrderedSmoke.ctx HasteBootsBatchOrderedSmoke.world HasteBootsBatchOrderedSmoke.work HasteBootsBatchOrderedSmoke.prepared ⟨parentFrames,parent,parentValid,batchFits⟩
    responseFits view HasteBootsFieldColumnSmoke.parsed

example (sourceLog : Log) (radius : ℕ) :
    BatchOpeningNativeObligation.source root HasteBootsBatchOrderedSmoke.ctx primitive (by decide +kernel) HasteBootsBatchOrderedSmoke.world HasteBootsBatchOrderedSmoke.work HasteBootsBatchOrderedSmoke.prepared view radius sourceLog =
      GoldCommonSourceTable.table HasteBootsBatchOrderedSmoke.ctx.parameters primitive (by decide +kernel) root
        (InputIndexedOracle.sha512 HasteBootsBatchOrderedSmoke.world (GoldContextInput.bytes HasteBootsBatchOrderedSmoke.ctx.parameters)) HasteBootsBatchOrderedSmoke.ctx.root sourceLog radius
        (BatchOpeningNativeObligation.dimensions HasteBootsBatchOrderedSmoke.ctx HasteBootsBatchOrderedSmoke.world HasteBootsBatchOrderedSmoke.work HasteBootsBatchOrderedSmoke.prepared) :=
  GoldCommonSourceBinding.batch_table root HasteBootsBatchOrderedSmoke.ctx primitive (by decide +kernel) HasteBootsBatchOrderedSmoke.world HasteBootsBatchOrderedSmoke.work HasteBootsBatchOrderedSmoke.prepared
    ⟨parentFrames,parent,parentValid,batchFits⟩ responseFits view HasteBootsFieldColumnSmoke.parsed sourceLog radius

end Parsed

end
end FormalProof4FHE.HasteBoots.CommonSourceSmoke
