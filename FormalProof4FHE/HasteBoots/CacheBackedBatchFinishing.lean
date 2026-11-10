module
public import FormalProof4FHE.HasteBoots.CacheBackedBatchSoundness
@[expose] public section

/-! Actual accepted native batch claims finish their original encoded group.
Constructor and root facts come from completed cache-backed code construction,
not caller-supplied primitive-root or encoding certificates. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedBatchFinishing
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldBlockCode (encoding logSize)
open NativeLookupRequestWire (Row)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem accepted_value {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (request : NativeGoldBlockCodeProgram.Request) (config : NativeGoldBlockCodeProgram.Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (result : NativeGoldBlockCodeProgram.Completed) (finished : config.phase = .done result)
    (retained : result.code = ctx.parameters.code)
    (index : Fin work.binding.queries.val.length) :
    ∃ (response claimed : Row) (group : Fin work.evaluations.length)
      (size : (work.binding.queries.val.get index).models.length = ctx.parameters.numVariables.val)
      (shape : (encoding ctx.parameters.code work.planRoot).messageLength = 2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)),
      group.val = (NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val ∧
      ctx.opening.evaluations.val[group.val]? = some response ∧ work.binding.values.val[index.val]? = some claimed ∧
      claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishEncoded
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) (CacheBackedBatchSoundness.primitive ctx request config reachable result finished retained))
        (NativeGoldBlockCodeMeaning.constructor_dimensions (CacheBackedBatchSoundness.constructorTables request config reachable) request.message request.block request.blowup ctx.parameters.code (CacheBackedBatchSoundness.constructed ctx request config reachable result finished retained)).2.2.1
        (NativeGoldSuffixFinishing.encodedRight ctx.parameters (work.binding.queries.val.get index) (encoding ctx.parameters.code work.planRoot) size shape)
        (fun lane => NativeGoldResponseMeaning.laneWord (encoding ctx.parameters.code work.planRoot) (work.evaluations.get group) lane.val)) := by
  exact NativeGoldBatchFinishingMeaning.accepted_value ctx choose fuel memory world work completion executed parent accepted
    (CacheBackedBatchSoundness.constructorTables request config reachable) request.message request.block request.blowup
    (CacheBackedBatchSoundness.constructed ctx request config reachable result finished retained)
    (CacheBackedBatchSoundness.primitive ctx request config reachable result finished retained) index

end
end FormalProof4FHE.HasteBoots.CacheBackedBatchFinishing
