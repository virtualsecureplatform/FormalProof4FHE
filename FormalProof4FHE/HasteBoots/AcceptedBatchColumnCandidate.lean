module
public import FormalProof4FHE.HasteBoots.AdaptiveBatchColumnLifetime
@[expose] public section

/-! Accepted native execution supplies all adaptive column-candidate data.
The selecting first read may precede verification and occur at any offset. -/
namespace FormalProof4FHE.HasteBoots.AcceptedBatchColumnCandidate
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeRootMessage (Digest)
noncomputable section

theorem candidate {A Memory : Type} (program : Program A) (world : World) (position : ℕ)
    (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx) (role : NativeBrakedownCalibration.Role)
    (admitted : NativeGoldBatchCalibration.Matches ctx role) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (work : Prepared) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (run program world).run.2 ctx choose fuel memory work)
    (selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run =
      some (NativeGoldBatchColumnRequestLaw.input ctx work world)) :
    ∃ found : BatchColumnParameterCandidate.Candidate program position ctx.parent.profile world,
      found.ctx = ctx ∧ found.decoded = decoded ∧ found.role = role := by
  obtain ⟨⟨before,parent,valid,fits⟩,completion,_,executed,_,observed⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,computed⟩ := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared
    before parent valid fits responseFits decoded parsed
  obtain ⟨first,atFirst⟩ := ProgramStreamReadCoverage.first program world position _ selected
  refine ⟨⟨ctx,origin,role,admitted,rfl,NativeGoldBatchColumnRequestLaw.input ctx work world,decoded,?_,first,atFirst,computed,?_⟩,rfl,rfl,rfl⟩
  · exact parsed
  · exact (NativeGoldBatchContextHistory.completed_context_log ctx choose fuel memory world work completion executed).trans observed

theorem occurs {A Memory : Type} (program : Program A) (world : World) (position : ℕ) (dummy : Digest)
    (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx) (role : NativeBrakedownCalibration.Role)
    (admitted : NativeGoldBatchCalibration.Matches ctx role) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (work : Prepared) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (run program world).run.2 ctx choose fuel memory work)
    (selected : CausalStreamExposure.firstRead OracleProgramMachine.step (runPrefix position program world).run =
      some (NativeGoldBatchColumnRequestLaw.input ctx work world))
    (proximity : NativeGoldBatchProfileColumnExposure.event dummy ctx (origin.primitiveAt ctx rfl)
      ctx.parent.profile OracleProgramMachine.step (runPrefix position program world).run
      (NativeBrakedownCalibration.radius .goldilocks role) world) :
    AdaptiveBatchColumnKernel.Occurs program position ctx.parent.profile dummy world := by
  obtain ⟨found,ctxEq,_,roleEq⟩ := candidate program world position ctx origin role admitted choose fuel memory work decoded parsed responseFits accepted selected
  refine ⟨found,?_⟩
  have params : found.ctx.parameters = ctx.parameters := congrArg Context.parameters ctxEq
  rw [roleEq]
  exact (NativeGoldBatchEventContext.profile_column_event dummy ctx found.ctx params.symm
    (origin.primitiveAt ctx rfl) (found.origin.primitiveAt _ rfl)
    (NativeBrakedownCalibration.radius .goldilocks role) ctx.parent.profile OracleProgramMachine.step _ world).mp proximity

end
end FormalProof4FHE.HasteBoots.AcceptedBatchColumnCandidate
