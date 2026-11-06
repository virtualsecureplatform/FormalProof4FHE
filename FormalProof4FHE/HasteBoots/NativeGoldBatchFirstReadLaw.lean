module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRandomLaw
public import FormalProof4FHE.HasteBoots.CausalStreamExposure
@[expose] public section

/-! The checked native batch matrix law at the causal first positive read of
its exact absorbed challenge input, including reads at arbitrary offsets.
The fresh cache premise is derived from the complete mixed history. Global
lineage/coverage and response-bound column exposure remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFirstReadLaw
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchRandomLaw (phase reindex rectangular)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeFields (Goldilocks goldilocksModulus)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section

theorem conditional_uniform {Cfg Payload S A : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (phase work).pending.input)
    (event : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | (rectangular ctx world work prepared other).elim False event} =
      BudgetedUniformSequence.completion (CanonicalCoefficientVector.scalar goldilocksModulus 1) ctx.fieldFuel (work.geometry.rows*ctx.parameters.width.val) *
        Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks)}[event matrix] :=
  NativeGoldBatchRandomLaw.conditional_uniform ctx world work prepared replay enc dummy shape state hashStart
    (CausalStreamExposure.firstRead_fresh step (past world).run (phase work).pending.input selected world (phase work).consumed.length) event

theorem eventual_le_uniform {Cfg Payload S A : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (selected : CausalStreamExposure.firstRead step (past world).run = some (phase work).pending.input)
    (event : (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks) → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ∃ fuel, ((NativeFieldMatrixLaw.values goldilocksModulus fuel ctx.parameters.width.val work.geometry.rows (phase work) other).map
        (reindex ctx world work prepared)).elim False event} ≤
        Pr{let matrix ← $ᵗ (Fin ctx.parameters.width.val → NativeGoldBatchRectangularWeights.Row ctx → Goldilocks)}[event matrix] :=
  NativeGoldBatchRandomLaw.eventual_le_uniform ctx world work prepared replay enc dummy shape state hashStart
    (CausalStreamExposure.firstRead_fresh step (past world).run (phase work).pending.input selected world (phase work).consumed.length) event
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFirstReadLaw
