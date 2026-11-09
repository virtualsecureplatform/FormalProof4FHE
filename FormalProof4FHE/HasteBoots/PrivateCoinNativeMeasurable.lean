module
public import FormalProof4FHE.HasteBoots.PrivateCoinReplay
@[expose] public section

/-! Native failure measurability from finite tape use of each causal history.
Finite-use obligations belong to the private-coin execution refinement; they
are not assumptions that the tape itself has countably many outcomes. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinNativeMeasurable
open MeasureTheory
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open OracleProgram (Program run)
open PrivateCoinReplay (Tape FiniteUse)
open CausalExposureLifetime (history)
noncomputable section

theorem finite_measurable {S A : Type} (Memory : Type) (dummy : Digest)
    (ctx : Context) (radius : ℕ) (prelude : Tape → Program S)
    (step : Tape → S → OracleMachine.Command S A) (fuel : ℕ)
    (finiteUse : FiniteUse (fun tape => history (run (prelude tape)) id (step tape) fuel)) :
    MeasurableSet {execution : Tape × World |
      Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius execution.2
        (history (run (prelude execution.1)) id (step execution.1) fuel execution.2).run.2)} := by
  have equal : {execution : Tape × World |
      Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius execution.2
        (history (run (prelude execution.1)) id (step execution.1) fuel execution.2).run.2)} =
      {execution : Tape × World | NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy ctx radius
        (history (run (prelude execution.1)) id (step execution.1) fuel execution.2).run.2} := by
    ext execution
    exact NativeGoldBatchLifetimeMeasurable.witness_iff_history Memory dummy ctx radius _ _
      ((CausalExposureLifetime.history_replay (OracleProgram.run_replay (prelude execution.1))
        id (step execution.1) fuel).truthful execution.2)
  rw [equal]
  exact PrivateCoinReplay.event_measurable
    (fun tape => CausalExposureLifetime.history_replay (OracleProgram.run_replay (prelude tape)) id (step tape) fuel)
    finiteUse (NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy ctx radius)

/-- The lifetime event is jointly measurable even if every new prefix uses
more private coins. Its witnesses and continuation lengths remain unbounded. -/
theorem failure_measurable {S A : Type} (Memory : Type) (dummy : Digest)
    (ctx : Context) (radius : ℕ) (prelude : Tape → Program S)
    (step : Tape → S → OracleMachine.Command S A)
    (finiteUse : ∀ fuel, FiniteUse (fun tape => history (run (prelude tape)) id (step tape) fuel)) :
    MeasurableSet (PrivateCoinLifetime.failure Memory dummy ctx radius prelude step) := by
  have equal : PrivateCoinLifetime.failure Memory dummy ctx radius prelude step =
      ⋃ fuel : ℕ, {execution : Tape × World |
        Nonempty (NativeGoldBatchLifetimeSoundness.Witness Memory dummy ctx radius execution.2
          (history (run (prelude execution.1)) id (step execution.1) fuel execution.2).run.2)} := by
    ext execution
    simp [PrivateCoinLifetime.failure, NativeGoldBatchLifetimeSoundness.Failure]
  rw [equal]
  exact MeasurableSet.iUnion fun fuel =>
    finite_measurable Memory dummy ctx radius prelude step fuel (finiteUse fuel)
end
end FormalProof4FHE.HasteBoots.PrivateCoinNativeMeasurable
