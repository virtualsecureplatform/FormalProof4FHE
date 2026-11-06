module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
@[expose] public section

/-! Any accepted native batch witnessed at any prefix of an unbounded causal machine lifetime has one global raw-source availability charge. The bound uses no batch, column, response-group or analysis-prefix union factor. Framing remains explicit in acceptance witnesses; physical work, lineage and application soundness remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSourceRisk
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (Program run)
open NativeRootFamilyLifetime (program prefixCharge Bad)
open MeasureTheory
noncomputable section

/-- Any witnessed native batch in any actual analysis prefix can fail source
availability; the machine itself need never terminate. -/
def Failure {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, NativeGoldBatchAnySourceRisk.Failure Memory dummy (run (program prelude step fuel) world).run.2 world

theorem failure_implies_lifetime_bad {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) (failed : Failure Memory dummy prelude step world) :
    ∃ fuel, Bad dummy (run (program prelude step fuel) world).run.2 := by
  obtain ⟨fuel,failed⟩ := failed
  exact ⟨fuel,NativeGoldBatchAnySourceRisk.failure_implies_bad Memory dummy world _
    ((OracleProgram.run_replay _).truthful world) failed⟩

theorem failure_measurable {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) : MeasurableSet {world | Failure Memory dummy prelude step world} := by
  have union : {world | Failure Memory dummy prelude step world} =
      ⋃ fuel : ℕ, {world | NativeGoldBatchAnySourceRisk.Failure Memory dummy (run (program prelude step fuel) world).run.2 world} := by
    ext world
    simp only [Failure,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => NativeGoldBatchAnySourceRisk.failure_measurable Memory dummy (program prelude step fuel))

/-- One global lifetime charge, with no union factor for batches, columns,
response groups or analysis-prefix count. It is not physical attacker work. -/
theorem lifetime_failure_le_charge {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) :
    InputIndexedOracle.law {world | Failure Memory dummy prelude step world} ≤
      ⨆ fuel : ℕ, prefixCharge dummy prelude step fuel := by
  have included : {world | Failure Memory dummy prelude step world} ⊆
      {world | ∃ fuel, Bad dummy (run (program prelude step fuel) world).run.2} :=
    fun world failed => failure_implies_lifetime_bad Memory dummy prelude step world failed
  exact (measure_mono included).trans (NativeRootFamilyLifetime.lifetime_bad_le_charge dummy prelude step)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSourceRisk
