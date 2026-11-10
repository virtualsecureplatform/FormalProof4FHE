module
public import FormalProof4FHE.HasteBoots.CacheBackedBatchAcceptance
@[expose] public section

/-! Every missing native opening view across an unbounded causal lifetime is
covered by the same persistent history risk. Each complete prefix includes the
prelude, issued calls, rejection and suffix work; caches and ledgers do not reset.
This is an ideal-oracle charge supremum, not a physical attacker-work theorem. -/
namespace FormalProof4FHE.HasteBoots.CacheBackedBatchAcceptanceLifetime
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (Program run)
open MeasureTheory
noncomputable section

def Failure {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, CacheBackedBatchAcceptance.Failure Memory dummy
    (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2 world

theorem failure_covered {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) (failed : Failure Memory dummy prelude step world) :
    ∃ fuel, NativeRootFamilyLifetime.Bad dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2 := by
  obtain ⟨fuel,missing⟩ := failed
  exact ⟨fuel,CacheBackedBatchAcceptance.failure_implies_bad Memory dummy world _
    ((OracleProgram.run_replay (NativeRootFamilyLifetime.program prelude step fuel)).truthful world) missing⟩

/-- No batch/trial cutoff or owner/group union: every witnessed acceptance in
all actual prefixes is covered by one supremum of increasing history charges. -/
theorem failure_le_charge {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) :
    InputIndexedOracle.law {world | Failure Memory dummy prelude step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy prelude step fuel := by
  have included : {world | Failure Memory dummy prelude step world} ⊆
      {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2} :=
    fun world failed => failure_covered Memory dummy prelude step world failed
  exact (measure_mono included).trans (NativeRootFamilyLifetime.lifetime_bad_le_charge dummy prelude step)

end
end FormalProof4FHE.HasteBoots.CacheBackedBatchAcceptanceLifetime
