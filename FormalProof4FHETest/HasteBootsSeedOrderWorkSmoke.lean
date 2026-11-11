module
import all FormalProof4FHE.HasteBoots.SeedOrderIdentityWork
import all FormalProof4FHETest.HasteBootsParentStateSmoke

namespace HasteBootsSeedOrderWorkSmoke
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input World)
open OracleProgram (Program runPrefix)
open HasteBootsParentStateSmoke (child quoted world)
noncomputable section

def program : Program Unit := .read child 0 1 (fun _ => .pure ())

theorem selected : CausalSeedExposure.firstRead OracleProgramMachine.step (runPrefix 0 program world).run = some child := rfl

-- A self-quote is absent from prior targets but remains an ordering hazard.
theorem no_prior : ¬CausalSeedExposure.event OracleProgramMachine.step (runPrefix 0 program world).run world := by
  simp only [CausalSeedExposure.event,selected]
  exact Finset.notMem_empty _

theorem pending_hit : SeedOrderRiskBudget.event OracleProgramMachine.step (runPrefix 0 program world).run world := by
  right
  simp only [PendingSeedQuote.event,selected,quoted]
  rfl

theorem original_bad : SeedQuoteOrder.Bad OracleProgramMachine.step program world :=
  (SeedOrderRiskBudget.bad_iff program world).mpr ⟨0,pending_hit⟩

-- Extending the containing program retains this actual original exception.
theorem continued_bad : SeedQuoteOrder.Bad OracleProgramMachine.step
    (OracleProgram.bind program (fun _ => Program.start [17] (Program.pure ()))) world :=
  SeedOrderContinuation.bad program _ world original_bad

-- Even with an empty prior log, the pending self-quote has a full seed charge.
theorem first_charge : SeedOrderRiskBudget.lowRisk 1 (runPrefix 0 program world).run = 1/(2 : ENNReal)^512 := by
  have small : (runPrefix 0 program world).run.2.length < 1 := by decide
  simp only [SeedOrderRiskBudget.lowRisk,small,ite_true,SeedOrderRiskBudget.risk,
    CausalSeedExposure.risk,PendingSeedQuote.risk,selected,quoted]
  have guesses : NativeChildSeedView.guesses (runPrefix 0 program world).run.2 = ∅ := rfl
  rw [guesses,Finset.card_empty,Nat.cast_zero,ENNReal.zero_div,zero_add]

-- Completed packets create neither prior nor pending seed charges.
theorem completed_charge (threshold : ℕ) (history : List NativeTranscript.Observation) :
    SeedOrderRiskBudget.lowRisk threshold (((.inr ()) : Program Unit ⊕ Unit),history) = 0 :=
  SeedOrderRiskBudget.score_absent threshold _ rfl

end
end HasteBootsSeedOrderWorkSmoke
