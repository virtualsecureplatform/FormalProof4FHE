module
public import FormalProof4FHE.HasteBoots.SeedOrderRiskBudget
@[expose] public section

/-! Actual seed-order exceptions persist through enclosing program
continuations with the same original selecting request and raw history. -/
namespace FormalProof4FHE.HasteBoots.SeedOrderContinuation
open InputIndexedOracle (World)
open OracleProgram (Program bind runPrefix)
noncomputable section

theorem event {A B : Type} (program : Program A) (next : A → Program B) (position : ℕ) (world : World)
    (occurred : SeedOrderRiskBudget.event OracleProgramMachine.step (runPrefix position program world).run world) :
    SeedOrderRiskBudget.event OracleProgramMachine.step (runPrefix position (bind program next) world).run world := by
  have active : CausalSeedExposure.request OracleProgramMachine.step (runPrefix position program world).run.1 ≠ none := by
    intro absent
    simp only [SeedOrderRiskBudget.event,CausalSeedExposure.event,PendingSeedQuote.event,CausalSeedExposure.firstRead,absent,false_or] at occurred
  obtain ⟨logEq,requestEq⟩ := ReferenceContinuation.packet program next position world active
  simpa only [SeedOrderRiskBudget.event,CausalSeedExposure.event,PendingSeedQuote.event,CausalSeedExposure.firstRead,logEq,requestEq] using occurred

theorem bad {A B : Type} (program : Program A) (next : A → Program B) (world : World)
    (occurred : SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    SeedQuoteOrder.Bad OracleProgramMachine.step (bind program next) world := by
  obtain ⟨position,hit⟩ := (SeedOrderRiskBudget.bad_iff program world).mp occurred
  exact (SeedOrderRiskBudget.bad_iff (bind program next) world).mpr ⟨position,event program next position world hit⟩

end
end FormalProof4FHE.HasteBoots.SeedOrderContinuation
