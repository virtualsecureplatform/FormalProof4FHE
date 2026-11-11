module
import all FormalProof4FHE.HasteBoots.ProgramReceiptCoverage
import all FormalProof4FHE.HasteBoots.AllocatedReceiptCoverage
import all FormalProof4FHETest.HasteBootsFreshReceiptTargetSmoke

namespace FormalProof4FHE.HasteBoots.ProgramReceiptSmoke
open FreshReceiptTargetSmoke (program phase past)
open HasteBootsSamplerAncestrySmoke (worldZero)
open OracleProgram (Program runPrefix)
noncomputable section

/-- The rare all-zero fixture really enters the shared lifetime ledger. -/
theorem fixture_bad : ProgramReceiptCoverage.Bad program worldZero := by
  refine ⟨4,?_⟩
  change FreshReceiptTargetRisk.event OracleProgramMachine.step (past worldZero).run worldZero
  simpa only [FreshReceiptTargetRisk.event,FreshReceiptTargetSmoke.selected] using FreshReceiptTargetSmoke.actual_target

/-- The far-offset read contributes the full-block charge exactly once. -/
theorem fixture_charge : FreshReceiptTargetRisk.risk OracleProgramMachine.step (runPrefix 4 program worldZero).run =
    1/(2 : ENNReal)^512 := by
  change FreshReceiptTargetRisk.risk OracleProgramMachine.step (past worldZero).run = _
  simp only [FreshReceiptTargetRisk.risk,FreshReceiptTargetSmoke.selected,
    FreshReceiptTargetSmoke.targets_one,Finset.card_singleton,Nat.cast_one]

/-- No further receipt charge is assigned to the later full digest read. -/
theorem later_charge : FreshReceiptTargetRisk.risk OracleProgramMachine.step (runPrefix 5 program worldZero).run = 0 := by
  have selected : FreshReceiptTargetRisk.select OracleProgramMachine.step (runPrefix 5 program worldZero).run = none := by
    change (if 0 < (64 : ℕ) ∧ CausalStreamExposure.seen
      [NativeTranscript.Observation.start (NativeReceiptPrefixView.key phase.consumed),
        .output (NativeReceiptPrefixView.key phase.consumed) 1000 [],
        .hash (NativeReceiptPrefixView.key phase.consumed) (List.ofFn (InputIndexedOracle.sha512 worldZero (NativeReceiptPrefixView.key phase.consumed))),
        .output FreshReceiptTargetSmoke.input 77 [0],.output (NativeReceiptPrefixView.key phase.consumed) 999 [0]]
      (NativeReceiptPrefixView.key phase.consumed) = false then some (NativeReceiptPrefixView.key phase.consumed) else none).bind ReceiptPayloadView.read = none
    simp [CausalStreamExposure.seen,CausalStreamExposure.touches]
  simp only [FreshReceiptTargetRisk.risk,selected]

/-- Terminated programs have zero lifetime charge at every world. -/
theorem pure_charge (world : InputIndexedOracle.World) :
    ProgramReceiptCoverage.totalCharge (.pure () : Program Unit) world = 0 := by
  unfold ProgramReceiptCoverage.totalCharge
  have zero (position : ℕ) : FreshReceiptTargetRisk.risk OracleProgramMachine.step
      (runPrefix position (.pure () : Program Unit) world).run = 0 := by
    cases position <;> rfl
  simp only [zero,tsum_zero]

end
end FormalProof4FHE.HasteBoots.ProgramReceiptSmoke
