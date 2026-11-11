module
import all FormalProof4FHE.HasteBoots.ReferenceRiskBudget
import all FormalProof4FHETest.HasteBootsFactorFiberSmoke

namespace FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke
open HasteBootsSamplerAncestrySmoke (worldZero)
noncomputable section

/-- Starts and empty reads pay naming-input bytes, while they do not name
receipt digest targets. The later hash contributes to both byte counts. -/
theorem naming_bytes :
    ClosedByteMachineRootBudget.inputWork [.start [17],.output [17] 999 [],.hash [17] []] = 3 ∧
    ReceiptDigestTargets.inputBytes [.start [17],.output [17] 999 [],.hash [17] []] = 1 := ⟨rfl,rfl⟩

/-- A zero analysis threshold excludes every score without changing execution. -/
theorem zero_threshold {S A : Type} (step : S → OracleMachine.Command S A)
    (packet : (S ⊕ A) × List NativeTranscript.Observation) : ReferenceRiskBudget.lowRisk step 0 packet = 0 := by
  simp [ReferenceRiskBudget.lowRisk]

/-- All later analysis positions after the actual five-entry mixed execution
have no request, irrespective of the first read's far offset. -/
theorem completed_suffix (later : ℕ) :
    CausalSeedExposure.request OracleProgramMachine.step
      (OracleProgram.runPrefix (5+later) FactorFiberSmoke.program worldZero).run.1 = none := by
  apply ProgramObservationClock.request_after_length
  change 5 ≤ 5+later
  omega

end
end FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke
