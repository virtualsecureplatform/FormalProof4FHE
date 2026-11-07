module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineGoldAllRisk
@[expose] public section

/-! First positive reads in the exact packets used by the priced closed
interpreter laws. The full prequery history is part of this same execution;
silent instructions do not become observation indices or fabricated starts. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineLineage
open InputIndexedOracle (Input World)
open NativeTranscript (Execution Observation)
open ClosedByteMachine (Instruction State Tape initialise take)
open ClosedByteMachineGoldRisk (history history_run packet)
open ClosedByteMachineRequest (command)
open CausalStreamExposure (seen firstRead)
noncomputable section

def initial (code : List Instruction) (privateData : Tape → Input) : World → Execution State := fun _ => pure (initialise code privateData)

theorem scalar_run (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (fuel : ℕ) (world : World) :
    (ClosedByteMachineHistory.history (initial code privateData) code publicData fuel world).run =
      (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run := by
  rw [ClosedByteMachineHistory.history,ObservationReplay.run_bind]
  rfl

theorem coverage (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (history code publicData privateData fuel world).run.2 input = true) :
    ∃ index < fuel,
      firstRead (command code publicData) (history code publicData privateData index world).run = some input ∧
      CausalFirstStreamPrefix.recover input (history code publicData privateData fuel world).run.2 =
        some (history code publicData privateData index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history code publicData privateData fuel world).run.2 =
          (history code publicData privateData index world).run.2 ++ .output input offset values :: after := by
  have scalarTouched : seen (ClosedByteMachineHistory.history (initial code privateData) code publicData fuel world).run.2 input = true := by
    simpa only [scalar_run,history_run,packet] using touched
  obtain ⟨index,bound,unseen,hit⟩ := ClosedByteMachineHistory.first_flip (initial code privateData) code publicData fuel world input rfl scalarTouched
  have recovered := ClosedByteMachineHistory.recover_at_flip (initial code privateData) code publicData fuel index world input bound unseen hit
  have selected := ClosedByteMachineRequest.firstRead_of_tick code publicData
    (ClosedByteMachineHistory.history (initial code privateData) code publicData index world).run.1
    (ClosedByteMachineHistory.history (initial code privateData) code publicData index world).run.2 world input unseen
      (by simpa only [ClosedByteMachineHistory.history_succ] using hit)
  refine ⟨index,bound,?_,?_,?_⟩
  · simpa only [scalar_run,history_run,packet] using selected
  · simpa only [scalar_run,history_run,packet] using recovered.1
  · simpa only [scalar_run,history_run,packet] using recovered.2
end
end FormalProof4FHE.HasteBoots.ClosedByteMachineLineage
