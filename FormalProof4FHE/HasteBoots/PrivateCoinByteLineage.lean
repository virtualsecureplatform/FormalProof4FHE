module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteRequest
@[expose] public section

/-! First positive stream reads on the actual runtime-coin instruction clock.
Private bytes, local instructions and stopped stuttering produce no fabricated
oracle observations. Recovery retains the complete earlier mixed history. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteLineage
open InputIndexedOracle (Input World)
open NativeTranscript (Execution Observation)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State take initialise)
open PrivateCoinByteRequest (command)
open CausalStreamExposure (seen firstRead)
noncomputable section

abbrev Packet := NativeIndexExposureRisk.Packet State State

def packet (state : State) (log : List Observation) : Packet := (.inl state, log)

def history (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) : Execution (State ⊕ State) :=
  OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world >>= fun state => pure (.inl state)

theorem history_run (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) :
    (history code publicData privateData tape fuel world).run =
      packet (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.2 := by
  rw [history, ObservationReplay.run_bind]
  change (_, _ ++ []) = (_, _)
  rw [List.append_nil]
  rfl

theorem history_replay (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) : ObservationReplay.Replayable (history code publicData privateData tape fuel) :=
  ObservationReplay.bind_replay (OracleProgram.run_replay _)
    (fun state => ObservationReplay.pure_replay (Sum.inl state : State ⊕ State))

def initial (code : List Instruction) (privateData : ClosedByteMachine.Tape → Input) : World → Execution State :=
  fun _ => pure (initialise code privateData)

theorem scalar_run (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) :
    (InstructionClock.history (initial code privateData) (command code publicData tape) fuel world).run =
      (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run := by
  rw [InstructionClock.history, ObservationReplay.run_bind, PrivateCoinByteRequest.take_exact]
  rfl

theorem coverage (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (tape : Tape) (fuel : ℕ) (world : World) (input : Input)
    (touched : seen (history code publicData privateData tape fuel world).run.2 input = true) :
    ∃ index < fuel,
      firstRead (command code publicData tape) (history code publicData privateData tape index world).run = some input ∧
      CausalFirstStreamPrefix.recover input (history code publicData privateData tape fuel world).run.2 =
        some (history code publicData privateData tape index world).run.2 ∧
      ∃ offset values after, values ≠ [] ∧
        (history code publicData privateData tape fuel world).run.2 =
          (history code publicData privateData tape index world).run.2 ++ .output input offset values :: after := by
  have scalarTouched : seen (InstructionClock.history (initial code privateData)
      (command code publicData tape) fuel world).run.2 input = true := by
    simpa only [scalar_run, history_run, packet] using touched
  obtain ⟨index, bound, unseen, hit⟩ := InstructionClock.first_flip (initial code privateData)
    (command code publicData tape) fuel world input rfl scalarTouched
  have recovered := InstructionClock.recover_at_flip (initial code privateData)
    (command code publicData tape) fuel index world input bound unseen hit
  have selected := PrivateCoinByteRequest.firstRead_of_tick code publicData tape
    (InstructionClock.history (initial code privateData) (command code publicData tape) index world).run.1
    (InstructionClock.history (initial code privateData) (command code publicData tape) index world).run.2
    world input unseen (by
      simpa only [InstructionClock.history_succ, ← PrivateCoinByteRequest.command_exact] using hit)
  refine ⟨index, bound, ?_, ?_, ?_⟩
  · simpa only [scalar_run, history_run, packet] using selected
  · simpa only [scalar_run, history_run, packet] using recovered.1
  · simpa only [scalar_run, history_run, packet] using recovered.2
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteLineage
