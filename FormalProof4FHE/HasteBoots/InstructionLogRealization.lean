module
public import FormalProof4FHE.HasteBoots.PrivateCoinReferenceProbability
@[expose] public section

/-! Every raw observation prefix of an actual runtime-coin interpreter run
is the exact log of an actual instruction prefix. Silent instructions remain
in the instruction clock; no observations are invented or discarded. -/
namespace FormalProof4FHE.HasteBoots.InstructionLogRealization
open InputIndexedOracle (Input World)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction State take tick)
open OracleProgram (run runPrefix)
noncomputable section

theorem next_log (code : List Instruction) (publicData : Input) (tape : Tape)
    (state : State) (fuel : ℕ) (world : World) :
    (run (take code publicData tape (fuel+1) state) world).run.2 =
      (run (take code publicData tape fuel state) world).run.2 ++
        (run (tick code publicData tape (run (take code publicData tape fuel state) world).run.1) world).run.2 := by
  rw [PrivateCoinByteMachine.take_resume code publicData tape fuel 1,OracleProgram.run_bind,ObservationReplay.run_bind,
    PrivateCoinByteLogWork.take_one_log]

theorem take_log (code : List Instruction) (publicData : Input) (tape : Tape)
    (state : State) (fuel count : ℕ) (world : World)
    (bounded : count ≤ (run (take code publicData tape fuel state) world).run.2.length) :
    ∃ index ≤ fuel, (run (take code publicData tape index state) world).run.2 =
      (run (take code publicData tape fuel state) world).run.2.take count := by
  induction fuel with
  | zero =>
    have zero : count = 0 := Nat.eq_zero_of_le_zero bounded
    subst count
    exact ⟨0,le_rfl,rfl⟩
  | succ fuel ih =>
    by_cases earlier : count ≤ (run (take code publicData tape fuel state) world).run.2.length
    · obtain ⟨index,inside,same⟩ := ih earlier
      refine ⟨index,by omega,?_⟩
      rw [next_log,List.take_append_of_le_length earlier]
      exact same
    · have one := PrivateCoinByteRequest.tick_log_length code publicData tape
        (run (take code publicData tape fuel state) world).run.1 world
      have length := congrArg List.length (next_log code publicData tape state fuel world)
      rw [List.length_append] at length
      have equal : count = (run (take code publicData tape (fuel+1) state) world).run.2.length := by omega
      exact ⟨fuel+1,le_rfl,by rw [equal,List.take_length]⟩

theorem raw_prefix (code : List Instruction) (publicData : Input) (tape : Tape)
    (state : State) (fuel position : ℕ) (world : World) :
    ∃ index ≤ fuel, (run (take code publicData tape index state) world).run.2 =
      (runPrefix position (take code publicData tape fuel state) world).run.2 := by
  have growing := OracleProgramMachine.log_prefix_run position (take code publicData tape fuel state) world
  rw [OracleProgramMachine.take_run] at growing
  obtain ⟨index,inside,same⟩ := take_log code publicData tape state fuel
    (runPrefix position (take code publicData tape fuel state) world).run.2.length world growing.length_le
  refine ⟨index,inside,?_⟩
  obtain ⟨tail,split⟩ := growing
  rw [← split,List.take_left] at same
  exact same

theorem pcs_prefix (code : List Instruction) (publicData : Input) (tape : Tape)
    (state : State) (fuel position : ℕ) (world : World) :
    ∃ index ≤ fuel, (run (take code publicData tape index state) world).run.2 =
      (CausalExposureLifetime.history (SingleOpeningLifetimeSoundness.clean (take code publicData tape fuel state))
        id OracleProgramMachine.step position world).run.2 := by
  rw [ProgramOpeningLifetime.history_log]
  exact raw_prefix code publicData tape state fuel position world

end
end FormalProof4FHE.HasteBoots.InstructionLogRealization
