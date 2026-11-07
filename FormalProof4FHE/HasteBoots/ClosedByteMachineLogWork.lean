module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineGoldRisk
@[expose] public section

/-! Derived bounds on actual observed receipt guesses. Work remains the
closed interpreter's explicit instruction accounting, never log length. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineLogWork
open InputIndexedOracle (Input World)
open ClosedByteMachine (Instruction State take tick tickCost)
open NativeTranscript (Observation)

theorem tick_log_le_cost (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    (OracleProgram.run (tick code publicData state) world).run.2.length ≤ tickCost code publicData state := by
  cases stopped : state.stopped with
  | some stop => simp only [tick,tickCost,stopped]; exact le_rfl
  | none =>
    exact (ClosedByteMachine.tick_log_length code publicData state world).trans
      (Nat.succ_le_of_lt (ClosedByteMachine.tickCost_pos code publicData state stopped))

theorem take_one_log (code : List Instruction) (publicData : Input) (state : State) (world : World) :
    (OracleProgram.run (take code publicData 1 state) world).run.2 =
      (OracleProgram.run (tick code publicData state) world).run.2 := by
  rw [take,OracleProgram.run_bind,ObservationReplay.run_bind]
  change _ ++ [] = _
  exact List.append_nil _

theorem log_le_work (code : List Instruction) (publicData : Input) (fuel : ℕ) (state : State) (world : World) :
    (OracleProgram.run (take code publicData fuel state) world).run.2.length ≤
      (OracleProgram.run (take code publicData fuel state) world).run.1.work := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    rw [ClosedByteMachine.take_resume code publicData fuel 1,OracleProgram.run_bind,ObservationReplay.run_bind,List.length_append,
      take_one_log,ClosedByteMachine.take_one_work]
    exact Nat.add_le_add ih (tick_log_le_cost _ _ _ _)

theorem guesses_le_log (count : ℕ) (log : List Observation) :
    (NativeReceiptPrefixView.guesses count log).card ≤ log.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem guesses_le_work (code : List Instruction) (publicData : Input) (fuel count : ℕ) (state : State) (world : World) :
    (NativeReceiptPrefixView.guesses count (OracleProgram.run (take code publicData fuel state) world).run.2).card ≤
      (OracleProgram.run (take code publicData fuel state) world).run.1.work :=
  (guesses_le_log _ _).trans (log_le_work _ _ _ _ _)
end FormalProof4FHE.HasteBoots.ClosedByteMachineLogWork
