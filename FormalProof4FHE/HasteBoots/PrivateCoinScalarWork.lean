module
public import FormalProof4FHE.HasteBoots.ClosedByteScalarWork
public import FormalProof4FHE.HasteBoots.PrivateCoinByteFixed
@[expose] public section

/-! Runtime private-coin scalar equation charges are bounded by the existing
interpreter work counter. Coins are consumed by real instructions, not
preloaded in a fuel-dependent run. Physical RNG/cache prices remain open. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinScalarWork
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open PrivateCoinByteMachine (Instruction State take tickCost initialise)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

theorem lift_bytes (command : OracleMachine.Command ClosedByteMachine.State ClosedByteMachine.State) (state : State) (log : List Observation) :
    ScalarEquationWork.selectedBytes (fun _ : State => PrivateCoinByteRequest.lift state.cursor command) (.inl state,log) =
      ScalarEquationWork.selectedBytes (fun _ : ClosedByteMachine.State => command) (.inl state.machine,log) := by
  cases command <;> rfl

theorem command_bytes (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (log : List Observation) :
    ScalarEquationWork.selectedBytes (PrivateCoinByteRequest.command code publicData tape) (.inl state,log) ≤ tickCost code publicData state := by
  cases stopped : state.machine.stopped with
  | some reason => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
      PrivateCoinByteRequest.command,tickCost,stopped]
  | none =>
    cases selected : code[state.machine.pc]? with
    | none => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
        PrivateCoinByteRequest.command,tickCost,stopped,selected]
    | some chosen =>
      cases chosen with
      | coin dst => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
          PrivateCoinByteRequest.command,tickCost,stopped,selected]
      | base instruction =>
        have same : ScalarEquationWork.selectedBytes (PrivateCoinByteRequest.command code publicData tape) (.inl state,log) =
            ScalarEquationWork.selectedBytes (fun _ : State => PrivateCoinByteRequest.lift state.cursor
              (ClosedByteMachineRequest.instruction publicData state.machine instruction)) (.inl state,log) := by
          simp only [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
            PrivateCoinByteRequest.command,stopped,selected]
        rw [same,lift_bytes]
        simpa only [tickCost,stopped,selected,ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request] using ClosedByteScalarWork.instruction_bytes publicData state.machine instruction log

theorem equations_le_cost (code : List Instruction) (publicData : Input) (tape : Tape) (state : State) (log : List Observation) :
    ScalarEquationWork.equations (PrivateCoinByteRequest.command code publicData tape) (.inl state,log) ≤ tickCost code publicData state :=
  (ScalarEquationWork.equations_le_bytes _ _).trans (command_bytes code publicData tape state log)

def totalCharge (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (tape : Tape) (world : World) : ENNReal :=
  ∑' fuel : ℕ, (ScalarEquationWork.equations (PrivateCoinByteRequest.command code publicData tape)
    (PrivateCoinByteFixed.history code publicData tape privateData fuel world).run : ENNReal) * ScalarEquationWork.rate

theorem charge_le_work (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (tape : Tape) (world : World) :
    totalCharge code publicData privateData tape world ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * ScalarEquationWork.rate := by
  unfold totalCharge
  calc
    _ ≤ ∑' fuel : ℕ, (tickCost code publicData (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) * ScalarEquationWork.rate := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      rw [PrivateCoinByteFixed.history_run]
      exact mul_le_mul' (Nat.cast_le.mpr (equations_le_cost code publicData tape _ _)) le_rfl
    _ = _ := ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_mul' (PrivateCoinByteFixed.stepCost_tsum_le code publicData tape privateData world) le_rfl

theorem expected_charge_le_work (coins : Measure Tape) (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) :
    (∫⁻ execution : Tape × World, totalCharge code publicData privateData execution.1 execution.2 ∂coins.prod law) ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * ScalarEquationWork.rate := by
  calc
    _ ≤ ∫⁻ execution : Tape × World, PrivateCoinByteWork.lifetimeWork code publicData privateData execution * ScalarEquationWork.rate ∂coins.prod law :=
      lintegral_mono (fun execution => charge_le_work code publicData privateData execution.1 execution.2)
    _ = _ := lintegral_mul_const ScalarEquationWork.rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)

end
end FormalProof4FHE.HasteBoots.PrivateCoinScalarWork
