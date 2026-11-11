module
public import FormalProof4FHE.HasteBoots.ScalarEquationWork
public import FormalProof4FHE.HasteBoots.ClosedByteMachineGoldRisk
@[expose] public section

/-! Native scalar equation counts are paid by actual issued instructions of
the existing closed byte interpreter. This uses its specified byte prices;
Rust instruction and primitive/cache pricing refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteScalarWork
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open ClosedByteMachine (Instruction State Tape initialise take tickCost)
open ClosedByteMachineRequest (command)
open MeasureTheory
noncomputable section

theorem instruction_bytes (publicData : Input) (state : State) (chosen : Instruction) (log : List Observation) :
    ScalarEquationWork.selectedBytes (fun current => ClosedByteMachineRequest.instruction publicData current chosen) (.inl state,log) ≤
      ClosedByteMachine.price publicData state chosen := by
  cases chosen with
  | read src dst offset count =>
    simp only [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
      ClosedByteMachineRequest.instruction,ClosedByteMachine.price]
    split_ifs
    · change (state.tapes src).length ≤ _
      omega
    · exact Nat.zero_le _
  | readTape src dst offset count =>
    simp only [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
      ClosedByteMachineRequest.instruction,ClosedByteMachine.price]
    split_ifs
    · change (state.tapes src).length ≤ _
      omega
    · exact Nat.zero_le _
  | pop src dst =>
    cases values : state.tapes src <;> simp [values,ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
      ClosedByteMachineRequest.instruction,ClosedByteMachine.price]
  | _ => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,
      ClosedByteMachineRequest.instruction,ClosedByteMachine.price]

theorem command_bytes (code : List Instruction) (publicData : Input) (state : State) (log : List Observation) :
    ScalarEquationWork.selectedBytes (command code publicData) (.inl state,log) ≤ tickCost code publicData state := by
  cases stopped : state.stopped with
  | some reason => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,command,tickCost,stopped]
  | none =>
    cases selected : code[state.pc]? with
    | none => simp [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,command,tickCost,stopped,selected]
    | some chosen =>
      simpa only [ScalarEquationWork.selectedBytes,CausalStreamExposure.firstRead,CausalSeedExposure.request,command,tickCost,stopped,selected] using
        instruction_bytes publicData state chosen log

theorem equations_le_cost (code : List Instruction) (publicData : Input) (state : State) (log : List Observation) :
    ScalarEquationWork.equations (command code publicData) (.inl state,log) ≤ tickCost code publicData state :=
  (ScalarEquationWork.equations_le_bytes _ _).trans (command_bytes code publicData state log)

def totalCharge (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, (ScalarEquationWork.equations (command code publicData)
    (ClosedByteMachineGoldRisk.history code publicData privateData fuel world).run : ENNReal) * ScalarEquationWork.rate

theorem charge_le_work (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (world : World) :
    totalCharge code publicData privateData world ≤ ClosedByteMachineWork.lifetimeWork code publicData privateData world * ScalarEquationWork.rate := by
  unfold totalCharge
  calc
    _ ≤ ∑' fuel : ℕ, (tickCost code publicData (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) * ScalarEquationWork.rate := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      rw [ClosedByteMachineGoldRisk.history_run]
      exact mul_le_mul' (Nat.cast_le.mpr (equations_le_cost code publicData _ _)) le_rfl
    _ = _ := ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_mul' (ClosedByteMachineWork.stepCost_tsum_le code publicData privateData world) le_rfl

end
end FormalProof4FHE.HasteBoots.ClosedByteScalarWork
