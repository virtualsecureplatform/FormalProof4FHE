module
public import FormalProof4FHE.HasteBoots.ScalarLogWork
public import FormalProof4FHE.HasteBoots.PrivateCoinScalarWork
public import FormalProof4FHE.HasteBoots.PrivateCoinByteRootBudget
@[expose] public section

/-! The original observation-clock scalar charge of every actual interpreter
prefix is paid by its specified work counter. Silent instructions and
runtime coins retain their original execution and work accounting. -/
namespace FormalProof4FHE.HasteBoots.ByteScalarLogWork
open InputIndexedOracle (Input World law)
open OracleProgram (run)
open ScalarLogWork (bytes weight)
open MeasureTheory
noncomputable section

theorem bytes_le_inputWork (log : List NativeTranscript.Observation) :
    bytes log ≤ ClosedByteMachineRootBudget.inputWork log := by
  induction log with
  | nil => exact le_rfl
  | cons entry rest ih =>
    have head : weight entry ≤ (NativeParentLedgerPools.inputOf entry).length := by
      cases entry with
      | output input offset values => simp only [weight,NativeParentLedgerPools.inputOf]; split_ifs <;> omega
      | _ => exact Nat.zero_le _
    exact Nat.add_le_add head ih

theorem prefix_bytes (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (fuel : ℕ) (state : ClosedByteMachine.State) (world : World) :
    bytes (run (ClosedByteMachine.take code publicData fuel state) world).run.2 ≤
      (run (ClosedByteMachine.take code publicData fuel state) world).run.1.work :=
  (bytes_le_inputWork _).trans (ClosedByteMachineRootBudget.take_inputWork_le _ _ _ _ _)

theorem prefix_charge (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (fuel : ℕ) (state : ClosedByteMachine.State) (world : World) :
    ScalarLifetimeComposition.totalCharge (ClosedByteMachine.take code publicData fuel state) world ≤
      ((run (ClosedByteMachine.take code publicData fuel state) world).run.1.work : ENNReal)*ScalarEquationWork.rate :=
  (ScalarLogWork.program_charge _ _).trans (mul_le_mul' (Nat.cast_le.mpr (prefix_bytes _ _ _ _ _)) le_rfl)

theorem private_prefix_bytes (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (fuel : ℕ) (state : PrivateCoinByteMachine.State) (world : World) :
    bytes (run (PrivateCoinByteMachine.take code publicData tape fuel state) world).run.2 ≤
      (run (PrivateCoinByteMachine.take code publicData tape fuel state) world).run.1.work :=
  (bytes_le_inputWork _).trans (PrivateCoinByteRootBudget.take_inputWork_le _ _ _ _ _ _)

theorem private_prefix_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (fuel : ℕ) (state : PrivateCoinByteMachine.State) (world : World) :
    ScalarLifetimeComposition.totalCharge (PrivateCoinByteMachine.take code publicData tape fuel state) world ≤
      ((run (PrivateCoinByteMachine.take code publicData tape fuel state) world).run.1.work : ENNReal)*ScalarEquationWork.rate :=
  (ScalarLogWork.program_charge _ _).trans (mul_le_mul' (Nat.cast_le.mpr (private_prefix_bytes _ _ _ _ _ _)) le_rfl)

/-- The actual observation-clock charge is retained at every instruction
horizon, including executions that never halt. -/
def privateLifetimeCharge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : PrivateCoinReplay.Tape × World) : ENNReal :=
  ⨆ fuel : ℕ, ScalarLifetimeComposition.totalCharge
    (PrivateCoinByteMachine.take code publicData execution.1 fuel (PrivateCoinByteMachine.initialise code privateData)) execution.2

theorem private_lifetime_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : PrivateCoinReplay.Tape × World) :
    privateLifetimeCharge code publicData privateData execution ≤
      PrivateCoinByteWork.lifetimeWork code publicData privateData execution * ScalarEquationWork.rate := by
  apply iSup_le
  intro fuel
  apply (private_prefix_charge _ _ _ _ _ _).trans
  exact mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index execution) fuel) le_rfl

theorem private_expected_charge (coins : Measure PrivateCoinReplay.Tape) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) :
    (∫⁻ execution, privateLifetimeCharge code publicData privateData execution ∂coins.prod law) ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * ScalarEquationWork.rate := by
  calc
    _ ≤ ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution * ScalarEquationWork.rate ∂coins.prod law :=
      lintegral_mono (private_lifetime_charge code publicData privateData)
    _ = _ := lintegral_mul_const ScalarEquationWork.rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)

/-- The existing safe scalar event now pays actual specified lifetime work,
for every instruction horizon of the original closed interpreter. -/
theorem safe_probability (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (dummy : NativeRootMessage.Digest) (radius : ℕ) :
    let program := ClosedByteMachine.take code publicData fuel (ClosedByteMachine.initialise code privateData)
    law {world | ScalarLifetimeComposition.Event program dummy radius world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      ClosedByteMachineWork.expectedWork code publicData privateData * ScalarEquationWork.rate := by
  dsimp only
  apply (ScalarLifetimeComposition.safe_bound _ dummy radius).trans
  calc
    _ ≤ ∫⁻ world, ClosedByteMachineWork.lifetimeWork code publicData privateData world * ScalarEquationWork.rate ∂law := by
      apply lintegral_mono
      intro world
      exact (prefix_charge _ _ _ _ _).trans
        (mul_le_mul' (le_iSup (fun index => ClosedByteMachineWork.prefixWork code publicData privateData index world) fuel) le_rfl)
    _ = _ := lintegral_mul_const ScalarEquationWork.rate (ClosedByteMachineWork.lifetimeWork_measurable code publicData privateData)

/-- Fixed-tape sections retain the original runtime coin execution. -/
theorem private_safe_probability (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (privateData : ClosedByteMachine.Tape → Input)
    (fuel : ℕ) (dummy : NativeRootMessage.Digest) (radius : ℕ) :
    let program := PrivateCoinByteMachine.take code publicData tape fuel (PrivateCoinByteMachine.initialise code privateData)
    law {world | ScalarLifetimeComposition.Event program dummy radius world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * ScalarEquationWork.rate := by
  dsimp only
  apply (ScalarLifetimeComposition.safe_bound _ dummy radius).trans
  calc
    _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * ScalarEquationWork.rate ∂law := by
      apply lintegral_mono
      intro world
      exact (private_prefix_charge _ _ _ _ _ _).trans
        (mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) le_rfl)
    _ = _ := lintegral_mul_const ScalarEquationWork.rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

end
end FormalProof4FHE.HasteBoots.ByteScalarLogWork
