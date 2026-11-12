module
public import FormalProof4FHE.HasteBoots.EqualityLifetime
public import FormalProof4FHE.HasteBoots.ByteScalarLogWork
@[expose] public section

/-! Observation-clock equality charges are paid by actual specified byte
interpreter work. This is the original input-byte potential, not a physical
attacker-work definition or an all-horizon probability theorem. -/
namespace FormalProof4FHE.HasteBoots.EqualityLogWork
open InputIndexedOracle (Input World law)
open OracleProgram (Program run)
open EqualityPositionKernel (rate)
open MeasureTheory
noncomputable section

theorem score_eq {A : Type} (packet : (Program A ⊕ A) × List NativeTranscript.Observation) :
    EqualityPositionKernel.score packet = (ScalarEquationWork.selectedBytes OracleProgramMachine.step packet : ENNReal)*rate := by
  cases selected : CausalStreamExposure.firstRead OracleProgramMachine.step packet <;>
    simp [EqualityPositionKernel.score,ScalarEquationWork.selectedBytes,selected]

theorem charge_eq {A : Type} (program : Program A) (world : World) :
    EqualityLifetime.totalCharge program world = ScalarEquationWork.totalBytes program world * rate := by
  simp only [EqualityLifetime.totalCharge,EqualityPositionKernel.charge,score_eq,ScalarEquationWork.totalBytes,ENNReal.tsum_mul_right]

theorem program_charge {A : Type} (program : Program A) (world : World) :
    EqualityLifetime.totalCharge program world ≤ (ScalarLogWork.bytes (run program world).run.2 : ENNReal)*rate := by
  rw [charge_eq]
  exact mul_le_mul' (ScalarLogWork.program_bytes program world) le_rfl

theorem private_prefix_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (fuel : ℕ) (state : PrivateCoinByteMachine.State) (world : World) :
    EqualityLifetime.totalCharge (PrivateCoinByteMachine.take code publicData tape fuel state) world ≤
      ((run (PrivateCoinByteMachine.take code publicData tape fuel state) world).run.1.work : ENNReal)*rate :=
  (program_charge _ world).trans (mul_le_mul' (Nat.cast_le.mpr (ByteScalarLogWork.private_prefix_bytes code publicData tape fuel state world)) le_rfl)

def privateLifetimeCharge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : PrivateCoinReplay.Tape × World) : ENNReal :=
  ⨆ fuel : ℕ, EqualityLifetime.totalCharge
    (PrivateCoinByteMachine.take code publicData execution.1 fuel (PrivateCoinByteMachine.initialise code privateData)) execution.2

theorem private_lifetime_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (execution : PrivateCoinReplay.Tape × World) :
    privateLifetimeCharge code publicData privateData execution ≤ PrivateCoinByteWork.lifetimeWork code publicData privateData execution * rate := by
  apply iSup_le
  intro fuel
  apply (private_prefix_charge _ _ _ _ _ _).trans
  exact mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index execution) fuel) le_rfl

theorem private_expected_charge (coins : Measure PrivateCoinReplay.Tape) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) :
    (∫⁻ execution, privateLifetimeCharge code publicData privateData execution ∂coins.prod law) ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  calc
    _ ≤ ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution * rate ∂coins.prod law :=
      lintegral_mono (private_lifetime_charge code publicData privateData)
    _ = _ := lintegral_mul_const rate (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)

/-- Every original finite instruction horizon has a safe equality probability
bound paid by the same fixed-tape specified lifetime work. -/
theorem private_safe_probability (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (tape : PrivateCoinReplay.Tape) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (dummy : NativeRootMessage.Digest) :
    let program := InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel
    law {world | EqualityLifetime.Event program dummy world ∧ ¬GlobalReferenceBad.Bad program dummy world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * rate := by
  dsimp only
  apply (EqualityLifetime.safe_bound _ dummy).trans
  calc
    _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate ∂law := by
      apply lintegral_mono
      intro world
      exact (private_prefix_charge _ _ _ _ _ _).trans
        (mul_le_mul' (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) le_rfl)
    _ = _ := lintegral_mul_const rate (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

end
end FormalProof4FHE.HasteBoots.EqualityLogWork
