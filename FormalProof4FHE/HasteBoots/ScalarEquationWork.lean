module
public import FormalProof4FHE.HasteBoots.AllocatedJointIdentityBound
public import FormalProof4FHE.HasteBoots.ScalarMetadataSize
@[expose] public section

/-! Scalar risk is a fixed rate times an actual first-read equation count.
The count is bounded by the selected input's native encoded bytes. These
are logical counts; native primitive and cache pricing remain separate. -/
namespace FormalProof4FHE.HasteBoots.ScalarEquationWork
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open OracleProgram (Program runPrefix)
open MeasureTheory
noncomputable section

def rate : ENNReal := (4 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ)

def equations {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) : ℕ :=
  match CausalStreamExposure.firstRead step packet with
  | none => 0
  | some input => match ScalarRecoveredReplay.recover input with
    | none => 0
    | some configuration => configuration.view.history.statement.infos.val.length

def selectedBytes {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) : ℕ :=
  match CausalStreamExposure.firstRead step packet with
  | none => 0
  | some input => input.length

theorem equations_le_input {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) (input : Input)
    (selected : CausalStreamExposure.firstRead step packet = some input) : equations step packet ≤ input.length := by
  unfold equations
  rw [selected]
  simp only []
  cases found : ScalarRecoveredReplay.recover input with
  | none => exact Nat.zero_le _
  | some configuration => exact ScalarMetadataSize.recovered_count_le input configuration found

theorem equations_le_bytes {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    equations step packet ≤ selectedBytes step packet := by
  cases selected : CausalStreamExposure.firstRead step packet with
  | none => simp [equations,selectedBytes,selected]
  | some input =>
    simpa only [selectedBytes,selected] using equations_le_input step packet input selected

theorem score_eq {A : Type} (packet : (Program A ⊕ A) × List Observation) :
    ScalarPositionKernel.score packet = (equations OracleProgramMachine.step packet : ENNReal) * rate := by
  unfold ScalarPositionKernel.score equations rate
  cases selected : CausalStreamExposure.firstRead OracleProgramMachine.step packet with
  | none => simp
  | some input =>
    simp only []
    cases found : ScalarRecoveredReplay.recover input <;> simp

def totalEquations {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, (equations OracleProgramMachine.step (runPrefix position program world).run : ENNReal)

def totalBytes {A : Type} (program : Program A) (world : World) : ENNReal :=
  ∑' position : ℕ, (selectedBytes OracleProgramMachine.step (runPrefix position program world).run : ENNReal)

theorem charge_eq {A : Type} (program : Program A) (world : World) :
    ScalarLifetimeComposition.totalCharge program world = totalEquations program world * rate := by
  simp only [ScalarLifetimeComposition.totalCharge,ScalarPositionKernel.charge,score_eq,totalEquations,ENNReal.tsum_mul_right]

theorem total_equations_le_bytes {A : Type} (program : Program A) (world : World) : totalEquations program world ≤ totalBytes program world :=
  ENNReal.tsum_le_tsum (fun position => Nat.cast_le.mpr (equations_le_bytes OracleProgramMachine.step (runPrefix position program world).run))

theorem charge_le_bytes {A : Type} (program : Program A) (world : World) :
    ScalarLifetimeComposition.totalCharge program world ≤ totalBytes program world * rate := by
  rw [charge_eq]
  exact mul_le_mul' (total_equations_le_bytes program world) le_rfl

theorem equations_measurable {A : Type} (program : Program A) : Measurable (totalEquations program) :=
  Measurable.tsum (fun position => OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program)
    (fun packet => (equations OracleProgramMachine.step packet : ENNReal)))

theorem bytes_measurable {A : Type} (program : Program A) : Measurable (totalBytes program) :=
  Measurable.tsum (fun position => OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program)
    (fun packet => (selectedBytes OracleProgramMachine.step packet : ENNReal)))

theorem expected_charge {A : Type} (program : Program A) :
    (∫⁻ world, ScalarLifetimeComposition.totalCharge program world ∂law) = (∫⁻ world, totalEquations program world ∂law) * rate := by
  simp_rw [charge_eq]
  exact lintegral_mul_const rate (equations_measurable program)

theorem expected_charge_le_bytes {A : Type} (program : Program A) :
    (∫⁻ world, ScalarLifetimeComposition.totalCharge program world ∂law) ≤ (∫⁻ world, totalBytes program world ∂law) * rate := by
  rw [expected_charge]
  exact mul_le_mul' (lintegral_mono (total_equations_le_bytes program)) le_rfl

end
end FormalProof4FHE.HasteBoots.ScalarEquationWork
