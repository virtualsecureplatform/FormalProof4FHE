module
public import FormalProof4FHE.HasteBoots.ProgramObservationClock
@[expose] public section

/-! All four original non-root reference risk scores are paid by observed
input bytes and observation count. Thresholds restrict only these scores;
they do not truncate the original interpreter or private random tape. -/
namespace FormalProof4FHE.HasteBoots.ReferenceRiskBudget
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open ClosedByteMachineRootBudget (inputWork)
noncomputable section

theorem parent_card (log : List Observation) : (ParentSeedCandidates.inputs log).card ≤ log.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem context_bytes (log : List Observation) : ContextDigestTargets.inputBytes log = inputWork log := rfl

theorem receipt_bytes (log : List Observation) : ReceiptDigestTargets.inputBytes log ≤ inputWork log := by
  induction log with
  | nil => exact le_rfl
  | cons entry rest ih =>
    have head : ReceiptDigestTargets.namedBytes entry ≤ (NativeParentLedgerPools.inputOf entry).length := by
      cases entry with
      | output input offset values => simp only [ReceiptDigestTargets.namedBytes,NativeParentLedgerPools.inputOf]; split_ifs <;> omega
      | start input => exact Nat.zero_le _
      | hash input digest => exact Nat.le_refl _
    exact Nat.add_le_add head ih

theorem parent_risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    ParentSeedCollisionRisk.risk step packet ≤ (packet.2.length : ENNReal)/2^512 := by
  cases chosen : ParentSeedCollisionRisk.select step packet with
  | none => simp only [ParentSeedCollisionRisk.risk,chosen]; exact zero_le
  | some input =>
    simp only [ParentSeedCollisionRisk.risk,chosen]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (parent_card packet.2)) _

theorem context_risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    ContextTargetRisk.risk step packet ≤ ((2*inputWork packet.2 : ℕ) : ENNReal)/2^512 := by
  cases chosen : ContextTargetRisk.select step packet with
  | none => simp only [ContextTargetRisk.risk,chosen]; exact zero_le
  | some input =>
    simp only [ContextTargetRisk.risk,chosen]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by simpa only [context_bytes] using ContextDigestTargets.card packet.2)) _

theorem fresh_risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    FreshReceiptTargetRisk.risk step packet ≤ (inputWork packet.2 : ENNReal)/2^512 := by
  cases chosen : FreshReceiptTargetRisk.select step packet with
  | none => simp only [FreshReceiptTargetRisk.risk,chosen]; exact zero_le
  | some input =>
    simp only [FreshReceiptTargetRisk.risk,chosen]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr ((ReceiptDigestTargets.card packet.2).trans (receipt_bytes packet.2))) _

theorem collision_risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    ReceiptCollisionRisk.risk step packet ≤ (packet.2.length : ENNReal)/2^512 := by
  cases chosen : ReceiptCollisionRisk.select step packet with
  | none => simp only [ReceiptCollisionRisk.risk,chosen]; exact zero_le
  | some input =>
    simp only [ReceiptCollisionRisk.risk,chosen]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (ReceiptPayloadView.card packet.2)) _

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) : ENNReal :=
  ParentSeedCollisionRisk.risk step packet + ContextTargetRisk.risk step packet +
    FreshReceiptTargetRisk.risk step packet + ReceiptCollisionRisk.risk step packet

theorem risk_le {S A : Type} (step : S → OracleMachine.Command S A) (packet : (S ⊕ A) × List Observation) :
    risk step packet ≤ ((2*packet.2.length+3*inputWork packet.2 : ℕ) : ENNReal)/2^512 := by
  calc
    _ ≤ (packet.2.length : ENNReal)/2^512 + ((2*inputWork packet.2 : ℕ) : ENNReal)/2^512 +
        (inputWork packet.2 : ENNReal)/2^512 + (packet.2.length : ENNReal)/2^512 :=
      add_le_add (add_le_add (add_le_add (parent_risk step packet) (context_risk step packet)) (fresh_risk step packet)) (collision_risk step packet)
    _ = _ := by simp only [← ENNReal.add_div]; congr 1; push_cast; ring

def lowRisk {S A : Type} (step : S → OracleMachine.Command S A) (threshold : ℕ)
    (packet : (S ⊕ A) × List Observation) : ENNReal :=
  if packet.2.length < threshold ∧ inputWork packet.2 < threshold then risk step packet else 0

def rate (threshold : ℕ) : ENNReal := ((5*threshold : ℕ) : ENNReal)/2^512

theorem lowRisk_le {S A : Type} (step : S → OracleMachine.Command S A) (threshold : ℕ)
    (packet : (S ⊕ A) × List Observation) : lowRisk step threshold packet ≤ rate threshold := by
  unfold lowRisk
  split_ifs with small
  · apply (risk_le step packet).trans
    apply ENNReal.div_le_div_right
    exact Nat.cast_le.mpr (by omega)
  · exact zero_le

theorem lowRisk_absent {S A : Type} (step : S → OracleMachine.Command S A) (threshold : ℕ)
    (packet : (S ⊕ A) × List Observation) (absent : CausalSeedExposure.request step packet.1 = none) :
    lowRisk step threshold packet = 0 := by
  simp [lowRisk,risk,ParentSeedCollisionRisk.risk,ParentSeedCollisionRisk.select,ContextTargetRisk.risk,ContextTargetRisk.select,
    FreshReceiptTargetRisk.risk,FreshReceiptTargetRisk.select,CausalStreamExposure.firstRead,
    ReceiptCollisionRisk.risk,ReceiptCollisionRisk.select,absent]

def totalLowCharge {A : Type} (program : Program A) (threshold : ℕ) (world : World) : ENNReal :=
  ∑' position : ℕ, lowRisk OracleProgramMachine.step threshold (runPrefix position program world).run

theorem total_le_log {A : Type} (program : Program A) (threshold : ℕ) (world : World) :
    totalLowCharge program threshold world ≤ (run program world).run.2.length * rate threshold :=
  ProgramObservationClock.score_sum program world _ _ (lowRisk_le _ threshold) (fun packet => lowRisk_absent _ threshold packet)

theorem closed_charge (code : List ClosedByteMachine.Instruction) (publicData : Input) (threshold fuel : ℕ)
    (state : ClosedByteMachine.State) (world : World) :
    totalLowCharge (ClosedByteMachine.take code publicData fuel state) threshold world ≤
      ((run (ClosedByteMachine.take code publicData fuel state) world).run.1.work : ENNReal)*rate threshold :=
  (total_le_log _ _ _).trans (mul_le_mul' (Nat.cast_le.mpr (ClosedByteMachineLogWork.log_le_work code publicData fuel state world)) le_rfl)

theorem private_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (threshold fuel : ℕ) (state : PrivateCoinByteMachine.State) (world : World) :
    totalLowCharge (PrivateCoinByteMachine.take code publicData tape fuel state) threshold world ≤
      ((run (PrivateCoinByteMachine.take code publicData tape fuel state) world).run.1.work : ENNReal)*rate threshold :=
  (total_le_log _ _ _).trans (mul_le_mul' (Nat.cast_le.mpr (PrivateCoinByteLogWork.log_le_work code publicData tape fuel state world)) le_rfl)

/-- Charges are retained at every actual instruction horizon. -/
def privateLifetimeCharge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (threshold : ℕ) (execution : PrivateCoinReplay.Tape × World) : ENNReal :=
  ⨆ fuel : ℕ, totalLowCharge (PrivateCoinByteMachine.take code publicData execution.1 fuel
    (PrivateCoinByteMachine.initialise code privateData)) threshold execution.2

theorem private_lifetime_charge (code : List PrivateCoinByteMachine.Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (threshold : ℕ) (execution : PrivateCoinReplay.Tape × World) :
    privateLifetimeCharge code publicData privateData threshold execution ≤
      PrivateCoinByteWork.lifetimeWork code publicData privateData execution * rate threshold := by
  apply iSup_le
  intro fuel
  exact (private_charge _ _ _ _ _ _ _).trans (mul_le_mul'
    (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index execution) fuel) le_rfl)

theorem private_expected_charge (coins : MeasureTheory.Measure PrivateCoinReplay.Tape) (code : List PrivateCoinByteMachine.Instruction)
    (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (threshold : ℕ) :
    (∫⁻ execution, privateLifetimeCharge code publicData privateData threshold execution ∂coins.prod InputIndexedOracle.law) ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate threshold := by
  calc
    _ ≤ ∫⁻ execution, PrivateCoinByteWork.lifetimeWork code publicData privateData execution * rate threshold ∂coins.prod InputIndexedOracle.law :=
      MeasureTheory.lintegral_mono (private_lifetime_charge code publicData privateData threshold)
    _ = _ := MeasureTheory.lintegral_mul_const (rate threshold) (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData)

end
end FormalProof4FHE.HasteBoots.ReferenceRiskBudget
