module
public import FormalProof4FHE.HasteBoots.CanonicalIdentityWork
@[expose] public section

/-! Prior and pending seed-quote exceptions share one raw-position charge.
Masking by original log length and a proof-only Markov split bound the cost
without a query, retry, instruction-horizon or dependency-graph cutoff. -/
namespace FormalProof4FHE.HasteBoots.SeedOrderRiskBudget
open InputIndexedOracle (Input World law)
open NativeTranscript (Observation)
open OracleProgram (Program run runPrefix)
open MeasureTheory ProbabilityTheory
noncomputable section

def event {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) (world : World) : Prop :=
  CausalSeedExposure.event step packet world ∨ PendingSeedQuote.event step packet world

def risk {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) : ENNReal :=
  CausalSeedExposure.risk step packet + PendingSeedQuote.risk step packet

def rate (threshold : ℕ) : ENNReal := (threshold : ENNReal)/(2 : ENNReal)^512

theorem guesses_card (log : List Observation) : (NativeChildSeedView.guesses log).card ≤ log.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem risk_le {S A : Type} (step : S → OracleMachine.Command S A) (packet : NativeIndexExposureRisk.Packet S A) :
    risk step packet ≤ ((packet.2.length+1 : ℕ) : ENNReal)/(2 : ENNReal)^512 := by
  unfold risk CausalSeedExposure.risk PendingSeedQuote.risk
  cases selected : CausalSeedExposure.firstRead step packet with
  | none => simp only [zero_add]; exact zero_le
  | some input =>
    have prior : ((NativeChildSeedView.guesses packet.2).card : ENNReal)/(2 : ENNReal)^512 ≤
        (packet.2.length : ENNReal)/(2 : ENNReal)^512 := ENNReal.div_le_div_right (Nat.cast_le.mpr (guesses_card packet.2)) _
    have pending : (match NativeChildSeedView.quote input with | none => (0 : ENNReal) | some _ => 1/(2 : ENNReal)^512) ≤
        1/(2 : ENNReal)^512 := by
      split <;> simp
    apply (add_le_add prior pending).trans
    exact le_of_eq (by rw [← ENNReal.add_div]; norm_cast)

def lowRisk {A : Type} (threshold : ℕ) (packet : (Program A ⊕ A) × List Observation) : ENNReal :=
  if packet.2.length < threshold then risk OracleProgramMachine.step packet else 0

def Low {A : Type} (program : Program A) (threshold : ℕ) (world : World) : Prop :=
  ∃ position, (runPrefix position program world).run.2.length < threshold ∧ event OracleProgramMachine.step (runPrefix position program world).run world

def totalCharge {A : Type} (program : Program A) (threshold : ℕ) (world : World) : ENNReal :=
  ∑' position : ℕ, lowRisk threshold (runPrefix position program world).run

theorem score_le {A : Type} (threshold : ℕ) (packet : (Program A ⊕ A) × List Observation) : lowRisk threshold packet ≤ rate threshold := by
  unfold lowRisk
  split
  next small => exact (risk_le _ _).trans (ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _)
  next => exact zero_le

theorem score_absent {A : Type} (threshold : ℕ) (packet : (Program A ⊕ A) × List Observation)
    (absent : CausalSeedExposure.request OracleProgramMachine.step packet.1 = none) : lowRisk threshold packet = 0 := by
  simp only [lowRisk,risk,CausalSeedExposure.risk,PendingSeedQuote.risk,CausalSeedExposure.firstRead,absent,zero_add,ite_self]

theorem total_le_log {A : Type} (program : Program A) (threshold : ℕ) (world : World) :
    totalCharge program threshold world ≤ (run program world).run.2.length * rate threshold :=
  ProgramObservationClock.score_sum program world (lowRisk threshold) _ (score_le threshold) (score_absent threshold)

theorem bad_iff {A : Type} (program : Program A) (world : World) :
    SeedQuoteOrder.Bad OracleProgramMachine.step program world ↔ ∃ position, event OracleProgramMachine.step (runPrefix position program world).run world := by
  simp only [SeedQuoteOrder.Bad,OracleProgramMachine.take_run,event]

theorem conditional {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World) :
    (law[|{other | (past other).run = (past world).run}]) {other | event step (past other).run other} ≤ risk step (past world).run :=
  (measure_union_le _ _).trans (add_le_add (CausalSeedExposure.conditional_event step replay world).le (PendingSeedQuote.conditional_event step replay world).le)

theorem low_bound {A : Type} (program : Program A) (threshold : ℕ) :
    law {world | Low program threshold world} ≤ ∫⁻ world, totalCharge program threshold world ∂law := by
  have union : {world | Low program threshold world} = ⋃ position : ℕ,
      {world | (runPrefix position program world).run.2.length < threshold ∧ event OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Low,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc
    _ ≤ ∑' position : ℕ, law {world | (runPrefix position program world).run.2.length < threshold ∧
        event OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
    _ ≤ ∑' position : ℕ, ∫⁻ world, lowRisk threshold (runPrefix position program world).run ∂law :=
      ENNReal.tsum_le_tsum (fun position => MaskedOracleBound.bound (OracleProgram.prefix_replay position program) id
        (fun packet => packet.2.length < threshold) {world | event OracleProgramMachine.step (runPrefix position program world).run world}
        (risk OracleProgramMachine.step) (fun world => conditional OracleProgramMachine.step (OracleProgram.prefix_replay position program) world))
    _ = _ := (lintegral_tsum (fun position => (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program)
      (lowRisk threshold)).aemeasurable)).symm

theorem private_bound (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel threshold : ℕ) (positive : 0 < threshold) :
    law {world | SeedQuoteOrder.Bad OracleProgramMachine.step (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * (1/(threshold : ENNReal)+rate threshold) := by
  let program := InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel
  have included : {world | SeedQuoteOrder.Bad OracleProgramMachine.step program world} ⊆
      {world | (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world} ∪ {world | Low program threshold world} := by
    intro world bad
    obtain ⟨position,occurred⟩ := (bad_iff program world).mp bad
    by_cases high : (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world
    · exact Or.inl high
    · right
      have growing := OracleProgramMachine.log_prefix_run position program world
      rw [OracleProgramMachine.take_run] at growing
      have entries := growing.length_le.trans (PrivateCoinByteLogWork.log_le_work code publicData tape fuel _ world)
      have below : ((run program world).run.1.work : ENNReal) < (threshold : ENNReal) :=
        lt_of_le_of_lt (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) (lt_of_not_ge high)
      exact ⟨position,lt_of_le_of_lt entries (Nat.cast_lt.mp below),occurred⟩
  have high := meas_ge_le_lintegral_div (μ := law) (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData).aemeasurable
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive) : (threshold : ENNReal) ≠ 0) (ENNReal.natCast_ne_top threshold)
  have low : law {world | Low program threshold world} ≤ PrivateCoinByteFixed.expectedWork code publicData tape privateData * rate threshold := by
    apply (low_bound program threshold).trans
    calc
      _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * rate threshold ∂law := by
        apply lintegral_mono
        intro world
        apply (total_le_log program threshold world).trans
        apply mul_le_mul' _ le_rfl
        exact (Nat.cast_le.mpr (PrivateCoinByteLogWork.log_le_work code publicData tape fuel _ world)).trans
          (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel)
      _ = _ := lintegral_mul_const _ (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)
  apply (measure_mono included).trans
  calc
    _ ≤ PrivateCoinByteFixed.expectedWork code publicData tape privateData/(threshold : ENNReal) +
        PrivateCoinByteFixed.expectedWork code publicData tape privateData * rate threshold := (measure_union_le _ _).trans (add_le_add high low)
    _ = _ := by rw [mul_add,one_div,div_eq_mul_inv]

end
end FormalProof4FHE.HasteBoots.SeedOrderRiskBudget
