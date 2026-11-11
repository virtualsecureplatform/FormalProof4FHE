module
public import FormalProof4FHE.HasteBoots.OriginalSourceJointCoverage
public import FormalProof4FHE.HasteBoots.PrivateCoinByteReceiptWork
@[expose] public section

/-! Early receipts on exact raw program prefixes have a single specified
work charge. A proof-only Markov threshold handles arbitrarily large logs. -/
namespace FormalProof4FHE.HasteBoots.ProgramEarlyReceiptWork
open InputIndexedOracle (Input World law)
open OracleProgram (Program run runPrefix)
open NativeRootMessage (Digest)
open MeasureTheory ProbabilityTheory
noncomputable section

def Occurs {A : Type} (program : Program A) (profile : Digest) (world : World) : Prop :=
  ∃ position, NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world

def lowRisk {A : Type} (threshold : ℕ) (packet : (Program A ⊕ A) × List NativeTranscript.Observation) : ENNReal :=
  if packet.2.length < threshold then NativeEarlyReceiptBound.risk OracleProgramMachine.step packet else 0

def Low {A : Type} (program : Program A) (threshold : ℕ) (profile : Digest) (world : World) : Prop :=
  ∃ position, (runPrefix position program world).run.2.length < threshold ∧
    NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world

def totalCharge {A : Type} (program : Program A) (threshold : ℕ) (world : World) : ENNReal :=
  ∑' position : ℕ, lowRisk threshold (runPrefix position program world).run

theorem score_le {A : Type} (threshold : ℕ) (packet : (Program A ⊕ A) × List NativeTranscript.Observation) :
    lowRisk threshold packet ≤ PrivateCoinByteReceiptWork.rate threshold := by
  unfold lowRisk
  split
  next small =>
    cases chosen : NativeEarlyReceiptPrefixRisk.select OracleProgramMachine.step packet with
    | none =>
      simp only [NativeEarlyReceiptBound.risk,NativeEarlyReceiptPrefixRisk.risk,NativeFreshReceiptLifetime.risk,chosen,zero_add]
      exact zero_le
    | some view =>
      rw [NativeEarlyReceiptBound.risk_selected _ _ view chosen]
      apply add_le_add _ le_rfl
      apply ENNReal.div_le_div_right
      exact Nat.cast_le.mpr ((PrivateCoinByteLogWork.guesses_le_log _ _).trans (Nat.le_of_lt small))
  next => exact zero_le

theorem score_absent {A : Type} (threshold : ℕ) (packet : (Program A ⊕ A) × List NativeTranscript.Observation)
    (absent : CausalSeedExposure.request OracleProgramMachine.step packet.1 = none) : lowRisk threshold packet = 0 := by
  simp only [lowRisk,NativeEarlyReceiptBound.risk,NativeEarlyReceiptPrefixRisk.risk,NativeFreshReceiptLifetime.risk,
    NativeEarlyReceiptPrefixRisk.select,CausalStreamExposure.firstRead,absent,Option.bind_eq_bind,Option.bind_none,zero_add,ite_self]

theorem total_le_log {A : Type} (program : Program A) (threshold : ℕ) (world : World) :
    totalCharge program threshold world ≤ (run program world).run.2.length * PrivateCoinByteReceiptWork.rate threshold :=
  ProgramObservationClock.score_sum program world (lowRisk threshold) _ (score_le threshold) (score_absent threshold)

theorem low_bound {A : Type} (program : Program A) (threshold : ℕ) (profile : Digest) :
    law {world | Low program threshold profile world} ≤ ∫⁻ world, totalCharge program threshold world ∂law := by
  have union : {world | Low program threshold profile world} = ⋃ position : ℕ,
      {world | (runPrefix position program world).run.2.length < threshold ∧
        NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world} := by
    ext world
    simp only [Low,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  calc
    _ ≤ ∑' position : ℕ, law {world | (runPrefix position program world).run.2.length < threshold ∧
        NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world} := measure_iUnion_le _
    _ ≤ ∑' position : ℕ, ∫⁻ world, lowRisk threshold (runPrefix position program world).run ∂law :=
      ENNReal.tsum_le_tsum (fun position => MaskedOracleBound.bound (OracleProgram.prefix_replay position program) id
        (fun packet => packet.2.length < threshold)
        {world | NativeEarlyReceiptBound.event profile OracleProgramMachine.step (runPrefix position program world).run world}
        (NativeEarlyReceiptBound.risk OracleProgramMachine.step)
        (fun world => NativeEarlyReceiptBound.conditional_bound (OracleProgram.prefix_replay position program) profile OracleProgramMachine.step world))
    _ = _ := (lintegral_tsum (fun position => (OracleExecutionLaw.score_measurable (OracleProgram.prefix_replay position program)
      (lowRisk threshold)).aemeasurable)).symm

theorem private_bound (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (fuel threshold : ℕ) (profile : Digest) (positive : 0 < threshold) :
    law {world | Occurs (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) profile world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData *
        (1/(threshold : ENNReal)+PrivateCoinByteReceiptWork.rate threshold) := by
  let program := InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel
  have included : {world | Occurs program profile world} ⊆
      {world | (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world} ∪
      {world | Low program threshold profile world} := by
    rintro world ⟨position,occurred⟩
    by_cases high : (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world
    · exact Or.inl high
    · right
      have growing := OracleProgramMachine.log_prefix_run position program world
      rw [OracleProgramMachine.take_run] at growing
      have entries := growing.length_le.trans (PrivateCoinByteLogWork.log_le_work code publicData tape fuel _ world)
      have below : ((run program world).run.1.work : ENNReal) < (threshold : ENNReal) :=
        lt_of_le_of_lt (le_iSup (fun index => PrivateCoinByteWork.prefixWork code publicData privateData index (tape,world)) fuel) (lt_of_not_ge high)
      exact ⟨position,lt_of_le_of_lt entries (Nat.cast_lt.mp below),occurred⟩
  have high := meas_ge_le_lintegral_div (μ := law)
    (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData).aemeasurable
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive) : (threshold : ENNReal) ≠ 0) (ENNReal.natCast_ne_top threshold)
  have low : law {world | Low program threshold profile world} ≤
      PrivateCoinByteFixed.expectedWork code publicData tape privateData * PrivateCoinByteReceiptWork.rate threshold := by
    apply (low_bound program threshold profile).trans
    calc
      _ ≤ ∫⁻ world, PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world * PrivateCoinByteReceiptWork.rate threshold ∂law := by
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
        PrivateCoinByteFixed.expectedWork code publicData tape privateData * PrivateCoinByteReceiptWork.rate threshold :=
      (measure_union_le _ _).trans (add_le_add high low)
    _ = _ := by rw [mul_add,one_div,div_eq_mul_inv]

end
end FormalProof4FHE.HasteBoots.ProgramEarlyReceiptWork
