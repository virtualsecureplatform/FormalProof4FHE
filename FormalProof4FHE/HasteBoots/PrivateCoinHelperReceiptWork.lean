module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineReceiptWork
public import FormalProof4FHE.HasteBoots.SingleOpeningEarlyReceiptBound
public import FormalProof4FHE.HasteBoots.PrivateCoinByteLogWork
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
@[expose] public section

/-! Early receipt hazards on actual closed instruction prefixes. A work
threshold below is an analysis split, not an execution or query cap. The
interpreter's byte-work still requires native physical refinement. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinHelperReceiptWork
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinByteMachine (Instruction State initialise take tickCost)
open PrivateCoinReplay (Tape)
open PrivateCoinByteRequest (command)
open PrivateCoinByteFixed (Packet packet history history_run history_replay)
open MeasureTheory ProbabilityTheory
noncomputable section

def packetWork (old : Packet) : ℕ := old.1.elim State.work State.work

def rate (threshold : ℕ) : ENNReal := (threshold : ENNReal)/2^576+1/2^512

def lowRisk (code : List Instruction) (publicData : Input) (tape : Tape) (threshold : ℕ) (old : Packet) : ENNReal :=
  if packetWork old < threshold then SingleOpeningEarlyReceiptBound.risk (command code publicData tape) old else 0

def lowEvent (code : List Instruction) (publicData : Input) (tape : Tape) (threshold : ℕ) (profile : Digest) (old : Packet) (world : World) : Prop :=
  packetWork old < threshold ∧ SingleOpeningEarlyReceiptBound.event profile (command code publicData tape) old world

variable (code : List Instruction) (publicData : Input) (tape : Tape) (threshold : ℕ)

theorem lowRisk_le_cost (state : State) (log : List NativeTranscript.Observation)
    (bounded : log.length ≤ state.work) :
    lowRisk code publicData tape threshold (packet state log) ≤ rate threshold*(tickCost code publicData state : ENNReal) := by
  change (if state.work < threshold then SingleOpeningEarlyReceiptBound.risk (command code publicData tape) (packet state log) else 0) ≤ _
  by_cases small : state.work < threshold
  · simp only [small,ite_true]
    cases selected : SingleOpeningEarlyReceiptPrefixRisk.select (command code publicData tape) (packet state log) with
    | none =>
      simp only [SingleOpeningEarlyReceiptBound.risk,SingleOpeningEarlyReceiptPrefixRisk.risk,SingleOpeningFreshReceiptLifetime.risk,selected,zero_add]
      exact zero_le
    | some view =>
      have active : state.machine.stopped = none := by
        cases stopped : state.machine.stopped with
        | none => rfl
        | some stop =>
          obtain ⟨input,first,_⟩ := SingleOpeningEarlyReceiptPrefixRisk.selected_link (command code publicData tape) (packet state log) view selected
          simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,packet,command,stopped] at first
          contradiction
      have guesses : (NativeReceiptPrefixView.guesses 72 log).card ≤ threshold :=
        (PrivateCoinByteLogWork.guesses_le_log _ _).trans (bounded.trans (Nat.le_of_lt small))
      have one : (1 : ENNReal) ≤ (tickCost code publicData state : ENNReal) := by
        exact_mod_cast Nat.succ_le_of_lt (PrivateCoinByteFixed.tickCost_pos code publicData state active)
      have guessCast : ((NativeReceiptPrefixView.guesses 72 log).card : ENNReal) ≤ (threshold : ENNReal) := by
        exact_mod_cast guesses
      rw [SingleOpeningEarlyReceiptBound.risk_selected _ _ view selected]
      calc
        _ ≤ rate threshold := add_le_add (ENNReal.div_le_div_right guessCast _) le_rfl
        _ = rate threshold*1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul' le_rfl one
  · simp only [small,ite_false]
    exact zero_le

def totalLowCharge (privateData : ClosedByteMachine.Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, lowRisk code publicData tape threshold (history code publicData tape privateData fuel world).run

theorem totalLowCharge_le_work (privateData : ClosedByteMachine.Tape → Input) (world : World) :
    totalLowCharge code publicData tape threshold privateData world ≤
      rate threshold*PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world := by
  calc
    _ ≤ ∑' fuel : ℕ, rate threshold*(tickCost code publicData
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      rw [history_run]
      exact lowRisk_le_cost code publicData tape threshold _ _ (PrivateCoinByteLogWork.log_le_work _ _ _ _ _ _)
    _ = rate threshold * ∑' fuel : ℕ, (tickCost code publicData
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (PrivateCoinByteFixed.stepCost_tsum_le code publicData tape privateData world)

theorem lowEvent_measurable (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    MeasurableSet {world | lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} :=
  (OracleExecutionLaw.event_measurable (history_replay code publicData tape privateData fuel)
    (fun old => packetWork old < threshold)).inter
      (SingleOpeningEarlyReceiptBound.event_measurable (history_replay code publicData tape privateData fuel) profile (command code publicData tape))

theorem averaged_lowEvent (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    law {world | lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} ≤
      ∫⁻ world, lowRisk code publicData tape threshold (history code publicData tape privateData fuel world).run ∂law := by
  have replay := history_replay code publicData tape privateData fuel
  rw [OracleHistoryComposition.average_event replay law _ (lowEvent_measurable code publicData tape threshold profile privateData fuel)]
  apply lintegral_mono
  intro world
  have fixed : (law[|{other | (history code publicData tape privateData fuel other).run = (history code publicData tape privateData fuel world).run}])
      {other | lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel other).run other} =
      (law[|{other | (history code publicData tape privateData fuel other).run = (history code publicData tape privateData fuel world).run}])
      {other | packetWork (history code publicData tape privateData fuel world).run < threshold ∧ SingleOpeningEarlyReceiptBound.event profile (command code publicData tape) (history code publicData tape privateData fuel other).run other} := by
    apply NativeShakeProjection.conditional_event_congr replay world
    intro other same
    simp only [lowEvent,same]
  change (law[|{other | (history code publicData tape privateData fuel other).run = (history code publicData tape privateData fuel world).run}])
    {other | lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel other).run other} ≤ _
  rw [fixed]
  by_cases small : packetWork (history code publicData tape privateData fuel world).run < threshold
  · simp only [small,true_and,lowRisk,ite_true]
    exact SingleOpeningEarlyReceiptBound.conditional_bound replay profile (command code publicData tape) world
  · simp only [small,false_and,Set.ofPred_false,measure_empty,lowRisk,ite_false,le_refl]

theorem lowLifetime_le_work (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} ≤
      rate threshold*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have union : {world | ∃ fuel, lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' fuel : ℕ, law {world | lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, lowRisk code publicData tape threshold (history code publicData tape privateData fuel world).run ∂law :=
      ENNReal.tsum_le_tsum (averaged_lowEvent code publicData tape threshold profile privateData)
    _ = ∫⁻ world, totalLowCharge code publicData tape threshold privateData world ∂law :=
      (lintegral_tsum (fun fuel => (OracleExecutionLaw.score_measurable (history_replay code publicData tape privateData fuel)
        (lowRisk code publicData tape threshold)).aemeasurable)).symm
    _ ≤ ∫⁻ world, rate threshold*PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world ∂law :=
      lintegral_mono (totalLowCharge_le_work code publicData tape threshold privateData)
    _ = _ := lintegral_const_mul _ (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

/-- The actual run is unrestricted. Large-work runs are paid by Markov,
while only the analysis of earlier low-work events uses the threshold. -/
theorem lifetime_le_work (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) (positive : 0 < threshold) :
    law {world | ∃ fuel, SingleOpeningEarlyReceiptBound.event profile (command code publicData tape)
      (history code publicData tape privateData fuel world).run world} ≤
        (1/(threshold : ENNReal)+rate threshold)*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have cover : {world | ∃ fuel, SingleOpeningEarlyReceiptBound.event profile (command code publicData tape)
      (history code publicData tape privateData fuel world).run world} ⊆
      {world | (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world} ∪
      {world | ∃ fuel, lowEvent code publicData tape threshold profile (history code publicData tape privateData fuel world).run world} := by
    rintro world ⟨fuel,event⟩
    by_cases small : packetWork (history code publicData tape privateData fuel world).run < threshold
    · exact Or.inr ⟨fuel,small,event⟩
    · left
      have bigger : threshold ≤ packetWork (history code publicData tape privateData fuel world).run := Nat.le_of_not_gt small
      rw [history_run] at bigger
      exact (Nat.cast_le.mpr bigger).trans
        (le_iSup (fun n => PrivateCoinByteFixed.prefixWork code publicData tape privateData n world) fuel)
  apply (measure_mono cover).trans
  apply (measure_union_le _ _).trans
  have high := meas_ge_le_lintegral_div (μ := law)
    (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData).aemeasurable
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive) : (threshold : ENNReal) ≠ 0) (ENNReal.natCast_ne_top threshold)
  calc
    _ ≤ PrivateCoinByteFixed.expectedWork code publicData tape privateData/(threshold : ENNReal)+
        rate threshold*PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
      add_le_add high (lowLifetime_le_work code publicData tape threshold profile privateData)
    _ = _ := by rw [add_mul,one_div,div_eq_mul_inv,mul_comm (PrivateCoinByteFixed.expectedWork code publicData tape privateData)]

/-- A numerical analysis threshold, never an operational limit. -/
theorem rate_256 : 1/((2^256 : ℕ) : ENNReal)+rate (2^256) ≤ 1/(2 : ENNReal)^255 :=
  ClosedByteMachineReceiptWork.rate_256

theorem lifetime_le_255 (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, SingleOpeningEarlyReceiptBound.event profile (command code publicData tape)
      (history code publicData tape privateData fuel world).run world} ≤
        (1/(2 : ENNReal)^255)*PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
  (lifetime_le_work code publicData tape (2^256) profile privateData (by positivity)).trans
    (mul_le_mul' rate_256 le_rfl)


end
end FormalProof4FHE.HasteBoots.PrivateCoinHelperReceiptWork
