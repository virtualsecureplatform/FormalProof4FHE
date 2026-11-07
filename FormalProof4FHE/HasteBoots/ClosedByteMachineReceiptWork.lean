module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineLogWork
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
@[expose] public section

/-! Early receipt hazards on actual closed instruction prefixes. A work
threshold below is an analysis split, not an execution or query cap. The
interpreter's byte-work still requires native physical refinement. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineReceiptWork
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open ClosedByteMachine (Instruction State Tape initialise take tickCost)
open ClosedByteMachineRequest (command)
open ClosedByteMachineGoldRisk (Packet packet history history_run history_replay)
open MeasureTheory ProbabilityTheory
noncomputable section

def packetWork (old : Packet) : ℕ := old.1.elim State.work State.work

def rate (threshold : ℕ) : ENNReal := (threshold : ENNReal)/2^576+1/2^512

def lowRisk (code : List Instruction) (publicData : Input) (threshold : ℕ) (old : Packet) : ENNReal :=
  if packetWork old < threshold then NativeEarlyReceiptBound.risk (command code publicData) old else 0

def lowEvent (code : List Instruction) (publicData : Input) (threshold : ℕ) (profile : Digest) (old : Packet) (world : World) : Prop :=
  packetWork old < threshold ∧ NativeEarlyReceiptBound.event profile (command code publicData) old world

variable (code : List Instruction) (publicData : Input) (threshold : ℕ)

theorem lowRisk_le_cost (state : State) (log : List NativeTranscript.Observation)
    (bounded : log.length ≤ state.work) :
    lowRisk code publicData threshold (packet state log) ≤ rate threshold*(tickCost code publicData state : ENNReal) := by
  change (if state.work < threshold then NativeEarlyReceiptBound.risk (command code publicData) (packet state log) else 0) ≤ _
  by_cases small : state.work < threshold
  · simp only [small,ite_true]
    cases selected : NativeEarlyReceiptPrefixRisk.select (command code publicData) (packet state log) with
    | none =>
      simp only [NativeEarlyReceiptBound.risk,NativeEarlyReceiptPrefixRisk.risk,NativeFreshReceiptLifetime.risk,selected,zero_add]
      exact zero_le
    | some view =>
      have active : state.stopped = none := by
        cases stopped : state.stopped with
        | none => rfl
        | some stop =>
          obtain ⟨input,first,_⟩ := NativeEarlyReceiptPrefixRisk.selected_link (command code publicData) (packet state log) view selected
          simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,packet,command,stopped] at first
          contradiction
      have guesses : (NativeReceiptPrefixView.guesses 72 log).card ≤ threshold :=
        (ClosedByteMachineLogWork.guesses_le_log _ _).trans (bounded.trans (Nat.le_of_lt small))
      have one : (1 : ENNReal) ≤ (tickCost code publicData state : ENNReal) := by
        exact_mod_cast Nat.succ_le_of_lt (ClosedByteMachine.tickCost_pos code publicData state active)
      have guessCast : ((NativeReceiptPrefixView.guesses 72 log).card : ENNReal) ≤ (threshold : ENNReal) := by
        exact_mod_cast guesses
      rw [NativeEarlyReceiptBound.risk_selected _ _ view selected]
      calc
        _ ≤ rate threshold := add_le_add (ENNReal.div_le_div_right guessCast _) le_rfl
        _ = rate threshold*1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul' le_rfl one
  · simp only [small,ite_false]
    exact zero_le

def totalLowCharge (privateData : Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, lowRisk code publicData threshold (history code publicData privateData fuel world).run

theorem totalLowCharge_le_work (privateData : Tape → Input) (world : World) :
    totalLowCharge code publicData threshold privateData world ≤
      rate threshold*ClosedByteMachineWork.lifetimeWork code publicData privateData world := by
  calc
    _ ≤ ∑' fuel : ℕ, rate threshold*(tickCost code publicData
        (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      rw [history_run]
      exact lowRisk_le_cost code publicData threshold _ _ (ClosedByteMachineLogWork.log_le_work _ _ _ _ _)
    _ = rate threshold * ∑' fuel : ℕ, (tickCost code publicData
        (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (ClosedByteMachineWork.stepCost_tsum_le code publicData privateData world)

theorem lowEvent_measurable (profile : Digest) (privateData : Tape → Input) (fuel : ℕ) :
    MeasurableSet {world | lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} :=
  (OracleExecutionLaw.event_measurable (history_replay code publicData privateData fuel)
    (fun old => packetWork old < threshold)).inter
      (NativeEarlyReceiptBound.event_measurable (history_replay code publicData privateData fuel) profile (command code publicData))

theorem averaged_lowEvent (profile : Digest) (privateData : Tape → Input) (fuel : ℕ) :
    law {world | lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} ≤
      ∫⁻ world, lowRisk code publicData threshold (history code publicData privateData fuel world).run ∂law := by
  have replay := history_replay code publicData privateData fuel
  rw [OracleHistoryComposition.average_event replay law _ (lowEvent_measurable code publicData threshold profile privateData fuel)]
  apply lintegral_mono
  intro world
  have fixed : (law[|{other | (history code publicData privateData fuel other).run = (history code publicData privateData fuel world).run}])
      {other | lowEvent code publicData threshold profile (history code publicData privateData fuel other).run other} =
      (law[|{other | (history code publicData privateData fuel other).run = (history code publicData privateData fuel world).run}])
      {other | packetWork (history code publicData privateData fuel world).run < threshold ∧ NativeEarlyReceiptBound.event profile (command code publicData) (history code publicData privateData fuel other).run other} := by
    apply NativeShakeProjection.conditional_event_congr replay world
    intro other same
    simp only [lowEvent,same]
  change (law[|{other | (history code publicData privateData fuel other).run = (history code publicData privateData fuel world).run}])
    {other | lowEvent code publicData threshold profile (history code publicData privateData fuel other).run other} ≤ _
  rw [fixed]
  by_cases small : packetWork (history code publicData privateData fuel world).run < threshold
  · simp only [small,true_and,lowRisk,ite_true]
    exact NativeEarlyReceiptBound.conditional_bound replay profile (command code publicData) world
  · simp only [small,false_and,Set.ofPred_false,measure_empty,lowRisk,ite_false,le_refl]

theorem lowLifetime_le_work (profile : Digest) (privateData : Tape → Input) :
    law {world | ∃ fuel, lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} ≤
      rate threshold*ClosedByteMachineWork.expectedWork code publicData privateData := by
  have union : {world | ∃ fuel, lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' fuel : ℕ, law {world | lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, lowRisk code publicData threshold (history code publicData privateData fuel world).run ∂law :=
      ENNReal.tsum_le_tsum (averaged_lowEvent code publicData threshold profile privateData)
    _ = ∫⁻ world, totalLowCharge code publicData threshold privateData world ∂law :=
      (lintegral_tsum (fun fuel => (OracleExecutionLaw.score_measurable (history_replay code publicData privateData fuel)
        (lowRisk code publicData threshold)).aemeasurable)).symm
    _ ≤ ∫⁻ world, rate threshold*ClosedByteMachineWork.lifetimeWork code publicData privateData world ∂law :=
      lintegral_mono (totalLowCharge_le_work code publicData threshold privateData)
    _ = _ := lintegral_const_mul _ (ClosedByteMachineWork.lifetimeWork_measurable code publicData privateData)

/-- The actual run is unrestricted. Large-work runs are paid by Markov,
while only the analysis of earlier low-work events uses the threshold. -/
theorem lifetime_le_work (profile : Digest) (privateData : Tape → Input) (positive : 0 < threshold) :
    law {world | ∃ fuel, NativeEarlyReceiptBound.event profile (command code publicData)
      (history code publicData privateData fuel world).run world} ≤
        (1/(threshold : ENNReal)+rate threshold)*ClosedByteMachineWork.expectedWork code publicData privateData := by
  have cover : {world | ∃ fuel, NativeEarlyReceiptBound.event profile (command code publicData)
      (history code publicData privateData fuel world).run world} ⊆
      {world | (threshold : ENNReal) ≤ ClosedByteMachineWork.lifetimeWork code publicData privateData world} ∪
      {world | ∃ fuel, lowEvent code publicData threshold profile (history code publicData privateData fuel world).run world} := by
    rintro world ⟨fuel,event⟩
    by_cases small : packetWork (history code publicData privateData fuel world).run < threshold
    · exact Or.inr ⟨fuel,small,event⟩
    · left
      have bigger : threshold ≤ packetWork (history code publicData privateData fuel world).run := Nat.le_of_not_gt small
      rw [history_run] at bigger
      exact (Nat.cast_le.mpr bigger).trans
        (le_iSup (fun n => ClosedByteMachineWork.prefixWork code publicData privateData n world) fuel)
  apply (measure_mono cover).trans
  apply (measure_union_le _ _).trans
  have high := meas_ge_le_lintegral_div (μ := law)
    (ClosedByteMachineWork.lifetimeWork_measurable code publicData privateData).aemeasurable
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive) : (threshold : ENNReal) ≠ 0) (ENNReal.natCast_ne_top threshold)
  calc
    _ ≤ ClosedByteMachineWork.expectedWork code publicData privateData/(threshold : ENNReal)+
        rate threshold*ClosedByteMachineWork.expectedWork code publicData privateData :=
      add_le_add high (lowLifetime_le_work code publicData threshold profile privateData)
    _ = _ := by rw [add_mul,one_div,div_eq_mul_inv,mul_comm (ClosedByteMachineWork.expectedWork code publicData privateData)]

/-- A numerical analysis threshold, never an operational limit. -/
theorem rate_256 : 1/((2^256 : ℕ) : ENNReal)+rate (2^256) ≤ 1/(2 : ENNReal)^255 := by
  have bound : (1 : NNReal)/2^256 + ((2 : NNReal)^256/2^576+1/2^512) ≤ 1/(2 : NNReal)^255 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [show (2 : ℝ)^576 = ((2 : ℝ)^192)^3 by rw [← pow_mul],
      show (2 : ℝ)^512 = ((2 : ℝ)^128)^4 by rw [← pow_mul]]
    norm_num
  have nonzero : (2 : NNReal) ≠ 0 := by norm_num
  have cast := ENNReal.coe_le_coe.mpr bound
  simp only [ENNReal.coe_add,ENNReal.coe_div (pow_ne_zero 256 nonzero),
    ENNReal.coe_div (pow_ne_zero 576 nonzero),ENNReal.coe_div (pow_ne_zero 512 nonzero),
    ENNReal.coe_div (pow_ne_zero 255 nonzero),ENNReal.coe_pow,ENNReal.coe_one,ENNReal.coe_ofNat] at cast
  simpa only [rate,Nat.cast_pow,Nat.cast_ofNat] using cast

theorem lifetime_le_255 (profile : Digest) (privateData : Tape → Input) :
    law {world | ∃ fuel, NativeEarlyReceiptBound.event profile (command code publicData)
      (history code publicData privateData fuel world).run world} ≤
        (1/(2 : ENNReal)^255)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  (lifetime_le_work code publicData (2^256) profile privateData (by positivity)).trans
    (mul_le_mul' rate_256 le_rfl)


/-- All three exposure components on the same actual instruction prefixes.
Root/source hazards and full application coverage remain separate. -/
theorem gold_exposure_lifetime_le_work (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (tables : NativeGoldBlockCode.Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : NativeBrakedownCalibration.Role) (compatible : NativeGoldBatchCalibration.Matches ctx role)
    (profile : Digest) (privateData : Tape → Input) :
    law {world | ∃ fuel,
      ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
        (history code publicData privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (command code publicData)
        (history code publicData privateData fuel world).run world} ≤
      ((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)*ClosedByteMachineWork.expectedWork code publicData privateData := by
  have union : {world | ∃ fuel,
      ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
        (history code publicData privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (command code publicData)
        (history code publicData privateData fuel world).run world} =
      {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
        (history code publicData privateData fuel world).run world} ∪
      {world | ∃ fuel, NativeEarlyReceiptBound.event profile (command code publicData)
        (history code publicData privateData fuel world).run world} := by
    ext world
    simp only [Set.mem_ofPred_eq,Set.mem_union,exists_or]
  rw [union]
  apply (measure_union_le _ _).trans
  calc
    _ ≤ ((17 : ENNReal)/2^141)*ClosedByteMachineWork.expectedWork code publicData privateData+
        (1/(2 : ENNReal)^255)*ClosedByteMachineWork.expectedWork code publicData privateData :=
      add_le_add (ClosedByteMachineGoldRisk.lifetime_le_work code publicData dummy ctx primitive role tables
        scalarMessage block blowup constructed compatible profile privateData)
        (lifetime_le_255 code publicData profile privateData)
    _ = _ := (add_mul _ _ _).symm

end
end FormalProof4FHE.HasteBoots.ClosedByteMachineReceiptWork
