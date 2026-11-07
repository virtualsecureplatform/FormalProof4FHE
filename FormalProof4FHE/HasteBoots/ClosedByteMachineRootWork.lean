module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRootFailure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
@[expose] public section

/-! Global source/collision first-failure hazards on actual closed instruction prefixes. A work
threshold below is an analysis split, not an execution or query cap. The
interpreter's byte-work still requires native physical refinement. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineRootWork
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open ClosedByteMachine (Instruction State Tape initialise take tickCost)
open ClosedByteMachineRequest (command)
open ClosedByteMachineGoldRisk (Packet packet history history_run history_replay)
open MeasureTheory ProbabilityTheory
noncomputable section

def packetWork (old : Packet) : ℕ := old.1.elim State.work State.work

def rate (threshold : ℕ) : ENNReal := ((3*threshold+256*threshold*threshold : ℕ) : ENNReal)/2^512

def lowRisk (code : List Instruction) (publicData : Input) (threshold : ℕ) (dummy : Digest) (old : Packet) : ENNReal :=
  if packetWork old < threshold then ClosedByteMachineRootFailure.risk code publicData dummy old else 0

def lowEvent (code : List Instruction) (publicData : Input) (threshold : ℕ) (dummy : Digest) (old : Packet) (world : World) : Prop :=
  packetWork old < threshold ∧ ClosedByteMachineRootFailure.event code publicData dummy old world

variable (code : List Instruction) (publicData : Input) (threshold : ℕ) (dummy : Digest)

theorem lowRisk_le_cost (privateData : Tape → Input) (fuel : ℕ) (world : World) :
    lowRisk code publicData threshold dummy (history code publicData privateData fuel world).run ≤
      rate threshold*(tickCost code publicData (OracleProgram.run
        (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) := by
  let state := (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1
  let before := (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.2
  rw [history_run]
  change (if state.work < threshold then ClosedByteMachineRootFailure.risk code publicData dummy (packet state before) else 0) ≤ _
  by_cases small : state.work < threshold
  · simp only [small,ite_true]
    cases selected : ClosedByteMachineRootFailure.select code publicData (packet state before) with
    | none => simp only [ClosedByteMachineRootFailure.risk,selected]; exact zero_le
    | some input =>
      have active : state.stopped = none := by
        cases stopped : state.stopped with
        | none => rfl
        | some stop =>
          simp only [ClosedByteMachineRootFailure.select,CausalSeedExposure.request,packet,command,stopped] at selected
          contradiction
      have one : (1 : ENNReal) ≤ (tickCost code publicData state : ENNReal) := by
        exact_mod_cast Nat.succ_le_of_lt (ClosedByteMachine.tickCost_pos code publicData state active)
      simp only [ClosedByteMachineRootFailure.risk,selected,NativeRootFamilyHashStep.risk]
      calc
        _ ≤ ((3*state.work+256*state.work*state.work : ℕ) : ENNReal)/(2 : ENNReal)^512 :=
          ClosedByteMachineRootBudget.hash_loss_le_work code publicData fuel (initialise code privateData) world dummy input
        _ ≤ rate threshold := by
          apply ENNReal.div_le_div_right
          apply Nat.cast_le.mpr
          have ordered := Nat.le_of_lt small
          have square := Nat.mul_le_mul ordered ordered
          nlinarith
        _ = rate threshold*1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul' le_rfl one
  · simp only [small,ite_false]
    exact zero_le

def totalLowCharge (privateData : Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, lowRisk code publicData threshold dummy (history code publicData privateData fuel world).run

theorem totalLowCharge_le_work (privateData : Tape → Input) (world : World) :
    totalLowCharge code publicData threshold dummy privateData world ≤
      rate threshold*ClosedByteMachineWork.lifetimeWork code publicData privateData world := by
  calc
    _ ≤ ∑' fuel : ℕ, rate threshold*(tickCost code publicData
        (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      exact lowRisk_le_cost code publicData threshold dummy privateData fuel world
    _ = rate threshold * ∑' fuel : ℕ, (tickCost code publicData
        (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (ClosedByteMachineWork.stepCost_tsum_le code publicData privateData world)

theorem lowEvent_measurable (privateData : Tape → Input) (fuel : ℕ) :
    MeasurableSet {world | lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} :=
  (OracleExecutionLaw.event_measurable (history_replay code publicData privateData fuel)
    (fun old => packetWork old < threshold)).inter
      (ClosedByteMachineRootFailure.event_measurable (history_replay code publicData privateData fuel) code publicData dummy)

theorem averaged_lowEvent (privateData : Tape → Input) (fuel : ℕ) :
    law {world | lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} ≤
      ∫⁻ world, lowRisk code publicData threshold dummy (history code publicData privateData fuel world).run ∂law := by
  have replay := history_replay code publicData privateData fuel
  rw [OracleHistoryComposition.average_event replay law _ (lowEvent_measurable code publicData threshold dummy privateData fuel)]
  apply lintegral_mono
  intro world
  have fixed : (law[|{other | (history code publicData privateData fuel other).run = (history code publicData privateData fuel world).run}])
      {other | lowEvent code publicData threshold dummy (history code publicData privateData fuel other).run other} =
      (law[|{other | (history code publicData privateData fuel other).run = (history code publicData privateData fuel world).run}])
      {other | packetWork (history code publicData privateData fuel world).run < threshold ∧ ClosedByteMachineRootFailure.event code publicData dummy (history code publicData privateData fuel other).run other} := by
    apply NativeShakeProjection.conditional_event_congr replay world
    intro other same
    simp only [lowEvent,same]
  change (law[|{other | (history code publicData privateData fuel other).run = (history code publicData privateData fuel world).run}])
    {other | lowEvent code publicData threshold dummy (history code publicData privateData fuel other).run other} ≤ _
  rw [fixed]
  by_cases small : packetWork (history code publicData privateData fuel world).run < threshold
  · simp only [small,true_and,lowRisk,ite_true]
    exact ClosedByteMachineRootFailure.conditional_bound replay code publicData dummy world
  · simp only [small,false_and,Set.ofPred_false,measure_empty,lowRisk,ite_false,le_refl]

theorem lowLifetime_le_work (privateData : Tape → Input) :
    law {world | ∃ fuel, lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} ≤
      rate threshold*ClosedByteMachineWork.expectedWork code publicData privateData := by
  have union : {world | ∃ fuel, lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' fuel : ℕ, law {world | lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, lowRisk code publicData threshold dummy (history code publicData privateData fuel world).run ∂law :=
      ENNReal.tsum_le_tsum (averaged_lowEvent code publicData threshold dummy privateData)
    _ = ∫⁻ world, totalLowCharge code publicData threshold dummy privateData world ∂law :=
      (lintegral_tsum (fun fuel => (OracleExecutionLaw.score_measurable (history_replay code publicData privateData fuel)
        (lowRisk code publicData threshold dummy)).aemeasurable)).symm
    _ ≤ ∫⁻ world, rate threshold*ClosedByteMachineWork.lifetimeWork code publicData privateData world ∂law :=
      lintegral_mono (totalLowCharge_le_work code publicData threshold dummy privateData)
    _ = _ := lintegral_const_mul _ (ClosedByteMachineWork.lifetimeWork_measurable code publicData privateData)

/-- The actual run is unrestricted. Large-work runs are paid by Markov,
while only the analysis of earlier low-work events uses the threshold. -/
theorem lifetime_le_work (privateData : Tape → Input) (positive : 0 < threshold) :
    law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} ≤
        (1/(threshold : ENNReal)+rate threshold)*ClosedByteMachineWork.expectedWork code publicData privateData := by
  have cover : {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} ⊆
      {world | (threshold : ENNReal) ≤ ClosedByteMachineWork.lifetimeWork code publicData privateData world} ∪
      {world | ∃ fuel, lowEvent code publicData threshold dummy (history code publicData privateData fuel world).run world} := by
    rintro world ⟨originalFuel,failed⟩
    obtain ⟨fuel,_,event⟩ := ClosedByteMachineRootFailure.coverage code publicData privateData dummy originalFuel world failed
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
      add_le_add high (lowLifetime_le_work code publicData threshold dummy privateData)
    _ = _ := by rw [add_mul,one_div,div_eq_mul_inv,mul_comm (ClosedByteMachineWork.expectedWork code publicData privateData)]



theorem lifetime_measurable (privateData : Tape → Input) :
    MeasurableSet {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} := by
  have union : {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} =
      ⋃ fuel : ℕ, {world | NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} := by ext world; simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => OracleExecutionLaw.event_measurable (history_replay code publicData privateData fuel)
    (fun old => NativeRootFamilyLifetime.Bad dummy old.2))

/-- A fixed analysis split, with no restriction on the execution. -/
theorem rate_160 : 1/((2^160 : ℕ) : ENNReal)+rate (2^160) ≤ 1/(2 : ENNReal)^159 := by
  have bound : (1 : NNReal)/2^160 + (3*(2 : NNReal)^160+256*(2 : NNReal)^160*(2 : NNReal)^160)/2^512 ≤
      1/(2 : NNReal)^159 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [show (2 : ℝ)^512 = ((2 : ℝ)^128)^4 by rw [← pow_mul]]
    norm_num
  have nonzero : (2 : NNReal) ≠ 0 := by norm_num
  have cast := ENNReal.coe_le_coe.mpr bound
  simp only [ENNReal.coe_add,ENNReal.coe_mul,ENNReal.coe_div (pow_ne_zero 160 nonzero),
    ENNReal.coe_div (pow_ne_zero 512 nonzero),ENNReal.coe_div (pow_ne_zero 159 nonzero),
    ENNReal.coe_pow,ENNReal.coe_one,ENNReal.coe_ofNat] at cast
  simpa only [rate,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using cast

theorem lifetime_le_159 (privateData : Tape → Input) :
    law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} ≤
      (1/(2 : ENNReal)^159)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  (lifetime_le_work code publicData (2^160) dummy privateData (by positivity)).trans
    (mul_le_mul' rate_160 le_rfl)

end
end FormalProof4FHE.HasteBoots.ClosedByteMachineRootWork
