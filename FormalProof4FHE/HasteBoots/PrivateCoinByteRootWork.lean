module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRootWork
public import FormalProof4FHE.HasteBoots.PrivateCoinByteRootFailure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
@[expose] public section

/-! Global source/collision first-failure hazards on actual closed instruction prefixes. A work
threshold below is an analysis split, not an execution or query cap. The
interpreter's byte-work still requires native physical refinement. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteRootWork
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinByteMachine (Instruction State initialise take tickCost)
open PrivateCoinReplay (Tape)
open PrivateCoinByteRequest (command)
open PrivateCoinByteFixed (Packet packet history history_run history_replay)
open MeasureTheory ProbabilityTheory
noncomputable section

def packetWork (old : Packet) : ℕ := old.1.elim State.work State.work

def rate (threshold : ℕ) : ENNReal := ((3*threshold+256*threshold*threshold : ℕ) : ENNReal)/2^512

def lowRisk (code : List Instruction) (publicData : Input) (tape : Tape) (threshold : ℕ) (dummy : Digest) (old : Packet) : ENNReal :=
  if packetWork old < threshold then PrivateCoinByteRootFailure.risk code publicData tape dummy old else 0

def lowEvent (code : List Instruction) (publicData : Input) (tape : Tape) (threshold : ℕ) (dummy : Digest) (old : Packet) (world : World) : Prop :=
  packetWork old < threshold ∧ PrivateCoinByteRootFailure.event code publicData tape dummy old world

variable (code : List Instruction) (publicData : Input) (tape : Tape) (threshold : ℕ) (dummy : Digest)

theorem lowRisk_le_cost (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (world : World) :
    lowRisk code publicData tape threshold dummy (history code publicData tape privateData fuel world).run ≤
      rate threshold*(tickCost code publicData (OracleProgram.run
        (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) := by
  let state := (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1
  let before := (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.2
  rw [history_run]
  change (if state.work < threshold then PrivateCoinByteRootFailure.risk code publicData tape dummy (packet state before) else 0) ≤ _
  by_cases small : state.work < threshold
  · simp only [small,ite_true]
    cases selected : PrivateCoinByteRootFailure.select code publicData tape (packet state before) with
    | none => simp only [PrivateCoinByteRootFailure.risk,selected]; exact zero_le
    | some input =>
      have active : state.machine.stopped = none := by
        cases stopped : state.machine.stopped with
        | none => rfl
        | some stop =>
          simp only [PrivateCoinByteRootFailure.select,CausalSeedExposure.request,packet,command,stopped] at selected
          contradiction
      have one : (1 : ENNReal) ≤ (tickCost code publicData state : ENNReal) := by
        exact_mod_cast Nat.succ_le_of_lt (PrivateCoinByteFixed.tickCost_pos code publicData state active)
      simp only [PrivateCoinByteRootFailure.risk,selected,NativeRootFamilyHashStep.risk]
      calc
        _ ≤ ((3*state.work+256*state.work*state.work : ℕ) : ENNReal)/(2 : ENNReal)^512 :=
          PrivateCoinByteRootBudget.hash_loss_le_work code publicData tape fuel (initialise code privateData) world dummy input
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

def totalLowCharge (privateData : ClosedByteMachine.Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, lowRisk code publicData tape threshold dummy (history code publicData tape privateData fuel world).run

theorem totalLowCharge_le_work (privateData : ClosedByteMachine.Tape → Input) (world : World) :
    totalLowCharge code publicData tape threshold dummy privateData world ≤
      rate threshold*PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world := by
  calc
    _ ≤ ∑' fuel : ℕ, rate threshold*(tickCost code publicData
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      exact lowRisk_le_cost code publicData tape threshold dummy privateData fuel world
    _ = rate threshold * ∑' fuel : ℕ, (tickCost code publicData
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) := ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (PrivateCoinByteFixed.stepCost_tsum_le code publicData tape privateData world)

theorem lowEvent_measurable (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    MeasurableSet {world | lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} :=
  (OracleExecutionLaw.event_measurable (history_replay code publicData tape privateData fuel)
    (fun old => packetWork old < threshold)).inter
      (PrivateCoinByteRootFailure.event_measurable (history_replay code publicData tape privateData fuel) code publicData tape dummy)

theorem averaged_lowEvent (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    law {world | lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} ≤
      ∫⁻ world, lowRisk code publicData tape threshold dummy (history code publicData tape privateData fuel world).run ∂law := by
  have replay := history_replay code publicData tape privateData fuel
  rw [OracleHistoryComposition.average_event replay law _ (lowEvent_measurable code publicData tape threshold dummy privateData fuel)]
  apply lintegral_mono
  intro world
  have fixed : (law[|{other | (history code publicData tape privateData fuel other).run = (history code publicData tape privateData fuel world).run}])
      {other | lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel other).run other} =
      (law[|{other | (history code publicData tape privateData fuel other).run = (history code publicData tape privateData fuel world).run}])
      {other | packetWork (history code publicData tape privateData fuel world).run < threshold ∧ PrivateCoinByteRootFailure.event code publicData tape dummy (history code publicData tape privateData fuel other).run other} := by
    apply NativeShakeProjection.conditional_event_congr replay world
    intro other same
    simp only [lowEvent,same]
  change (law[|{other | (history code publicData tape privateData fuel other).run = (history code publicData tape privateData fuel world).run}])
    {other | lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel other).run other} ≤ _
  rw [fixed]
  by_cases small : packetWork (history code publicData tape privateData fuel world).run < threshold
  · simp only [small,true_and,lowRisk,ite_true]
    exact PrivateCoinByteRootFailure.conditional_bound replay code publicData tape dummy world
  · simp only [small,false_and,Set.ofPred_false,measure_empty,lowRisk,ite_false,le_refl]

theorem lowLifetime_le_work (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} ≤
      rate threshold*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have union : {world | ∃ fuel, lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' fuel : ℕ, law {world | lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, lowRisk code publicData tape threshold dummy (history code publicData tape privateData fuel world).run ∂law :=
      ENNReal.tsum_le_tsum (averaged_lowEvent code publicData tape threshold dummy privateData)
    _ = ∫⁻ world, totalLowCharge code publicData tape threshold dummy privateData world ∂law :=
      (lintegral_tsum (fun fuel => (OracleExecutionLaw.score_measurable (history_replay code publicData tape privateData fuel)
        (lowRisk code publicData tape threshold dummy)).aemeasurable)).symm
    _ ≤ ∫⁻ world, rate threshold*PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world ∂law :=
      lintegral_mono (totalLowCharge_le_work code publicData tape threshold dummy privateData)
    _ = _ := lintegral_const_mul _ (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

/-- The actual run is unrestricted. Large-work runs are paid by Markov,
while only the analysis of earlier low-work events uses the threshold. -/
theorem lifetime_le_work (privateData : ClosedByteMachine.Tape → Input) (positive : 0 < threshold) :
    law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} ≤
        (1/(threshold : ENNReal)+rate threshold)*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have cover : {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} ⊆
      {world | (threshold : ENNReal) ≤ PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world} ∪
      {world | ∃ fuel, lowEvent code publicData tape threshold dummy (history code publicData tape privateData fuel world).run world} := by
    rintro world ⟨originalFuel,failed⟩
    obtain ⟨fuel,_,event⟩ := PrivateCoinByteRootFailure.coverage code publicData tape privateData dummy originalFuel world failed
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
      add_le_add high (lowLifetime_le_work code publicData tape threshold dummy privateData)
    _ = _ := by rw [add_mul,one_div,div_eq_mul_inv,mul_comm (PrivateCoinByteFixed.expectedWork code publicData tape privateData)]



theorem lifetime_measurable (privateData : ClosedByteMachine.Tape → Input) :
    MeasurableSet {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} := by
  have union : {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} =
      ⋃ fuel : ℕ, {world | NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} := by ext world; simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => OracleExecutionLaw.event_measurable (history_replay code publicData tape privateData fuel)
    (fun old => NativeRootFamilyLifetime.Bad dummy old.2))

/-- A fixed analysis split, with no restriction on the execution. -/
theorem rate_160 : 1/((2^160 : ℕ) : ENNReal)+rate (2^160) ≤ 1/(2 : ENNReal)^159 :=
  ClosedByteMachineRootWork.rate_160

theorem lifetime_le_159 (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} ≤
      (1/(2 : ENNReal)^159)*PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
  (lifetime_le_work code publicData tape (2^160) dummy privateData (by positivity)).trans
    (mul_le_mul' rate_160 le_rfl)

end
end FormalProof4FHE.HasteBoots.PrivateCoinByteRootWork
