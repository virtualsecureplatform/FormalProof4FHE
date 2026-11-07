module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRequest
public import FormalProof4FHE.HasteBoots.ClosedByteMachineWork
public import FormalProof4FHE.HasteBoots.NativeGoldBatchCalibration
@[expose] public section

/-! Calibrated field/column exposure charges on actual closed interpreter
prefixes are paid by its specified instruction work. Silent steps and stopped
stuttering have no exposure charge. This does not price honest verification,
prove application coverage, or refine byte-work prices to physical work. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineGoldRisk
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize Tables)
open NativeBrakedownCalibration (Role radius)
open ClosedByteMachine (Instruction State Tape initialise take tickCost)
open ClosedByteMachineRequest (command)
open MeasureTheory ProbabilityTheory
noncomputable section

abbrev Packet := NativeIndexExposureRisk.Packet State State

def packet (state : State) (log : List NativeTranscript.Observation) : Packet := (.inl state,log)

def risk (code : List Instruction) (publicData : Input) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role) (old : Packet) : ENNReal :=
  NativeGoldBatchFieldProximity.risk dummy ctx primitive (radius .goldilocks role) (command code publicData) old +
    NativeGoldBatchProfileColumnExposure.risk dummy ctx primitive (command code publicData) old (radius .goldilocks role)

def history (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (fuel : ℕ) (world : World) :
    NativeTranscript.Execution (State ⊕ State) :=
  OracleProgram.run (take code publicData fuel (initialise code privateData)) world >>= fun state => pure (.inl state)

theorem history_run (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (fuel : ℕ) (world : World) :
    (history code publicData privateData fuel world).run =
      packet (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1
        (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.2 := by
  rw [history,ObservationReplay.run_bind]
  change (_, _ ++ []) = (_, _)
  rw [List.append_nil]
  rfl

theorem history_replay (code : List Instruction) (publicData : Input) (privateData : Tape → Input) (fuel : ℕ) :
    ObservationReplay.Replayable (history code publicData privateData fuel) :=
  ObservationReplay.bind_replay (ClosedByteMachine.prefix_replay code publicData fuel (initialise code privateData))
    (fun state => ObservationReplay.pure_replay (Sum.inl state : State ⊕ State))

variable (code : List Instruction) (publicData : Input) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role)

theorem risk_no_read (old : Packet) (absent : CausalStreamExposure.firstRead (command code publicData) old = none) :
    risk code publicData dummy ctx primitive role old = 0 := by
  have fieldNone : NativeGoldBatchFieldExposure.select (command code publicData) old = none := by
    rw [NativeGoldBatchFieldExposure.select,absent,Option.bind_none]
  have columnNone : NativeGoldBatchProfileColumnExposure.select ctx (command code publicData) old = none := by
    cases selected : NativeGoldBatchProfileColumnExposure.select ctx (command code publicData) old with
    | none => rfl
    | some decoded =>
      obtain ⟨input,first,_⟩ := NativeGoldBatchProfileColumnExposure.selected_link ctx (command code publicData) old decoded selected
      rw [absent] at first
      contradiction
  simp only [risk,NativeGoldBatchFieldProximity.risk,fieldNone,NativeGoldBatchProfileColumnExposure.risk,columnNone,zero_add]

variable (tables : Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (compatible : NativeGoldBatchCalibration.Matches ctx role)

include constructed compatible in
/-- The price is that of the actual current instruction, with no log-length
proxy or charge for unexecuted future instructions. -/
theorem risk_le_cost (state : State) (log : List NativeTranscript.Observation) :
    risk code publicData dummy ctx primitive role (packet state log) ≤
      ((17 : ENNReal)/2^141) * (tickCost code publicData state : ENNReal) := by
  cases stopped : state.stopped with
  | some stop =>
    have absent : CausalStreamExposure.firstRead (command code publicData) (packet state log) = none := by
      simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,packet,command,stopped]
    rw [risk_no_read code publicData dummy ctx primitive role _ absent]
    exact zero_le
  | none =>
    have positive := ClosedByteMachine.tickCost_pos code publicData state stopped
    have atLeastOne : (1 : ENNReal) ≤ (tickCost code publicData state : ENNReal) :=
      by exact_mod_cast (Nat.succ_le_of_lt positive)
    calc
      _ ≤ (17 : ENNReal)/2^141 :=
        NativeGoldBatchCalibration.risk_bound dummy ctx tables scalarMessage block blowup constructed primitive role compatible _ _
      _ = ((17 : ENNReal)/2^141)*1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul' le_rfl atLeastOne

def totalCharge (privateData : Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk code publicData dummy ctx primitive role (history code publicData privateData fuel world).run

include constructed compatible in
theorem totalCharge_le_work (privateData : Tape → Input) (world : World) :
    totalCharge code publicData dummy ctx primitive role privateData world ≤
      ((17 : ENNReal)/2^141)*ClosedByteMachineWork.lifetimeWork code publicData privateData world := by
  calc
    _ ≤ ∑' fuel : ℕ, ((17 : ENNReal)/2^141) *
        (tickCost code publicData (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      rw [history_run]
      exact risk_le_cost code publicData dummy ctx primitive role tables scalarMessage block blowup constructed compatible _ _
    _ = ((17 : ENNReal)/2^141) * ∑' fuel : ℕ,
        (tickCost code publicData (OracleProgram.run (take code publicData fuel (initialise code privateData)) world).run.1 : ENNReal) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (ClosedByteMachineWork.stepCost_tsum_le code publicData privateData world)

include constructed compatible in
theorem expectedCharge_le_work (privateData : Tape → Input) :
    (∫⁻ world, totalCharge code publicData dummy ctx primitive role privateData world ∂law) ≤
      ((17 : ENNReal)/2^141)*ClosedByteMachineWork.expectedWork code publicData privateData := by
  calc
    _ ≤ ∫⁻ world, ((17 : ENNReal)/2^141)*ClosedByteMachineWork.lifetimeWork code publicData privateData world ∂law :=
      lintegral_mono (totalCharge_le_work code publicData dummy ctx primitive role tables scalarMessage block blowup constructed compatible privateData)
    _ = _ := lintegral_const_mul _ (ClosedByteMachineWork.lifetimeWork_measurable code publicData privateData)

def event (profile : Digest) (old : Packet) (world : World) : Prop :=
  NativeGoldBatchFieldProximity.event dummy ctx primitive (radius .goldilocks role) profile (command code publicData) old world ∨
    NativeGoldBatchProfileColumnExposure.event dummy ctx primitive profile (command code publicData) old (radius .goldilocks role) world

theorem event_measurable (profile : Digest) (privateData : Tape → Input) (fuel : ℕ) :
    MeasurableSet {world | event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world} :=
  (NativeGoldBatchFieldProximity.event_measurable dummy ctx primitive (radius .goldilocks role) profile
    (command code publicData) (history_replay code publicData privateData fuel)).union
      (NativeGoldBatchProfileColumnExposure.event_measurable (history_replay code publicData privateData fuel)
        dummy ctx primitive profile (command code publicData) (radius .goldilocks role))

include constructed compatible in
theorem averaged_event (profile : Digest) (privateData : Tape → Input) (fuel : ℕ) :
    law {world | event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world} ≤
        ∫⁻ world, risk code publicData dummy ctx primitive role (history code publicData privateData fuel world).run ∂law := by
  have replay := history_replay code publicData privateData fuel
  have dimensions := NativeGoldBatchCalibration.radius_valid ctx tables scalarMessage block blowup constructed primitive role compatible
  rw [OracleHistoryComposition.average_event replay law _
    (event_measurable code publicData dummy ctx primitive role profile privateData fuel)]
  apply lintegral_mono
  intro world
  change (law[|{other | (history code publicData privateData fuel other).run =
      (history code publicData privateData fuel world).run}])
    ({other | NativeGoldBatchFieldProximity.event dummy ctx primitive (radius .goldilocks role) profile
      (command code publicData) (history code publicData privateData fuel other).run other} ∪
     {other | NativeGoldBatchProfileColumnExposure.event dummy ctx primitive profile (command code publicData)
      (history code publicData privateData fuel other).run (radius .goldilocks role) other}) ≤ _
  apply (measure_union_le _ _).trans
  exact add_le_add
    (NativeGoldBatchFieldProximity.conditional_bound dummy ctx primitive (radius .goldilocks role) profile
      (command code publicData) replay world dimensions.1 dimensions.2)
    (NativeGoldBatchProfileColumnExposure.conditional_bound replay dummy ctx primitive profile
      (command code publicData) world (radius .goldilocks role))

include constructed compatible in
theorem lifetime_le_charge (profile : Digest) (privateData : Tape → Input) :
    law {world | ∃ fuel, event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world} ≤
        ∫⁻ world, totalCharge code publicData dummy ctx primitive role privateData world ∂law := by
  have union : {world | ∃ fuel, event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | event code publicData dummy ctx primitive role profile
        (history code publicData privateData fuel world).run world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' fuel : ℕ, law {world | event code publicData dummy ctx primitive role profile
        (history code publicData privateData fuel world).run world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, risk code publicData dummy ctx primitive role
        (history code publicData privateData fuel world).run ∂law :=
      ENNReal.tsum_le_tsum (averaged_event code publicData dummy ctx primitive role tables scalarMessage block blowup
        constructed compatible profile privateData)
    _ = _ := (lintegral_tsum (fun fuel =>
      (OracleExecutionLaw.score_measurable (history_replay code publicData privateData fuel)
        (risk code publicData dummy ctx primitive role)).aemeasurable)).symm

include constructed compatible in
/-- A genuine exposure-event/work bound for this closed interpreter. Hash,
receipt and application-coverage obligations are not folded into this event. -/
theorem lifetime_le_work (profile : Digest) (privateData : Tape → Input) :
    law {world | ∃ fuel, event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world} ≤
        ((17 : ENNReal)/2^141)*ClosedByteMachineWork.expectedWork code publicData privateData :=
  (lifetime_le_charge code publicData dummy ctx primitive role tables scalarMessage block blowup
    constructed compatible profile privateData).trans
      (expectedCharge_le_work code publicData dummy ctx primitive role tables scalarMessage block blowup
        constructed compatible privateData)

end
end FormalProof4FHE.HasteBoots.ClosedByteMachineGoldRisk
