module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteFixed
public import FormalProof4FHE.HasteBoots.SingleOpeningCalibration
public import FormalProof4FHE.HasteBoots.PrivateCoinHelperReceiptWork
@[expose] public section

/-! Calibrated field/column exposure charges on actual closed interpreter
prefixes are paid by its specified instruction work. Silent steps and stopped
stuttering have no exposure charge. This does not price honest verification,
prove application coverage, or refine byte-work prices to physical work. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinHelperGoldRisk
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeGoldPcsExecution (Context)
open NativeGoldBlockCode (logSize Tables)
open NativeBrakedownCalibration (Role radius)
open PrivateCoinByteMachine (Instruction State initialise take tickCost)
open PrivateCoinReplay (Tape)
open PrivateCoinByteFixed (Packet packet history history_run history_replay)
open PrivateCoinByteRequest (command)
open MeasureTheory ProbabilityTheory
noncomputable section

def risk (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role) (old : Packet) : ENNReal :=
  SingleOpeningFieldProximity.risk dummy ctx primitive (radius .goldilocks role) (command code publicData tape) old +
    SingleOpeningProfileColumnExposure.risk dummy ctx primitive (command code publicData tape) old (radius .goldilocks role)

variable (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (role : Role)

theorem risk_no_read (old : Packet) (absent : CausalStreamExposure.firstRead (command code publicData tape) old = none) :
    risk code publicData tape dummy ctx primitive role old = 0 := by
  have fieldNone : SingleOpeningFieldExposure.select (command code publicData tape) old = none := by
    rw [SingleOpeningFieldExposure.select,absent,Option.bind_none]
  have columnNone : SingleOpeningProfileColumnExposure.select ctx (command code publicData tape) old = none := by
    cases selected : SingleOpeningProfileColumnExposure.select ctx (command code publicData tape) old with
    | none => rfl
    | some decoded =>
      obtain ⟨input,first,_⟩ := SingleOpeningProfileColumnExposure.selected_link ctx (command code publicData tape) old decoded selected
      rw [absent] at first
      contradiction
  simp only [risk,SingleOpeningFieldProximity.risk,fieldNone,SingleOpeningProfileColumnExposure.risk,columnNone,zero_add]

variable (origin : CacheBackedSingleOpening.Origin ctx) (compatible : SingleOpeningCalibration.Matches ctx role)

include origin compatible in
/-- The price is that of the actual current instruction, with no log-length
proxy or charge for unexecuted future instructions. -/
theorem risk_le_cost (state : State) (log : List NativeTranscript.Observation) :
    risk code publicData tape dummy ctx primitive role (packet state log) ≤
      ((17 : ENNReal)/2^141) * (tickCost code publicData state : ENNReal) := by
  cases stopped : state.machine.stopped with
  | some stop =>
    have absent : CausalStreamExposure.firstRead (command code publicData tape) (packet state log) = none := by
      simp only [CausalStreamExposure.firstRead,CausalSeedExposure.request,packet,command,stopped]
    rw [risk_no_read code publicData tape dummy ctx primitive role _ absent]
    exact zero_le
  | none =>
    have positive := PrivateCoinByteFixed.tickCost_pos code publicData state stopped
    have atLeastOne : (1 : ENNReal) ≤ (tickCost code publicData state : ENNReal) :=
      by exact_mod_cast (Nat.succ_le_of_lt positive)
    calc
      _ ≤ (17 : ENNReal)/2^141 :=
        SingleOpeningCalibration.risk_bound dummy ctx origin role compatible _ _
      _ = ((17 : ENNReal)/2^141)*1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul' le_rfl atLeastOne

def totalCharge (privateData : ClosedByteMachine.Tape → Input) (world : World) : ENNReal :=
  ∑' fuel : ℕ, risk code publicData tape dummy ctx primitive role (history code publicData tape privateData fuel world).run

include origin compatible in
theorem totalCharge_le_work (privateData : ClosedByteMachine.Tape → Input) (world : World) :
    totalCharge code publicData tape dummy ctx primitive role privateData world ≤
      ((17 : ENNReal)/2^141)*PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world := by
  calc
    _ ≤ ∑' fuel : ℕ, ((17 : ENNReal)/2^141) *
        (tickCost code publicData (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) := by
      apply ENNReal.tsum_le_tsum
      intro fuel
      rw [history_run]
      exact risk_le_cost code publicData tape dummy ctx primitive role origin compatible _ _
    _ = ((17 : ENNReal)/2^141) * ∑' fuel : ℕ,
        (tickCost code publicData (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1 : ENNReal) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (PrivateCoinByteFixed.stepCost_tsum_le code publicData tape privateData world)

include origin compatible in
theorem expectedCharge_le_work (privateData : ClosedByteMachine.Tape → Input) :
    (∫⁻ world, totalCharge code publicData tape dummy ctx primitive role privateData world ∂law) ≤
      ((17 : ENNReal)/2^141)*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  calc
    _ ≤ ∫⁻ world, ((17 : ENNReal)/2^141)*PrivateCoinByteFixed.lifetimeWork code publicData tape privateData world ∂law :=
      lintegral_mono (totalCharge_le_work code publicData tape dummy ctx primitive role origin compatible privateData)
    _ = _ := lintegral_const_mul _ (PrivateCoinByteFixed.lifetimeWork_measurable code publicData tape privateData)

def event (profile : Digest) (old : Packet) (world : World) : Prop :=
  SingleOpeningFieldProximity.event dummy ctx primitive (radius .goldilocks role) profile (command code publicData tape) old world ∨
    SingleOpeningProfileColumnExposure.event dummy ctx primitive profile (command code publicData tape) old (radius .goldilocks role) world

theorem event_measurable (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    MeasurableSet {world | event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world} :=
  (SingleOpeningFieldProximity.event_measurable dummy ctx primitive (radius .goldilocks role) profile
    (command code publicData tape) (history_replay code publicData tape privateData fuel)).union
      (SingleOpeningProfileColumnExposure.event_measurable (history_replay code publicData tape privateData fuel)
        dummy ctx primitive profile (command code publicData tape) (radius .goldilocks role))

include origin compatible in
theorem averaged_event (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) :
    law {world | event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world} ≤
        ∫⁻ world, risk code publicData tape dummy ctx primitive role (history code publicData tape privateData fuel world).run ∂law := by
  have replay := history_replay code publicData tape privateData fuel
  have dimensions := SingleOpeningCalibration.radius_valid ctx origin role compatible
  rw [OracleHistoryComposition.average_event replay law _
    (event_measurable code publicData tape dummy ctx primitive role profile privateData fuel)]
  apply lintegral_mono
  intro world
  change (law[|{other | (history code publicData tape privateData fuel other).run =
      (history code publicData tape privateData fuel world).run}])
    ({other | SingleOpeningFieldProximity.event dummy ctx primitive (radius .goldilocks role) profile
      (command code publicData tape) (history code publicData tape privateData fuel other).run other} ∪
     {other | SingleOpeningProfileColumnExposure.event dummy ctx primitive profile (command code publicData tape)
      (history code publicData tape privateData fuel other).run (radius .goldilocks role) other}) ≤ _
  apply (measure_union_le _ _).trans
  exact add_le_add
    (SingleOpeningFieldProximity.conditional_bound dummy ctx primitive (radius .goldilocks role) profile
      (command code publicData tape) replay world dimensions.1 dimensions.2)
    (SingleOpeningProfileColumnExposure.conditional_bound replay dummy ctx primitive profile
      (command code publicData tape) world (radius .goldilocks role))

include origin compatible in
theorem lifetime_le_charge (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world} ≤
        ∫⁻ world, totalCharge code publicData tape dummy ctx primitive role privateData world ∂law := by
  have union : {world | ∃ fuel, event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | event code publicData tape dummy ctx primitive role profile
        (history code publicData tape privateData fuel world).run world} := by ext world; simp
  rw [union]
  calc
    _ ≤ ∑' fuel : ℕ, law {world | event code publicData tape dummy ctx primitive role profile
        (history code publicData tape privateData fuel world).run world} := measure_iUnion_le _
    _ ≤ ∑' fuel : ℕ, ∫⁻ world, risk code publicData tape dummy ctx primitive role
        (history code publicData tape privateData fuel world).run ∂law :=
      ENNReal.tsum_le_tsum (averaged_event code publicData tape dummy ctx primitive role origin compatible profile privateData)
    _ = _ := (lintegral_tsum (fun fuel =>
      (OracleExecutionLaw.score_measurable (history_replay code publicData tape privateData fuel)
        (risk code publicData tape dummy ctx primitive role)).aemeasurable)).symm

include origin compatible in
/-- A genuine exposure-event/work bound for this closed interpreter. Hash,
receipt and application-coverage obligations are not folded into this event. -/
theorem lifetime_le_work (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world} ≤
        ((17 : ENNReal)/2^141)*PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
  (lifetime_le_charge code publicData tape dummy ctx primitive role origin compatible profile privateData).trans
      (expectedCharge_le_work code publicData tape dummy ctx primitive role origin compatible privateData)

include origin compatible in
theorem exposure_lifetime_le_work (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    law {world | ∃ fuel, event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world ∨
      SingleOpeningEarlyReceiptBound.event profile (command code publicData tape)
        (history code publicData tape privateData fuel world).run world} ≤
      ((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have included : {world | ∃ fuel, event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world ∨
      SingleOpeningEarlyReceiptBound.event profile (command code publicData tape)
        (history code publicData tape privateData fuel world).run world} ⊆
      {world | ∃ fuel, event code publicData tape dummy ctx primitive role profile
        (history code publicData tape privateData fuel world).run world} ∪
      {world | ∃ fuel, SingleOpeningEarlyReceiptBound.event profile (command code publicData tape)
        (history code publicData tape privateData fuel world).run world} := by
    rintro world ⟨fuel,exposure | receipt⟩
    · exact Or.inl ⟨fuel,exposure⟩
    · exact Or.inr ⟨fuel,receipt⟩
  apply (measure_mono included).trans
  calc
    _ ≤ ((17 : ENNReal)/2^141)*PrivateCoinByteFixed.expectedWork code publicData tape privateData +
        (1/(2 : ENNReal)^255)*PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
      (measure_union_le _ _).trans (add_le_add
        (lifetime_le_work code publicData tape dummy ctx primitive role origin compatible profile privateData)
        (PrivateCoinHelperReceiptWork.lifetime_le_255 code publicData tape profile privateData))
    _ = _ := (add_mul _ _ _).symm

end
end FormalProof4FHE.HasteBoots.PrivateCoinHelperGoldRisk
