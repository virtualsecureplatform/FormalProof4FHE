module
public import FormalProof4FHE.HasteBoots.PrivateCoinClosedWork
public import FormalProof4FHE.HasteBoots.ClosedByteMachineGoldRisk
@[expose] public section

/-! The existing calibrated field/column exposure event is bounded under
private random initialization by unconditional expected specified byte-work.
This event excludes source/hash/receipt exceptions and application coverage;
this is not a false-PBS or native physical-work theorem. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinClosedGoldRisk
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open ClosedByteMachine (Instruction)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (logSize Tables)
open NativeBrakedownCalibration (Role)
noncomputable section

theorem data_fiber_measurable
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (value : ClosedByteMachine.Tape → Input) :
    MeasurableSet {tape | privateData tape = value} := by
  let program (tape : Tape) (_ : World) : NativeTranscript.Execution (ClosedByteMachine.Tape → Input) :=
    pure (privateData tape)
  have finiteResult : PrivateCoinMachine.FiniteResult program := by
    intro tape world
    obtain ⟨count, fixed⟩ := finiteData tape
    exact ⟨count, fun other same => congrArg (fun data => (data, [])) (fixed other same)⟩
  exact (PrivateCoinScores.event_measurable (fun tape => ObservationReplay.pure_replay (privateData tape))
    finiteResult (fun result => result.1 = value)).preimage
      (measurable_id.prodMk ((measurable_const : Measurable (fun _ : Tape => (fun _ => 0 : World)))))

variable (code : List Instruction) (publicData : Input) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(logSize ctx.parameters.code+1))) (role : Role) (profile : Digest)

def event (privateData : Tape → ClosedByteMachine.Tape → Input) (execution : Tape × World) : Prop :=
  ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
    (ClosedByteMachineGoldRisk.history code publicData (privateData execution.1) fuel execution.2).run execution.2

theorem event_measurable (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) :
    MeasurableSet {execution | event code publicData dummy ctx primitive role profile privateData execution} := by
  have equal : {execution | event code publicData dummy ctx primitive role profile privateData execution} =
      ⋃ data : ClosedByteMachine.Tape → Input, {tape | privateData tape = data} ×ˢ
        {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
          (ClosedByteMachineGoldRisk.history code publicData data fuel world).run world} := by
    ext execution
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod]
    constructor
    · intro yes
      exact ⟨privateData execution.1, rfl, yes⟩
    · rintro ⟨data, same, yes⟩
      change ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
        (ClosedByteMachineGoldRisk.history code publicData (privateData execution.1) fuel execution.2).run execution.2
      rwa [same]
  rw [equal]
  apply MeasurableSet.iUnion
  intro data
  apply (data_fiber_measurable privateData finiteData data).prod
  have union : {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
      (ClosedByteMachineGoldRisk.history code publicData data fuel world).run world} =
      ⋃ fuel : ℕ, {world | ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
        (ClosedByteMachineGoldRisk.history code publicData data fuel world).run world} := by
    ext world
    simp
  rw [union]
  exact MeasurableSet.iUnion fun fuel =>
    ClosedByteMachineGoldRisk.event_measurable code publicData dummy ctx primitive role profile data fuel

variable (tables : Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (compatible : NativeGoldBatchCalibration.Matches ctx role)

include constructed compatible in
theorem lifetime_le_work (coins : Measure Tape)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) :
    (coins.prod law) {execution | event code publicData dummy ctx primitive role profile privateData execution} ≤
      ((17 : ENNReal)/2^141) * PrivateCoinClosedWork.expectedWork coins code publicData privateData := by
  have averaged := PrivateCoinLifetime.independent_bound coins _
    (event_measurable code publicData dummy ctx primitive role profile privateData finiteData)
    (fun tape => ((17 : ENNReal)/2^141) * ClosedByteMachineWork.expectedWork code publicData (privateData tape))
    (fun tape => ClosedByteMachineGoldRisk.lifetime_le_work code publicData dummy ctx primitive role
      tables scalarMessage block blowup constructed compatible profile (privateData tape))
  have meansMeasurable : Measurable (fun tape => ClosedByteMachineWork.expectedWork code publicData (privateData tape)) :=
    (PrivateCoinClosedWork.lifetimeWork_measurable code publicData privateData finiteData).lintegral_prod_right'
  rw [lintegral_const_mul _ meansMeasurable,
    ← PrivateCoinClosedWork.expectedWork_prod coins code publicData privateData finiteData] at averaged
  exact averaged

include constructed compatible in
/-- A scaled bound for this exposure component in specified byte-work units.
The full false-PBS event and physical-work calibration remain separate. -/
theorem scaled_exposure_bound (coins : Measure Tape)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | event code publicData dummy ctx primitive role profile privateData execution} ≤
        PrivateCoinClosedWork.expectedWork coins code publicData privateData := by
  have bounded := mul_le_mul' (le_rfl : (2 : ENNReal)^128 ≤ (2 : ENNReal)^128)
    (lifetime_le_work code publicData dummy ctx primitive role profile
      tables scalarMessage block blowup constructed compatible coins privateData finiteData)
  have factor : (2 : ENNReal)^128 * ((17 : ENNReal)/2^141) ≤ 1 := by
    have rational : (2 : NNReal)^128 * (17/2^141) ≤ 1 := by
      change (2 : ℝ)^128 * (17/2^141) ≤ 1
      norm_num
    have cast := ENNReal.coe_le_coe.mpr rational
    have nonzero : (2 : NNReal)^141 ≠ 0 := by positivity
    simpa only [ENNReal.coe_mul, ENNReal.coe_div nonzero, ENNReal.coe_pow, ENNReal.coe_ofNat, ENNReal.coe_one] using cast
  exact bounded.trans (by
    rw [← mul_assoc]
    exact (mul_le_mul' factor le_rfl).trans_eq (one_mul _))
end
end FormalProof4FHE.HasteBoots.PrivateCoinClosedGoldRisk
