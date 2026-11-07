module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineNativeCoverage
@[expose] public section

/-! Native batch analysis-extractor soundness on actual closed instruction
histories, with arbitrary roots/parents/responses/schedulers under fixed public
parameters and profile. Acceptance retains the actual native program/log
inclusion and strict parsed-view premises. This is not public PBS semantics,
efficient extraction, actor-cost separation or native physical refinement. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineNativeSoundness
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (Tables logSize)
open NativeBrakedownCalibration (Role radius)
open ClosedByteMachine (Instruction Tape)
open ClosedByteMachineGoldRisk (history history_replay)
open ClosedByteMachineRequest (command)
open NativeGoldBatchLifetimeSoundness (Witness)
open MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def Failure (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role) (world : World) : Prop :=
  ∃ fuel, Nonempty (Witness Memory dummy ctx (radius .goldilocks role) world (history code publicData privateData fuel world).run.2)

theorem failure_covered (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (compatible : NativeGoldBatchCalibration.Matches ctx role) (world : World)
    (failed : Failure Memory code publicData privateData dummy ctx role world) :
    ClosedByteMachineGoldAllRisk.Failure code publicData dummy ctx primitive role ctx.parent.profile privateData world := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  have candidateConstructed : NativeGoldBlockCode.build tables message block blowup = .ok witness.candidate.parameters.code := by
    rw [witness.sameParameters]
    exact constructed
  have candidateWidth : 3 ≤ witness.candidate.parameters.width.val := by
    rw [witness.sameParameters,compatible.width]
    cases role <;> decide +kernel
  have covered := ClosedByteMachineNativeCoverage.accepted_coverage code publicData privateData fuel world dummy
    witness.candidate witness.work tables message block blowup candidateConstructed witness.primitive witness.choose witness.verifierFuel
    witness.memory witness.decoded witness.parsed witness.responseFits witness.accepted witness.capacity
    (radius .goldilocks role) candidateWidth witness.falseClaim
  rcases covered with different | early | field | column
  · left
    have audit := NativeRootFamilyAudit.disagreement_implies_bad dummy world _
      ((history_replay code publicData privateData fuel).truthful world)
    have decisions : (fun first second : Digest => Fintype.decidablePiFintype first second) =
        (inferInstance : DecidableEq Digest) := Subsingleton.elim _ _
    rw [decisions] at audit
    exact ⟨fuel,audit different⟩
  · obtain ⟨index,_,event⟩ := early
    rw [witness.sameProfile] at event
    exact Or.inr ⟨index,Or.inr event⟩
  · obtain ⟨index,_,event⟩ := field
    have transferred := (NativeGoldBatchEventContext.field_event dummy witness.candidate ctx witness.sameParameters witness.primitive primitive
      (radius .goldilocks role) witness.candidate.parent.profile (command code publicData) _ world).mp event
    rw [witness.sameProfile] at transferred
    exact Or.inr ⟨index,Or.inl (Or.inl transferred)⟩
  · obtain ⟨index,_,event⟩ := column
    have transferred := (NativeGoldBatchEventContext.profile_column_event dummy witness.candidate ctx witness.sameParameters witness.primitive primitive
      (radius .goldilocks role) witness.candidate.parent.profile (command code publicData) _ world).mp event
    rw [witness.sameProfile] at transferred
    exact Or.inr ⟨index,Or.inl (Or.inr transferred)⟩

theorem finite_measurable (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role) (fuel : ℕ) :
    MeasurableSet {world | Nonempty (Witness Memory dummy ctx (radius .goldilocks role) world
      (history code publicData privateData fuel world).run.2)} := by
  have same : {world | Nonempty (Witness Memory dummy ctx (radius .goldilocks role) world
      (history code publicData privateData fuel world).run.2)} =
      {world | NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy ctx (radius .goldilocks role)
        (history code publicData privateData fuel world).run.2} := by
    ext world
    exact NativeGoldBatchLifetimeMeasurable.witness_iff_history Memory dummy ctx (radius .goldilocks role) world _
      ((history_replay code publicData privateData fuel).truthful world)
  rw [same]
  exact OracleExecutionLaw.event_measurable (history_replay code publicData privateData fuel)
    (fun packet => NativeGoldBatchLifetimeMeasurable.HistoryFailure Memory dummy ctx (radius .goldilocks role) packet.2)

theorem failure_measurable (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role) :
    MeasurableSet {world | Failure Memory code publicData privateData dummy ctx role world} := by
  have union : {world | Failure Memory code publicData privateData dummy ctx role world} =
      ⋃ fuel : ℕ, {world | Nonempty (Witness Memory dummy ctx (radius .goldilocks role) world
        (history code publicData privateData fuel world).run.2)} := by ext world; simp only [Failure,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (finite_measurable Memory code publicData privateData dummy ctx role)

theorem lifetime_le_work (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (compatible : NativeGoldBatchCalibration.Matches ctx role) :
    law {world | Failure Memory code publicData privateData dummy ctx role world} ≤
      ClosedByteMachineGoldAllRisk.rate*ClosedByteMachineWork.expectedWork code publicData privateData := by
  apply (measure_mono (failure_covered Memory code publicData privateData dummy ctx role tables message block blowup
    constructed primitive compatible)).trans
  exact ClosedByteMachineGoldAllRisk.lifetime_le_work code publicData dummy ctx tables message block blowup
    constructed primitive role compatible ctx.parent.profile privateData

/-- Quantitative native analysis-claim security in the declared interpreter
units. The claim predicate remains the common-source analysis extractor. -/
theorem scaled_lifetime_le_work (Memory : Type) (code : List Instruction) (publicData : Input) (privateData : Tape → Input)
    (dummy : Digest) (ctx : Context) (role : Role)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (compatible : NativeGoldBatchCalibration.Matches ctx role) :
    (2 : ENNReal)^128 * law {world | Failure Memory code publicData privateData dummy ctx role world} ≤
      (9/4096 : ENNReal)*ClosedByteMachineWork.expectedWork code publicData privateData := by
  have computed : (2 : NNReal)^128*((18 : NNReal)/2^141) = 9/4096 := by norm_num
  have nonzero : (2 : NNReal)^141 ≠ 0 := by positivity
  have cast := congrArg (fun value : NNReal => (value : ENNReal)) computed
  simp only [ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_div nonzero,
    ENNReal.coe_div (by norm_num : (4096 : NNReal) ≠ 0),ENNReal.coe_ofNat] at cast
  calc
    _ ≤ (2 : ENNReal)^128*(ClosedByteMachineGoldAllRisk.rate*ClosedByteMachineWork.expectedWork code publicData privateData) :=
      mul_le_mul' le_rfl (lifetime_le_work Memory code publicData privateData dummy ctx role tables message block blowup constructed primitive compatible)
    _ = ((2 : ENNReal)^128*ClosedByteMachineGoldAllRisk.rate)*ClosedByteMachineWork.expectedWork code publicData privateData :=
      (mul_assoc _ _ _).symm
    _ ≤ ((2 : ENNReal)^128*((18 : ENNReal)/2^141))*ClosedByteMachineWork.expectedWork code publicData privateData :=
      mul_le_mul' (mul_le_mul' le_rfl ClosedByteMachineGoldAllRisk.rate_le) le_rfl
    _ = _ := by rw [cast]

end
end FormalProof4FHE.HasteBoots.ClosedByteMachineNativeSoundness
