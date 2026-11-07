module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineRootWork
public import FormalProof4FHE.HasteBoots.ClosedByteMachineReceiptWork
@[expose] public section

/-! All previously identified ideal-oracle hazards on the SAME closed byte
interpreter execution. This is not yet application false-acceptance coverage,
knowledge extraction, actor-cost separation or physical/native refinement. -/
namespace FormalProof4FHE.HasteBoots.ClosedByteMachineGoldAllRisk
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open ClosedByteMachine (Instruction Tape)
open ClosedByteMachineGoldRisk (history)
open NativeGoldBatchPcsProgram (Context)
open NativeBrakedownCalibration (Role)
open MeasureTheory
noncomputable section

def rate : ENNReal := 1/(2 : ENNReal)^159+((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)

def Failure (code : List Instruction) (publicData : Input) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : Role) (profile : Digest) (privateData : Tape → Input) (world : World) : Prop :=
  (∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2) ∨
  ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
    (history code publicData privateData fuel world).run world ∨
    NativeEarlyReceiptBound.event profile (ClosedByteMachineRequest.command code publicData)
      (history code publicData privateData fuel world).run world

theorem failure_measurable (code : List Instruction) (publicData : Input) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : Role) (profile : Digest) (privateData : Tape → Input) :
    MeasurableSet {world | Failure code publicData dummy ctx primitive role profile privateData world} := by
  change MeasurableSet ({world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} ∪
    {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (ClosedByteMachineRequest.command code publicData)
        (history code publicData privateData fuel world).run world})
  apply (ClosedByteMachineRootWork.lifetime_measurable code publicData dummy privateData).union
  have union : {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (ClosedByteMachineRequest.command code publicData)
        (history code publicData privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
        (history code publicData privateData fuel world).run world ∨
        NativeEarlyReceiptBound.event profile (ClosedByteMachineRequest.command code publicData)
          (history code publicData privateData fuel world).run world} := by ext world; simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel =>
    (ClosedByteMachineGoldRisk.event_measurable code publicData dummy ctx primitive role profile privateData fuel).union
      (NativeEarlyReceiptBound.event_measurable (ClosedByteMachineGoldRisk.history_replay code publicData privateData fuel)
        profile (ClosedByteMachineRequest.command code publicData)))

theorem lifetime_le_work (code : List Instruction) (publicData : Input) (dummy : Digest) (ctx : Context)
    (tables : NativeGoldBlockCode.Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : Role) (compatible : NativeGoldBatchCalibration.Matches ctx role) (profile : Digest) (privateData : Tape → Input) :
    law {world | Failure code publicData dummy ctx primitive role profile privateData world} ≤
      rate*ClosedByteMachineWork.expectedWork code publicData privateData := by
  change law ({world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData privateData fuel world).run.2} ∪
    {world | ∃ fuel, ClosedByteMachineGoldRisk.event code publicData dummy ctx primitive role profile
      (history code publicData privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (ClosedByteMachineRequest.command code publicData)
        (history code publicData privateData fuel world).run world}) ≤ _
  apply (measure_union_le _ _).trans
  calc
    _ ≤ (1/(2 : ENNReal)^159)*ClosedByteMachineWork.expectedWork code publicData privateData+
      ((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)*ClosedByteMachineWork.expectedWork code publicData privateData :=
      add_le_add (ClosedByteMachineRootWork.lifetime_le_159 code publicData dummy privateData)
        (ClosedByteMachineReceiptWork.gold_exposure_lifetime_le_work code publicData dummy ctx tables scalarMessage block blowup
          constructed primitive role compatible profile privateData)
    _ = _ := (add_mul _ _ _).symm

/-- Arithmetic allowance only; application consumption of any finite shape
or role union remains an independent proof obligation. -/
theorem rate_le : rate ≤ (18 : ENNReal)/2^141 := by
  have bound : (1 : NNReal)/2^159+((17 : NNReal)/2^141+1/(2 : NNReal)^255) ≤ (18 : NNReal)/2^141 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  have nonzero : (2 : NNReal) ≠ 0 := by norm_num
  have cast := ENNReal.coe_le_coe.mpr bound
  simpa only [rate,ENNReal.coe_add,ENNReal.coe_div (pow_ne_zero 159 nonzero),
    ENNReal.coe_div (pow_ne_zero 141 nonzero),ENNReal.coe_div (pow_ne_zero 255 nonzero),
    ENNReal.coe_pow,ENNReal.coe_one,ENNReal.coe_ofNat] using cast

/-- Numerical allowance for a 64-shape/four-role union. This is not an
application coverage theorem and is not an attacker trial or lifetime cap. -/
theorem shape_role_allowance : (2 : ENNReal)^128*(64*4*rate) ≤ 9/16 := by
  have computed : (2 : NNReal)^128*(64*4*((18 : NNReal)/2^141)) = 9/16 := by norm_num
  have nonzero : (2 : NNReal)^141 ≠ 0 := by positivity
  have cast := congrArg (fun value : NNReal => (value : ENNReal)) computed
  simp only [ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_div nonzero,
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0),ENNReal.coe_ofNat] at cast
  calc
    _ ≤ (2 : ENNReal)^128*(64*4*((18 : ENNReal)/2^141)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le)
    _ = _ := cast

end
end FormalProof4FHE.HasteBoots.ClosedByteMachineGoldAllRisk
