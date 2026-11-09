module
public import FormalProof4FHE.HasteBoots.ClosedByteMachineGoldAllRisk
public import FormalProof4FHE.HasteBoots.PrivateCoinByteRootWork
public import FormalProof4FHE.HasteBoots.PrivateCoinByteReceiptWork
@[expose] public section

/-! All previously identified ideal-oracle hazards on the SAME closed byte
interpreter execution. This is not yet application false-acceptance coverage,
knowledge extraction, actor-cost separation or physical/native refinement. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteAllRisk
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open PrivateCoinByteFixed (history)
open NativeGoldBatchPcsProgram (Context)
open NativeBrakedownCalibration (Role)
open MeasureTheory
noncomputable section

def rate : ENNReal := 1/(2 : ENNReal)^159+((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)

def Failure (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : Role) (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) (world : World) : Prop :=
  (∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2) ∨
  ∃ fuel, PrivateCoinByteGoldRisk.event code publicData tape dummy ctx primitive role profile
    (history code publicData tape privateData fuel world).run world ∨
    NativeEarlyReceiptBound.event profile (PrivateCoinByteRequest.command code publicData tape)
      (history code publicData tape privateData fuel world).run world

theorem failure_measurable (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : Role) (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    MeasurableSet {world | Failure code publicData tape dummy ctx primitive role profile privateData world} := by
  change MeasurableSet ({world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} ∪
    {world | ∃ fuel, PrivateCoinByteGoldRisk.event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (PrivateCoinByteRequest.command code publicData tape)
        (history code publicData tape privateData fuel world).run world})
  apply (PrivateCoinByteRootWork.lifetime_measurable code publicData tape dummy privateData).union
  have union : {world | ∃ fuel, PrivateCoinByteGoldRisk.event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (PrivateCoinByteRequest.command code publicData tape)
        (history code publicData tape privateData fuel world).run world} =
      ⋃ fuel : ℕ, {world | PrivateCoinByteGoldRisk.event code publicData tape dummy ctx primitive role profile
        (history code publicData tape privateData fuel world).run world ∨
        NativeEarlyReceiptBound.event profile (PrivateCoinByteRequest.command code publicData tape)
          (history code publicData tape privateData fuel world).run world} := by ext world; simp
  rw [union]
  exact MeasurableSet.iUnion (fun fuel =>
    (PrivateCoinByteGoldRisk.event_measurable code publicData tape dummy ctx primitive role profile privateData fuel).union
      (NativeEarlyReceiptBound.event_measurable (PrivateCoinByteFixed.history_replay code publicData tape privateData fuel)
        profile (PrivateCoinByteRequest.command code publicData tape)))

theorem lifetime_le_work (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (ctx : Context)
    (tables : NativeGoldBlockCode.Tables) (scalarMessage block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables scalarMessage block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (role : Role) (compatible : NativeGoldBatchCalibration.Matches ctx role) (profile : Digest) (privateData : ClosedByteMachine.Tape → Input) :
    law {world | Failure code publicData tape dummy ctx primitive role profile privateData world} ≤
      rate*PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  change law ({world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code publicData tape privateData fuel world).run.2} ∪
    {world | ∃ fuel, PrivateCoinByteGoldRisk.event code publicData tape dummy ctx primitive role profile
      (history code publicData tape privateData fuel world).run world ∨
      NativeEarlyReceiptBound.event profile (PrivateCoinByteRequest.command code publicData tape)
        (history code publicData tape privateData fuel world).run world}) ≤ _
  apply (measure_union_le _ _).trans
  calc
    _ ≤ (1/(2 : ENNReal)^159)*PrivateCoinByteFixed.expectedWork code publicData tape privateData+
      ((17 : ENNReal)/2^141+1/(2 : ENNReal)^255)*PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
      add_le_add (PrivateCoinByteRootWork.lifetime_le_159 code publicData tape dummy privateData)
        (PrivateCoinByteReceiptWork.gold_exposure_lifetime_le_work code publicData tape dummy ctx tables scalarMessage block blowup
          constructed primitive role compatible profile privateData)
    _ = _ := (add_mul _ _ _).symm

/-- Arithmetic allowance only; application consumption of any finite shape
or role union remains an independent proof obligation. -/
theorem rate_le : rate ≤ (18 : ENNReal)/2^141 :=
  ClosedByteMachineGoldAllRisk.rate_le

end
end FormalProof4FHE.HasteBoots.PrivateCoinByteAllRisk
