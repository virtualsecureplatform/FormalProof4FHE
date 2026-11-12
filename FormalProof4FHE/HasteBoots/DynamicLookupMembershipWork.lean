module
public import FormalProof4FHE.HasteBoots.LookupAssemblyScope
public import FormalProof4FHE.HasteBoots.LookupPcsFamilyInclusion
@[expose] public section

/-! Dynamic proof/caller templates within one fixed original assembly scope
retain the 128-bit specified-work membership bound. Source-family inclusion
is pointwise; there is no probability union over possible templates/proofs. -/
namespace FormalProof4FHE.HasteBoots.DynamicLookupMembershipWork
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeBrakedownCalibration (Role)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open LookupAssemblyScope (Scope View SourceIndex source sourceOrigin sourceRole)
open MeasureTheory
noncomputable section

def Failure (Memory : Type) (scope : Scope) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (execution : Tape × World) : Prop :=
  ∃ fuel, ∃ view : View scope, Nonempty (LookupMembershipWork.Witness (Memory := Memory) view.ctx view.allocation
    (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

variable (Memory : Type) (scope : Scope) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (target : NativeGoldPcsExecution.Context) (parameters : scope.anchor.helper = target.parameters)
    (profile : scope.anchor.parent.profile = target.transcript.profile) (helperRole : Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (roles : Fin scope.anchor.registry.val.length → Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context scope.anchor slot) (roles slot))
include parameters profile helperAdmitted sourceAdmitted

theorem covered (execution : Tape × World) (failed : Failure Memory scope code publicData privateData dummy execution) :
    (∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution) ∨
      (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
      (∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
      PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (source scope) (sourceOrigin scope)
        (NativeBrakedownCalibration.radius .goldilocks helperRole)
        (fun index => NativeBrakedownCalibration.radius .goldilocks (sourceRole roles index)) execution := by
  obtain ⟨fuel,view,witness⟩ := failed
  have helperParameters := (LookupAssemblyScope.helper view).trans parameters
  have helperWidth : view.ctx.helper.width.val ≤ 4 := by
    rw [helperParameters,helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have admitted (slot : Fin view.ctx.registry.val.length) := LookupAssemblyScope.source_admitted roles sourceAdmitted ⟨view,slot⟩
  have sourceWidths (slot : Fin view.ctx.registry.val.length) : (view.ctx.registry.val.get slot).parameters.width.val ≤ 4 := by
    change (source scope ⟨view,slot⟩).parameters.width.val ≤ 4
    rw [(admitted slot).width]
    cases sourceRole roles ⟨view,slot⟩ <;> decide +kernel
  rcases LookupMembershipWork.covered Memory view.ctx view.allocation code publicData privateData dummy target helperParameters
      (view.profile.trans profile) helperRole helperAdmitted (fun slot => sourceRole roles ⟨view,slot⟩) admitted
      helperWidth sourceWidths execution ⟨fuel,witness⟩ with seed | challenge | reference | pcs
  · exact Or.inl seed
  · exact Or.inr (Or.inl challenge)
  · exact Or.inr (Or.inr (Or.inl reference))
  · exact Or.inr (Or.inr (Or.inr (LookupPcsFamilyInclusion.include_family Memory Memory code publicData privateData dummy target
      (source scope) (sourceOrigin scope) (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun index => NativeBrakedownCalibration.radius .goldilocks (sourceRole roles index)) (fun slot => ⟨view,slot⟩) execution pcs)))

theorem bound (coins : Measure Tape) :
    (coins.prod law) {execution | Failure Memory scope code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupMembershipWork.rate := by
  let allocation := scope.allocation
  let anchor := scope.anchor
  let helperOrigin := AllocatedOpeningLifetimeBound.helperOrigin anchor allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled target parameters
  have width : 3 ≤ target.parameters.width.val := by
    rw [helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have included : {execution | Failure Memory scope code publicData privateData dummy execution} ⊆
      {execution | ∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
        (∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (source scope) (sourceOrigin scope)
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun index => NativeBrakedownCalibration.radius .goldilocks (sourceRole roles index)) execution} := by
    intro execution failed
    exact covered Memory scope code publicData privateData dummy target parameters profile helperRole helperAdmitted roles sourceAdmitted execution failed
  apply (measure_mono included).trans ((measure_union_le _ _).trans ?_)
  apply (add_le_add (PrivateCoinSeedOrderProbability.lifetime_le_159 coins code publicData privateData)
    (CanonicalAllLookupJointWorkBound.bound Memory Memory code publicData privateData dummy scope.anchor.parent.profile target helperOrigin helperRole
      helperAdmitted width (source scope) (sourceOrigin scope) (sourceRole roles) (LookupAssemblyScope.source_admitted roles sourceAdmitted)
      (LookupAssemblyScope.profiles scope) coins)).trans
  exact le_of_eq (by rw [LookupMembershipWork.rate,mul_add,add_comm])

theorem work_128 (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory scope code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * LookupMembershipWork.rate) :=
      mul_le_mul' le_rfl (bound Memory scope code publicData privateData dummy target parameters profile helperRole helperAdmitted roles sourceAdmitted coins)
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^128)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl LookupMembershipWork.rate_le_128)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^128*(1/(2 : ENNReal)^128)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.DynamicLookupMembershipWork
