module
public import FormalProof4FHE.HasteBoots.ProfileMetadataErasure
public import FormalProof4FHE.HasteBoots.PrivateCoinByteSoundness
@[expose] public section

/-! One hazard budget covers every profile metadata value. Actual profile
frames remain in the transcript inputs; only analysis metadata is erased.
This includes profiles computed adaptively from the same oracle history.
Trusted geometry and native acceptance premises remain unchanged. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteAnyProfile
open MeasureTheory
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinExecutableSoundness (Target)
noncomputable section

def withProfile (target : Target) (profile : Digest) : Target :=
  { target with
    ctx := { target.ctx with parent := { target.ctx.parent with profile := profile } }
    compatible := ⟨target.compatible.width, target.compatible.height, target.compatible.message, target.compatible.queries⟩ }

def Failure (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) : Prop :=
  ∃ profile : Digest, PrivateCoinByteFailure.Failure Memory code publicData privateData dummy (withProfile target profile) execution

theorem failure_measurable (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    MeasurableSet {execution | Failure Memory code publicData privateData dummy target execution} := by
  have union : {execution | Failure Memory code publicData privateData dummy target execution} =
      ⋃ profile : Digest, {execution | PrivateCoinByteFailure.Failure Memory code publicData privateData dummy (withProfile target profile) execution} := by
    ext execution
    simp only [Failure, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion fun profile =>
    PrivateCoinByteFailure.failure_measurable Memory code publicData privateData dummy (withProfile target profile)

/-- This coverage step, rather than a union bound over profile identifiers,
allows even oracle-dependent identifiers with the same quantitative loss. -/
theorem failure_covered (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) (failed : Failure Memory code publicData privateData dummy target execution) :
    PrivateCoinByteAllRisk.Failure code publicData execution.1 dummy target.ctx target.primitive target.role
      target.ctx.parent.profile privateData execution.2 := by
  obtain ⟨profile, failed⟩ := failed
  rcases PrivateCoinByteFailure.failure_covered Memory code publicData privateData dummy (withProfile target profile) execution failed with
    root | ⟨fuel, early | field | column⟩
  · exact Or.inl root
  · exact Or.inr ⟨fuel, Or.inr ((ProfileMetadataErasure.receipt_event profile target.ctx.parent.profile _ _ _).mp early)⟩
  · have moved := (NativeGoldBatchEventContext.field_event dummy (withProfile target profile).ctx target.ctx rfl
      (withProfile target profile).primitive target.primitive _ profile _ _ _).mp field
    exact Or.inr ⟨fuel, Or.inl (Or.inl ((ProfileMetadataErasure.field_event dummy target.ctx target.primitive _
      profile target.ctx.parent.profile _ _ _).mp moved))⟩
  · have moved := (NativeGoldBatchEventContext.profile_column_event dummy (withProfile target profile).ctx target.ctx rfl
      (withProfile target profile).primitive target.primitive _ profile _ _ _).mp column
    exact Or.inr ⟨fuel, Or.inl (Or.inr ((ProfileMetadataErasure.profile_column_event dummy target.ctx target.primitive
      profile target.ctx.parent.profile _ _ _ _).mp moved))⟩

theorem fixed_lifetime_bound (Memory : Type) (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    law {world | Failure Memory code publicData privateData dummy target (tape, world)} ≤
      PrivateCoinByteAllRisk.rate * PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  apply (measure_mono (fun world failed => failure_covered Memory code publicData privateData dummy target (tape, world) failed)).trans
  exact PrivateCoinByteAllRisk.lifetime_le_work code publicData tape dummy target.ctx target.tables target.message
    target.block target.blowup target.constructed target.primitive target.role target.compatible target.ctx.parent.profile privateData

theorem fixed_scaled_bound (Memory : Type) (code : List Instruction) (publicData : Input) (tape : Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    (2 : ENNReal)^128 * law {world | Failure Memory code publicData privateData dummy target (tape, world)} ≤
      (9/4096 : ENNReal) * PrivateCoinByteFixed.expectedWork code publicData tape privateData := by
  have computed : (2 : NNReal)^128*((18 : NNReal)/2^141) = 9/4096 := by norm_num
  have nonzero : (2 : NNReal)^141 ≠ 0 := by positivity
  have cast := congrArg (fun value : NNReal => (value : ENNReal)) computed
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div nonzero,
    ENNReal.coe_div (by norm_num : (4096 : NNReal) ≠ 0), ENNReal.coe_ofNat] at cast
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteAllRisk.rate * PrivateCoinByteFixed.expectedWork code publicData tape privateData) :=
      mul_le_mul' le_rfl (fixed_lifetime_bound Memory code publicData tape privateData dummy target)
    _ = ((2 : ENNReal)^128 * PrivateCoinByteAllRisk.rate) * PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
      (mul_assoc _ _ _).symm
    _ ≤ ((2 : ENNReal)^128 * ((18 : ENNReal)/2^141)) * PrivateCoinByteFixed.expectedWork code publicData tape privateData :=
      mul_le_mul' (mul_le_mul' le_rfl PrivateCoinByteAllRisk.rate_le) le_rfl
    _ = _ := by rw [cast]

theorem scaled_lifetime_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory code publicData privateData dummy target execution} ≤
      (9/4096 : ENNReal) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  rw [Measure.prod_apply (failure_measurable Memory code publicData privateData dummy target),
    ← lintegral_const_mul' ((2 : ENNReal)^128) _ (by simp)]
  apply (lintegral_mono (fun tape => fixed_scaled_bound Memory code publicData tape privateData dummy target)).trans_eq
  have sections : Measurable (fun tape => PrivateCoinByteFixed.expectedWork code publicData tape privateData) :=
    (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).lintegral_prod_right'
  rw [lintegral_const_mul _ sections, PrivateCoinByteWork.expectedWork_prod]
  rfl

def FamilyFailure {Index : Type} (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (targets : Index → Target)
    (execution : Tape × World) : Prop := ∃ index, Failure Memory code publicData privateData dummy (targets index) execution

/-- The numerical loss counts parameter targets, never profile identifiers. -/
theorem scaled_family_bound {Index : Type} [Fintype Index] (coins : Measure Tape) (Memory : Type)
    (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (targets : Index → Target) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | FamilyFailure Memory code publicData privateData dummy targets execution} ≤
      ((Fintype.card Index : ENNReal)*(9/4096)) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have union : {execution | FamilyFailure Memory code publicData privateData dummy targets execution} =
      ⋃ index, {execution | Failure Memory code publicData privateData dummy (targets index) execution} := by
    ext execution
    simp only [FamilyFailure, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [union]
  calc
    _ ≤ (2 : ENNReal)^128 * ∑ index, (coins.prod law)
        {execution | Failure Memory code publicData privateData dummy (targets index) execution} :=
      mul_le_mul' le_rfl (measure_iUnion_fintype_le _ _)
    _ = ∑ index, (2 : ENNReal)^128 * (coins.prod law)
        {execution | Failure Memory code publicData privateData dummy (targets index) execution} := by rw [Finset.mul_sum]
    _ ≤ ∑ _index : Index, (9/4096 : ENNReal)*PrivateCoinByteWork.expectedWork coins code publicData privateData :=
      Finset.sum_le_sum fun index _ => scaled_lifetime_bound coins Memory code publicData privateData dummy (targets index)
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

theorem family_work_bound {Index : Type} [Fintype Index] (coins : Measure Tape) (Memory : Type)
    (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input)
    (dummy : Digest) (targets : Index → Target) (bounded : Fintype.card Index ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | FamilyFailure Memory code publicData privateData dummy targets execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  have numeric : (256 : NNReal)*(9/4096) ≤ 1 := by
    apply (NNReal.coe_le_coe).mp
    norm_num
  have allowance := ENNReal.coe_le_coe.mpr numeric
  simp only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4096 : NNReal) ≠ 0), ENNReal.coe_ofNat, ENNReal.coe_one] at allowance
  have cardinal : (Fintype.card Index : ENNReal) ≤ 256 := by exact_mod_cast bounded
  have factor := (mul_le_mul' cardinal (le_refl (9/4096 : ENNReal))).trans allowance
  exact (scaled_family_bound coins Memory code publicData privateData dummy targets).trans
    (by simpa only [one_mul] using mul_le_mul' factor (le_refl (PrivateCoinByteWork.expectedWork coins code publicData privateData)))

end
end FormalProof4FHE.HasteBoots.PrivateCoinByteAnyProfile
