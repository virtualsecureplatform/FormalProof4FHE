module
public import FormalProof4FHE.HasteBoots.PrivateCoinExecutableSoundness
@[expose] public section

/-! A finite family of calibrated configurations shares one execution and one
unconditional work expectation. Its size counts configurations, not attacker
trials or lifetime. Binding actual application contexts to this family is a
separate obligation; no configuration coverage premise is silently assumed. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinConfigurationUnion
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinExecutableSoundness (Target Failure)
open NativeRootMessage (Digest)
noncomputable section

def familyFailure {Index : Type} (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input) (dummy : Digest) (targets : Index → Target)
    (execution : Tape × World) : Prop :=
  ∃ index, Failure Memory code publicData privateData dummy (targets index) execution

theorem failure_measurable {Index : Type} [Fintype Index]
    (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (dummy : Digest) (targets : Index → Target) :
    MeasurableSet {execution | familyFailure Memory code publicData privateData dummy targets execution} := by
  have union : {execution | familyFailure Memory code publicData privateData dummy targets execution} =
      ⋃ index, {execution | Failure Memory code publicData privateData dummy (targets index) execution} := by
    ext execution
    simp [familyFailure]
  rw [union]
  exact MeasurableSet.iUnion fun index =>
    PrivateCoinExecutableSoundness.failure_measurable Memory code publicData privateData finiteData dummy (targets index)

/-- All targets share exactly the same initialized code, private tape, oracle
world and expected work. No separate run is charged for each target. -/
theorem scaled_family_le_work {Index : Type} [Fintype Index]
    (coins : Measure Tape) (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (dummy : Digest) (targets : Index → Target) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | familyFailure Memory code publicData privateData dummy targets execution} ≤
        ((Fintype.card Index : ENNReal) * (9/4096)) *
          PrivateCoinClosedWork.expectedWork coins code publicData privateData := by
  have union : {execution | familyFailure Memory code publicData privateData dummy targets execution} =
      ⋃ index, {execution | Failure Memory code publicData privateData dummy (targets index) execution} := by
    ext execution
    simp [familyFailure]
  rw [union]
  calc
    _ ≤ (2 : ENNReal)^128 * ∑ index, (coins.prod law)
        {execution | Failure Memory code publicData privateData dummy (targets index) execution} :=
      mul_le_mul' le_rfl (measure_iUnion_fintype_le _ _)
    _ = ∑ index, (2 : ENNReal)^128 * (coins.prod law)
        {execution | Failure Memory code publicData privateData dummy (targets index) execution} := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _index : Index, (9/4096 : ENNReal) * PrivateCoinClosedWork.expectedWork coins code publicData privateData :=
      Finset.sum_le_sum fun index _ =>
        PrivateCoinExecutableSoundness.scaled_lifetime_le_work coins Memory code publicData privateData finiteData dummy (targets index)
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

/-- A configured family of at most 256 targets fits the existing numerical
allowance for 64 shapes and four roles. This does not prove application
coverage by those targets, and imposes no bound on attempts or execution. -/
theorem configured_allowance {Index : Type} [Fintype Index]
    (coins : Measure Tape) (Memory : Type) (code : List ClosedByteMachine.Instruction) (publicData : Input)
    (privateData : Tape → ClosedByteMachine.Tape → Input)
    (finiteData : PrivateCoinClosedWork.FiniteData privateData) (dummy : Digest) (targets : Index → Target)
    (bounded : Fintype.card Index ≤ 256) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | familyFailure Memory code publicData privateData dummy targets execution} ≤
        (9/16 : ENNReal) * PrivateCoinClosedWork.expectedWork coins code publicData privateData := by
  have numeric : (256 : NNReal) * (9/4096) = 9/16 := by norm_num
  have cast := congrArg (fun value : NNReal => (value : ENNReal)) numeric
  simp only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4096 : NNReal) ≠ 0),
    ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0), ENNReal.coe_ofNat] at cast
  have cardinal : (Fintype.card Index : ENNReal) ≤ 256 := by exact_mod_cast bounded
  have factor : (Fintype.card Index : ENNReal) * (9/4096) ≤ (9/16 : ENNReal) :=
    (mul_le_mul' cardinal le_rfl).trans_eq cast
  exact (scaled_family_le_work coins Memory code publicData privateData finiteData dummy targets).trans
    (mul_le_mul' factor le_rfl)
end
end FormalProof4FHE.HasteBoots.PrivateCoinConfigurationUnion
