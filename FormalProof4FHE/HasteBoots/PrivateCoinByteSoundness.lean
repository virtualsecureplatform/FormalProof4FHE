module
public import FormalProof4FHE.HasteBoots.PrivateCoinByteAllRisk
@[expose] public section

/-! Executable common-source extraction soundness for runtime private-coin
programs. All four hazard components are paid by the same specified work
counter. This is not a physical-work or complete false-PBS theorem. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteSoundness
open MeasureTheory
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinExecutableSoundness (Target)
open PrivateCoinByteFailure (Failure)
noncomputable section

theorem failure_covered (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target)
    (execution : Tape × World) (failed : Failure Memory code publicData privateData dummy target execution) :
    PrivateCoinByteAllRisk.Failure code publicData execution.1 dummy target.ctx target.primitive target.role
      target.ctx.parent.profile privateData execution.2 := by
  rcases PrivateCoinByteFailure.failure_covered Memory code publicData privateData dummy target execution failed with
    root | ⟨fuel, early | field | column⟩
  · exact Or.inl root
  · exact Or.inr ⟨fuel, Or.inr early⟩
  · exact Or.inr ⟨fuel, Or.inl (Or.inl field)⟩
  · exact Or.inr ⟨fuel, Or.inl (Or.inr column)⟩

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

/-- The tape is independent of the oracle. Its full runtime use, including
local coin-only loops and rejected/aborted paths, remains in expected work. -/
theorem lifetime_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    (coins.prod law) {execution | Failure Memory code publicData privateData dummy target execution} ≤
      PrivateCoinByteAllRisk.rate * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  rw [Measure.prod_apply (PrivateCoinByteFailure.failure_measurable Memory code publicData privateData dummy target)]
  apply (lintegral_mono (fun tape => fixed_lifetime_bound Memory code publicData tape privateData dummy target)).trans_eq
  have sections : Measurable (fun tape => PrivateCoinByteFixed.expectedWork code publicData tape privateData) :=
    (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).lintegral_prod_right'
  rw [lintegral_const_mul _ sections, PrivateCoinByteWork.expectedWork_prod]
  rfl

theorem scaled_lifetime_bound (coins : Measure Tape) (Memory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (target : Target) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory code publicData privateData dummy target execution} ≤
      (9/4096 : ENNReal) * PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  rw [Measure.prod_apply (PrivateCoinByteFailure.failure_measurable Memory code publicData privateData dummy target),
    ← lintegral_const_mul' ((2 : ENNReal)^128) _ (by simp)]
  apply (lintegral_mono (fun tape => fixed_scaled_bound Memory code publicData tape privateData dummy target)).trans_eq
  have sections : Measurable (fun tape => PrivateCoinByteFixed.expectedWork code publicData tape privateData) :=
    (PrivateCoinByteWork.lifetimeWork_measurable code publicData privateData).lintegral_prod_right'
  rw [lintegral_const_mul _ sections, PrivateCoinByteWork.expectedWork_prod]
  rfl
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteSoundness
