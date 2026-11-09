module
import FormalProof4FHE.HasteBoots.PrivateCoinConfigurationUnion
import all FormalProof4FHETest.HasteBootsPrivateCoinWorkSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinExecutableSoundness (Target Failure)
open PrivateCoinConfigurationUnion (familyFailure)
namespace HasteBootsPrivateCoinExecutableSmoke
noncomputable section
open HasteBootsCalibrationSmoke (ctx tables constructed primitive compatible)
open HasteBootsBatchMeaningSmoke (usize)
open HasteBootsPrivateCoinWorkSmoke (code data data_finite)

def target : Target :=
  ⟨ctx, .helper, tables, usize 2048, usize 4, usize 2, constructed, primitive, compatible⟩
def dummy : NativeRootMessage.Digest := fun _ => 0

def alternate : Target :=
  { target with
    ctx := {ctx with root := fun _ => 1, parent := {ctx.parent with profile := fun _ => 1}}
    compatible := ⟨compatible.width, compatible.height, compatible.message, compatible.queries⟩ }

def pair (index : Fin 2) : Target := if index = 0 then target else alternate
example : (pair 0).ctx.parent.profile ≠ (pair 1).ctx.parent.profile := by
  intro same
  have byte := congrFun same 0
  change (0 : InputIndexedOracle.Byte) = 1 at byte
  exact (by decide : (0 : InputIndexedOracle.Byte) ≠ 1) byte

example : MeasurableSet {execution | Failure Unit code [] data dummy target execution} :=
  PrivateCoinExecutableSoundness.failure_measurable Unit code [] data data_finite dummy target
example (execution : Tape × World) (failed : Failure Unit code [] data dummy target execution) :
    ClosedByteMachineGoldAllRisk.Failure code [] dummy ctx primitive .helper ctx.parent.profile
      (data execution.1) execution.2 :=
  PrivateCoinExecutableSoundness.failure_covered Unit code [] data dummy target execution failed
example (coins : Measure Tape) :
    (coins.prod law) {execution | Failure Unit code [] data dummy target execution} ≤
      ClosedByteMachineGoldAllRisk.rate * PrivateCoinClosedWork.expectedWork coins code [] data :=
  PrivateCoinExecutableSoundness.lifetime_le_work coins Unit code [] data data_finite dummy target
example (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Unit code [] data dummy target execution} ≤
      (9/4096 : ENNReal) * PrivateCoinClosedWork.expectedWork coins code [] data :=
  PrivateCoinExecutableSoundness.scaled_lifetime_le_work coins Unit code [] data data_finite dummy target

-- Families cover configurations on the same execution, with no assumption
-- that different roots or profiles use independent oracle worlds.
example (execution : Tape × World) (failed : Failure Unit code [] data dummy alternate execution) :
    familyFailure Unit code [] data dummy pair execution := ⟨1, failed⟩
example : MeasurableSet {execution | familyFailure Unit code [] data dummy pair execution} :=
  PrivateCoinConfigurationUnion.failure_measurable Unit code [] data data_finite dummy pair
example (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | familyFailure Unit code [] data dummy pair execution} ≤
      ((2 : ENNReal) * (9/4096)) * PrivateCoinClosedWork.expectedWork coins code [] data := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    PrivateCoinConfigurationUnion.scaled_family_le_work coins Unit code [] data data_finite dummy pair

-- Empty and duplicated families have the expected events; indices do not
-- become independent trials or fresh native executions.
example : {execution | familyFailure Unit code [] data dummy (fun _ : Fin 0 => target) execution} = ∅ := by
  ext execution
  simp [familyFailure]
example : {execution | familyFailure Unit code [] data dummy (fun _ : Fin 2 => target) execution} =
    {execution | Failure Unit code [] data dummy target execution} := by
  ext execution
  simp [familyFailure]

-- The numerical allowance is for configured targets, not an execution cap.
example (coins : Measure Tape) (targets : Fin 256 → Target) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | familyFailure Unit code [] data dummy targets execution} ≤
      (9/16 : ENNReal) * PrivateCoinClosedWork.expectedWork coins code [] data :=
  PrivateCoinConfigurationUnion.configured_allowance coins Unit code [] data data_finite dummy targets (by simp only [Fintype.card_fin, Nat.le_refl])
end
end HasteBootsPrivateCoinExecutableSmoke
