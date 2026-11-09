module
import FormalProof4FHE.HasteBoots.PrivateCoinByteConfigurationUnion
import all FormalProof4FHETest.HasteBootsPrivateCoinLineageSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteFixed (history)
namespace HasteBootsRuntimeCoinSoundnessSmoke
noncomputable section
open HasteBootsPrivateCoinLineageSmoke (code empty tape)
open HasteBootsPrivateCoinExecutableSmoke (target dummy pair)

-- A real coin instruction has a positive work cost and zero exposure risk.
example (world : World) : PrivateCoinByteMachine.tickCost code []
    (PrivateCoinByteWork.program code [] empty 3 tape world).run.1 = 2 := by rfl
example (world : World) : PrivateCoinByteGoldRisk.risk code [] tape dummy target.ctx target.primitive target.role
    (history code [] tape empty 3 world).run = 0 := by
  apply PrivateCoinByteGoldRisk.risk_no_read
  rfl
example (world : World) : PrivateCoinByteRootFailure.risk code [] tape dummy
    (history code [] tape empty 3 world).run = 0 := by rfl
example (world : World) (threshold : ℕ) : PrivateCoinByteReceiptWork.lowRisk code [] tape threshold
    (history code [] tape empty 3 world).run = 0 := by
  have absent : NativeEarlyReceiptBound.risk (PrivateCoinByteRequest.command code [] tape)
      (history code [] tape empty 3 world).run = 0 := by
    have selected : NativeEarlyReceiptPrefixRisk.select (PrivateCoinByteRequest.command code [] tape)
        (history code [] tape empty 3 world).run = none := by rfl
    simp only [NativeEarlyReceiptBound.risk, NativeEarlyReceiptPrefixRisk.risk,
      NativeFreshReceiptLifetime.risk, selected, zero_add]
  simp only [PrivateCoinByteReceiptWork.lowRisk, absent, ite_self]

-- Actual input-byte/log budgets retain the SHA-512 prequery, empty read,
-- later positive read and the silent work before them.
example (world : World) : ClosedByteMachineRootBudget.inputWork
    (PrivateCoinByteWork.program code [] empty 9 tape world).run.2 = 4 := by rfl
example (world : World) :
    (PrivateCoinByteWork.program code [] empty 9 tape world).run.2.length ≤
      (PrivateCoinByteWork.program code [] empty 9 tape world).run.1.work :=
  PrivateCoinByteLogWork.log_le_work code [] tape 9 (PrivateCoinByteMachine.initialise code empty) world
example (world : World) :
    NativeRootFamilyHashStep.risk dummy [7] (history code [] tape empty 9 world).run.2 ≤
      ((3*(PrivateCoinByteWork.program code [] empty 9 tape world).run.1.work +
        256*(PrivateCoinByteWork.program code [] empty 9 tape world).run.1.work*
          (PrivateCoinByteWork.program code [] empty 9 tape world).run.1.work : ℕ) : ENNReal)/(2 : ENNReal)^512 :=
  PrivateCoinByteRootBudget.hash_loss_le_work code [] tape 9 (PrivateCoinByteMachine.initialise code empty) world dummy [7]

example : law {world | ∃ fuel, NativeEarlyReceiptBound.event target.ctx.parent.profile
    (PrivateCoinByteRequest.command code [] tape) (history code [] tape empty fuel world).run world} ≤
      (1/(2 : ENNReal)^255) * PrivateCoinByteFixed.expectedWork code [] tape empty :=
  PrivateCoinByteReceiptWork.lifetime_le_255 code [] tape target.ctx.parent.profile empty
example : law {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (history code [] tape empty fuel world).run.2} ≤
    (1/(2 : ENNReal)^159) * PrivateCoinByteFixed.expectedWork code [] tape empty :=
  PrivateCoinByteRootWork.lifetime_le_159 code [] tape dummy empty

-- The per-tape theorem discharges all hazard prices, rather than accepting
-- an assumed failure/work inequality as a calibration premise.
example : (2 : ENNReal)^128 * law {world | PrivateCoinByteFailure.Failure Unit code [] empty dummy target (tape,world)} ≤
    (9/4096 : ENNReal) * PrivateCoinByteFixed.expectedWork code [] tape empty :=
  PrivateCoinByteSoundness.fixed_scaled_bound Unit code [] tape empty dummy target
example (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | PrivateCoinByteFailure.Failure Unit code [] empty dummy target execution} ≤
      (9/4096 : ENNReal) * PrivateCoinByteWork.expectedWork coins code [] empty :=
  PrivateCoinByteSoundness.scaled_lifetime_bound coins Unit code [] empty dummy target

-- Configurations share the actual runtime coin stream and one work counter.
example (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | PrivateCoinByteConfigurationUnion.familyFailure Unit code [] empty dummy pair execution} ≤
        ((2 : ENNReal)*(9/4096)) * PrivateCoinByteWork.expectedWork coins code [] empty := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    PrivateCoinByteConfigurationUnion.scaled_family_le_work coins Unit code [] empty dummy pair
example (coins : Measure Tape) (targets : Fin 256 → PrivateCoinExecutableSoundness.Target) :
    (2 : ENNReal)^128 * (coins.prod law)
      {execution | PrivateCoinByteConfigurationUnion.familyFailure Unit code [] empty dummy targets execution} ≤
        (9/16 : ENNReal) * PrivateCoinByteWork.expectedWork coins code [] empty :=
  PrivateCoinByteConfigurationUnion.configured_allowance coins Unit code [] empty dummy targets
    (by simp only [Fintype.card_fin, Nat.le_refl])
end
end HasteBootsRuntimeCoinSoundnessSmoke
