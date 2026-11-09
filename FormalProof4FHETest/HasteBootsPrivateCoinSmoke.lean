module
import FormalProof4FHE.HasteBoots.PrivateCoinLifetime
import all FormalProof4FHETest.HasteBootsLifetimeSoundnessSmoke
open FormalProof4FHE.HasteBoots MeasureTheory
open InputIndexedOracle (World law)
namespace HasteBootsPrivateCoinSmoke
noncomputable section

-- Exact averaging: a coin-independent event incurs no multiplicity factor.
example {Coins : Type} [MeasurableSpace Coins] (coins : Measure Coins)
    [IsProbabilityMeasure coins] (event : Set World) :
    (coins.prod law) (Set.univ ×ˢ event) = law event := by
  simp

-- A nonconstant coin event retains its actual probability, not its support size.
def coinLaw : Measure Bool :=
  (1 / 4 : ENNReal) • Measure.dirac false + (3 / 4 : ENNReal) • Measure.dirac true
example : (coinLaw.prod law) ({true} ×ˢ Set.univ) = (3 / 4 : ENNReal) := by
  simp [coinLaw]

-- Countably infinite support needs no externally supplied joint measurability.
open HasteBootsBatchMeaningSmoke (ctx root primitive usize)
open HasteBootsLifetimeSoundnessSmoke (nativePrelude stopped)
local instance : NeZero ctx.parameters.code.blockWidth.val := ⟨by decide +kernel⟩
def before (coin : ℕ) : OracleProgram.Program (NativeGoldBatchPcsProgram.Outcome Unit) :=
  .read [77] coin 1 (fun _ => nativePrelude)
example : MeasurableSet (PrivateCoinLifetime.failure Unit root ctx 0 before (fun _ => stopped)) :=
  PrivateCoinLifetime.failure_measurable_countable Unit root ctx 0 before (fun _ => stopped)
example (coins : Measure ℕ) :
    (coins.prod law) (PrivateCoinLifetime.failure Unit root ctx 0 before (fun _ => stopped)) ≤
      ∫⁻ coin, PrivateCoinLifetime.charge root ctx primitive 0 before (fun _ => stopped) coin ∂coins :=
  PrivateCoinLifetime.prelude_bound coins Unit root ctx primitive ctx.tables (usize 2) (usize 4) (usize 2)
    HasteBootsBatchMeaningSmoke.constructed 0 (by decide +kernel) before (fun _ => stopped)
    Fintype.card_pos (by rw [BlockCode.minDist _ _ _ (by decide +kernel)]; decide +kernel)
    (PrivateCoinLifetime.failure_measurable_countable Unit root ctx 0 before (fun _ => stopped))

-- An infinite Boolean tape with its product sigma algebra, rather than a
-- discrete space of tapes. Selection of the first bit is measurable.
def selectedBefore (bit : Bool) := before (if bit then 1 else 0)
example : MeasurableSet (PrivateCoinLifetime.failure Unit root ctx 0
    (fun tape : ℕ → Bool => selectedBefore (tape 0)) (fun _ => stopped)) :=
  PrivateCoinLifetime.failure_measurable_selection Unit root ctx 0
    (fun tape : ℕ → Bool => tape 0) (measurable_pi_apply 0) selectedBefore (fun _ => stopped)

-- Arbitrary (possibly uncountable) tapes are supported with joint measurability.
-- The scale survives averaging; the physical-work calibration is assumed here.
example {Coins : Type} [MeasurableSpace Coins] (coins : Measure Coins)
    (event : Set (Coins × World)) (joint : MeasurableSet event)
    (work : Coins × World → ENNReal) (workMeasurable : AEMeasurable work (coins.prod law))
    (calibrated : ∀ coin, (2 : ENNReal)^128 * law {w | (coin,w) ∈ event} ≤
      ∫⁻ w, work (coin,w) ∂law) :
    (2 : ENNReal)^128 * (coins.prod law) event ≤ ∫⁻ e, work e ∂coins.prod law :=
  PrivateCoinLifetime.independent_scaled_work_bound coins event joint _ (by simp) work workMeasurable calibrated
end
end HasteBootsPrivateCoinSmoke
