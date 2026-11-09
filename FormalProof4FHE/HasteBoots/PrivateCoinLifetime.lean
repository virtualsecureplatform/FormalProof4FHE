module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeMeasurable
public import Mathlib.MeasureTheory.Measure.Prod
@[expose] public section

/-! Independent private randomness is integrated, without a union bound over
coins or a bound on continuation length. Joint measurability is an explicit
obligation: measurability of each oracle section alone does not imply it.
The resulting charges still need calibration to actual attacker work. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinLifetime
open MeasureTheory
open InputIndexedOracle (World law)
open OracleProgram (Program run)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCode (Tables logSize)
open NativeRootMessage (Digest)
noncomputable section

/-- The coin space may include an entire infinite private random tape. The
product law states independence from the ideal oracle. -/
theorem independent_bound {Coins : Type*} [MeasurableSpace Coins]
    (coins : Measure Coins) (event : Set (Coins × World))
    (measurable : MeasurableSet event) (charge : Coins → ENNReal)
    (conditional : ∀ coin, law {world | (coin, world) ∈ event} ≤ charge coin) :
    (coins.prod law) event ≤ ∫⁻ coin, charge coin ∂coins := by
  rw [Measure.prod_apply measurable]
  exact lintegral_mono conditional

/-- Calibration must include all work on the same execution, including failed
and aborted executions. No conditional-on-success expectation is used. -/
theorem independent_work_bound {Coins : Type*} [MeasurableSpace Coins]
    (coins : Measure Coins) (event : Set (Coins × World))
    (measurable : MeasurableSet event) (work : Coins × World → ENNReal)
    (workMeasurable : AEMeasurable work (coins.prod law))
    (conditional : ∀ coin, law {world | (coin, world) ∈ event} ≤
      ∫⁻ world, work (coin, world) ∂law) :
    (coins.prod law) event ≤ ∫⁻ execution, work execution ∂coins.prod law := by
  rw [lintegral_prod work workMeasurable]
  exact independent_bound coins event measurable _ conditional

/-- A finite scaling factor, including the intended 128-bit factor, commutes
with private-coin averaging. The per-coin work inequality is a hypothesis. -/
theorem independent_scaled_work_bound {Coins : Type*} [MeasurableSpace Coins]
    (coins : Measure Coins) (event : Set (Coins × World))
    (measurable : MeasurableSet event) (scale : ENNReal) (finite : scale ≠ ⊤)
    (work : Coins × World → ENNReal)
    (workMeasurable : AEMeasurable work (coins.prod law))
    (conditional : ∀ coin, scale * law {world | (coin, world) ∈ event} ≤
      ∫⁻ world, work (coin, world) ∂law) :
    scale * (coins.prod law) event ≤ ∫⁻ execution, work execution ∂coins.prod law := by
  rw [Measure.prod_apply measurable, lintegral_prod work workMeasurable,
    ← lintegral_const_mul' scale _ finite]
  exact lintegral_mono conditional

def failure {Coins S A : Type} (Memory : Type) (dummy : Digest)
    (ctx : Context) (radius : ℕ) (prelude : Coins → Program S)
    (step : Coins → S → OracleMachine.Command S A) : Set (Coins × World) :=
  {execution | NativeGoldBatchLifetimeSoundness.Failure Memory dummy ctx radius
    (run (prelude execution.1)) id (step execution.1) execution.2}

/-- For countably many coin outcomes, measurability follows from the causal
oracle replay theorem. There is still no finite support or fuel restriction. -/
theorem failure_measurable_countable {Coins S A : Type} [MeasurableSpace Coins]
    [Countable Coins] [MeasurableSingletonClass Coins]
    (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (prelude : Coins → Program S) (step : Coins → S → OracleMachine.Command S A) :
    MeasurableSet (failure Memory dummy ctx radius prelude step) := by
  have sections : ∀ coin, MeasurableSet {world |
      NativeGoldBatchLifetimeSoundness.Failure Memory dummy ctx radius
        (run (prelude coin)) id (step coin) world} := fun coin =>
    NativeGoldBatchLifetimeMeasurable.failure_measurable Memory dummy ctx radius
      (OracleProgram.run_replay (prelude coin)) id (step coin)
  have union : failure Memory dummy ctx radius prelude step =
      ⋃ coin : Coins, {coin} ×ˢ {world |
        NativeGoldBatchLifetimeSoundness.Failure Memory dummy ctx radius
          (run (prelude coin)) id (step coin) world} := by
    ext execution
    simp [failure]
  rw [union]
  exact MeasurableSet.iUnion fun coin => (measurableSet_singleton coin).prod (sections coin)

/-- A measurable choice of countably many causal strategies also gives a
measurable event on an arbitrary tape space. Unused tape coordinates remain
part of that space; no support-size factor is introduced. -/
theorem failure_measurable_selection {Coins Choices S A : Type}
    [MeasurableSpace Coins] [MeasurableSpace Choices]
    [Countable Choices] [MeasurableSingletonClass Choices]
    (Memory : Type) (dummy : Digest) (ctx : Context) (radius : ℕ)
    (select : Coins → Choices) (selected : Measurable select)
    (prelude : Choices → Program S) (step : Choices → S → OracleMachine.Command S A) :
    MeasurableSet (failure Memory dummy ctx radius
      (fun coin => prelude (select coin)) (fun coin => step (select coin))) := by
  exact (failure_measurable_countable Memory dummy ctx radius prelude step).preimage
    (selected.prodMap measurable_id)

def charge {Coins S A : Type} (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ) (prelude : Coins → Program S)
    (step : Coins → S → OracleMachine.Command S A) (coin : Coins) : ENNReal :=
  (⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy (.pure (prelude coin))
    (OracleMachinePrelude.prepend (step coin)) fuel) +
  NativeGoldBatchLifetimeSoundness.exposureCharge
    (NativeGoldBatchLifetimeSoundness.clean (prelude coin)) id dummy ctx primitive radius
    (OracleMachinePrelude.prepend (step coin))

/-- The fixed-coin lifetime theorem lifts to any independent measurable coin
law. The prelude and every finite continuation are covered for each coin. -/
theorem prelude_bound {Coins S A : Type} [MeasurableSpace Coins]
    (coins : Measure Coins) (Memory : Type) (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot)
      (2^(logSize ctx.parameters.code+1)))
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (prelude : Coins → Program S) (step : Coins → S → OracleMachine.Command S A)
    (large : radius < Fintype.card NativeFields.Goldilocks)
    (small : 3*radius < Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (NativeGoldBatchConcreteColumnFamily.Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)))
    (measurable : MeasurableSet (failure Memory dummy ctx radius prelude step)) :
    (coins.prod law) (failure Memory dummy ctx radius prelude step) ≤
      ∫⁻ coin, charge dummy ctx primitive radius prelude step coin ∂coins := by
  apply independent_bound coins _ measurable
  intro coin
  exact NativeGoldBatchLifetimeSoundness.prelude_bound Memory dummy ctx primitive
    tables message block blowup constructed radius width (prelude coin) (step coin) large small

end
end FormalProof4FHE.HasteBoots.PrivateCoinLifetime
