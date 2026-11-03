module

public import FormalProof4FHE.HasteBoots.ChargeAccountShift
public import FormalProof4FHE.HasteBoots.CompletedPrefixMixture
public import FormalProof4FHE.HasteBoots.SharedChargedCompletion

@[expose] public section

/-!
# Charged earlier work before unbounded completed shared execution

The original prefix runs first on the real shared handler. Its complete
result/state/account is retained before private sampling. Account shifting
connects the zero-increment conditional construction to the actual full
recorded query program. The expected completed account includes earlier
work and equals the supremum of the real whole-prefix charges.
-/

open OracleSpec OracleComp BinaryTree MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ChargedPrefixCompletion

noncomputable section

variable {First A Later Cfg Input Digest Payload : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

local instance (X : Type) : MeasurableSpace X := ⊤
local instance (X Y : Type) : MeasurableSpace (X × Y) := ⊤

abbrev Source (shape : Cfg → Skeleton) (First : Type) :=
  First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal

abbrev Tail (shape : Cfg → Skeleton) (A Later : Type) :=
  (A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal

/-- The original shared prefix executes before any sampler observation. -/
def program (step : ProbComp A) (complete : A → Prop)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) First)
    (next : First → A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later) := do
  let first ← before
  let last ← SharedCompletedContinuation.program step complete (next first)
  pure (first, last)

/-- Both the prefix account and all later increments remain in the actual
final account. Only analysis snapshots are erased by this projection. -/
def pack {shape : Cfg → Skeleton}
    (outcome : Source (Input := Input) (Digest := Digest) shape First × Tail (Input := Input) (Digest := Digest) shape A Later) :
    (First × (A × Option Later)) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal :=
  ((outcome.1.1, outcome.2.1), (outcome.2.2.1, outcome.1.2.2 + outcome.2.2.2))

variable (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
  (loss : (CheckpointExecution.Spec unifSpec Cfg Input Digest).Domain →
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
  (private_zero : ∀ query state, loss (.inl query) state = 0)
  (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) First)
  (next : First → A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
  (observations : ℕ → ProbComp A) (complete : A → Prop)
  (grows : ∀ i j, i ≤ j → CompletedObservation.LE (observations i) (observations j) complete)

def source : ProbComp (Source (Input := Input) (Digest := Digest) shape First) :=
  (simulateQ (ChargedExecution.handler
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss) before).run (initial, 0)

def tail (first : Source (Input := Input) (Digest := Digest) shape First) (n : ℕ) :=
  SharedChargedCompletion.experiment enc dummy shape loss (next first.1) first.2.1 observations complete n

local notation "src" => source enc dummy shape loss before initial
local notation "tails" => tail enc dummy shape loss next observations complete
local notation "done" => fun _ : Source (Input := Input) (Digest := Digest) shape First =>
  SharedChargedCompletion.finished (A := A) (Later := Later) (shape := shape)

include private_zero grows in
/-- Each actual prefix observation starts its own correctly ordered tail. -/
theorem tail_ordered (first : Source (Input := Input) (Digest := Digest) shape First) (i j : ℕ) (h : i ≤ j) :
    CompletedObservation.LE (tails first i) (tails first j) (done first) :=
  SharedChargedCompletion.ordered enc dummy shape loss private_zero (next first.1) first.2.1 observations complete grows h

/-- Countably additive joint law retains the original prefix snapshot and
account, raw sampling observation, later result and final state/increment. -/
def measure : Measure (Source (Input := Input) (Digest := Digest) shape First ×
    Tail (Input := Input) (Digest := Digest) shape A Later) :=
  CompletedPrefixMixture.measure src tails done
    (tail_ordered enc dummy shape loss private_zero next observations complete grows)

local notation "law" => measure enc dummy shape loss private_zero before next initial observations complete grows

/-- The full original recorded program is recovered, with the actual prefix
account added to later increments and no query moved after completion. -/
theorem finite_operational (n : ℕ) :
    pack <$> CompletedPrefixMixture.program src tails n =
      (simulateQ (ChargedExecution.handler
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
        (program (observations n) complete before next)).run (initial, 0) := by
  simp only [CompletedPrefixMixture.program, program, source, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, map_bind]
  congr 1
  funext first
  rw [ChargeAccountShift.run _ _ _ first.2.1 first.2.2]
  simp only [tail, SharedChargedCompletion.experiment, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_apply, pack, ChargeAccountShift.shift]

/-- Projection to the actual result/final-state/account query execution. -/
def operational : Measure ((First × (A × Option Later)) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) :=
  @Measure.map _ _ ⊤ ⊤ pack law

/-- Each operational event is the limit of actual completed finite full runs. -/
theorem operational_apply (event : (First × (A × Option Later)) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal → Prop) :
    operational enc dummy shape loss private_zero before next initial observations complete grows {outcome | event outcome} =
      ⨆ n, Pr{let outcome ← (simulateQ (ChargedExecution.handler
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
        (program (observations n) complete before next)).run (initial, 0)}[outcome.1.2.2 ≠ none ∧ event outcome] := by
  rw [operational, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    measure, CompletedPrefixMixture.measure, CompletedObservationLimit.measure_apply]
  apply iSup_congr
  intro n
  rw [← finite_operational, prEvent_map]
  rfl

/-- Every possible earlier observation has the proved sampler completion law. -/
theorem probability (total : (⨆ n, Pr{let observed ← observations n}[complete observed]) = 1) :
    IsProbabilityMeasure law := by
  apply CompletedPrefixMixture.probability
  intro first
  simpa only [tail, SharedChargedCompletion.completion enc dummy shape loss private_zero] using total

/-- The projected full recorded execution is normalized as well. -/
theorem operational_probability (total : (⨆ n, Pr{let observed ← observations n}[complete observed]) = 1) :
    IsProbabilityMeasure (operational enc dummy shape loss private_zero before next initial observations complete grows) := by
  unfold operational
  apply (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr
  exact probability enc dummy shape loss private_zero before next initial observations complete grows total

include private_zero in
/-- The finite conditional charge is exactly its completion-gated account. -/
theorem tail_charge (first : Source (Input := Input) (Digest := Digest) shape First) (n : ℕ) :
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
      (SharedCompletedContinuation.program (observations n) complete (next first.1)) first.2.1 =
      ∫⁻ value, value ∂𝒟[(fun last => if SharedChargedCompletion.finished last then last.2.2 else 0) <$> tails first n] := by
  exact ((SharedChargedCompletion.gated_account enc dummy shape loss private_zero (next first.1) first.2.1
    (observations n) complete).trans (ChargedExecution.expected_zero _ _ _ _)).symm

include private_zero grows in
/-- Conditional charges increase pointwise in the actual prefix observation. -/
theorem tail_charge_monotone (first : Source (Input := Input) (Digest := Digest) shape First) :
    Monotone (fun n => ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
      (SharedCompletedContinuation.program (observations n) complete (next first.1)) first.2.1) := by
  intro i j h
  have ordered := CompletedPrefixMixture.inner_monotone tails done
    (tail_ordered enc dummy shape loss private_zero next observations complete grows) (fun _ last => last.2.2) first h
  exact (tail_charge enc dummy shape loss private_zero next observations complete first i).trans_le
    (ordered.trans_eq (tail_charge enc dummy shape loss private_zero next observations complete first j).symm)

/-- The actual earlier charge is retained once, followed by the prefix-average
conditional charge. No work certificate or finite-mean premise is supplied. -/
theorem whole_charge (n : ℕ) :
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
      (program (observations n) complete before next) initial =
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss before initial +
      ∫⁻ value, value ∂𝒟[(fun first => ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
        (SharedCompletedContinuation.program (observations n) complete (next first.1)) first.2.1) <$> src] := by
  unfold program
  rw [ExpectedChargeComposition.bind]
  simp only [ExpectedChargeComposition.bind, ExpectedHazard.charge_pure, OracleComp.evalDist_map_const,
    lintegral_dirac, add_zero]
  rw [← ChargedExecution.erase _ _ before initial 0, Functor.map_map]
  rfl

/-- The complete mean includes earlier source work and all conditional later
charges, even when either expectation is infinite. -/
theorem expected_split (total : (⨆ n, Pr{let observed ← observations n}[complete observed]) = 1) :
    (∫⁻ outcome, outcome.2.2 ∂operational enc dummy shape loss private_zero before next initial observations complete grows) =
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss before initial +
      ∫⁻ value, value ∂𝒟[(fun first => ⨆ n, ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
        (SharedCompletedContinuation.program (observations n) complete (next first.1)) first.2.1) <$> src] := by
  rw [operational, lintegral_map Measurable.of_discrete Measurable.of_discrete]
  change (∫⁻ outcome, outcome.1.2.2 + outcome.2.2.2 ∂law) = _
  rw [measure, CompletedPrefixMixture.integral src tails done
    (tail_ordered enc dummy shape loss private_zero next observations complete grows)
    (fun first last => first.2.2 + last.2.2)]
  have kernel_mean (first : Source (Input := Input) (Digest := Digest) shape First) :
      (∫⁻ last, first.2.2 + last.2.2 ∂CompletedObservationLimit.measure (tails first) (done first)
        (tail_ordered enc dummy shape loss private_zero next observations complete grows first)) =
        first.2.2 + ⨆ n, ExpectedHazard.charge
          (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
          (SharedCompletedContinuation.program (observations n) complete (next first.1)) first.2.1 := by
    change (∫⁻ last, first.2.2 + last.2.2 ∂SharedChargedCompletion.measure enc dummy shape loss private_zero
      (next first.1) first.2.1 observations complete grows) = _
    let _ := SharedChargedCompletion.probability enc dummy shape loss private_zero (next first.1) first.2.1 observations complete grows total
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      SharedChargedCompletion.expected]
  simp_rw [kernel_mean]
  rw [lintegral_id_evalDist_map_add, source, ChargedExecution.expected_zero]

/-- Exact whole-prefix expected-charge transfer. Earlier work executes before
sampling and remains in the normalized completed law; there is no tail-cost
or source-work omission and no bounded-query assumption. -/
theorem expected (total : (⨆ n, Pr{let observed ← observations n}[complete observed]) = 1) :
    (∫⁻ outcome, outcome.2.2 ∂operational enc dummy shape loss private_zero before next initial observations complete grows) =
      ⨆ n, ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
        (program (observations n) complete before next) initial := by
  rw [expected_split enc dummy shape loss private_zero before next initial observations complete grows total,
    lintegral_id_evalDist_map]
  rw [lintegral_iSup (fun _ => Measurable.of_discrete)
    (fun i j h first => tail_charge_monotone enc dummy shape loss private_zero next observations complete grows first h)]
  rw [ENNReal.add_iSup]
  apply iSup_congr
  intro n
  rw [← lintegral_id_evalDist_map]
  exact (whole_charge enc dummy shape loss before next initial observations complete n).symm

end

end FormalProof4FHE.HasteBoots.ChargedPrefixCompletion
