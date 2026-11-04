module

public import FormalProof4FHE.HasteBoots.OracleExecutionLaw

@[expose] public section

/-!
# Averaging cache-aware bounds over every attainable oracle history

The partition contains full result/log histories, including rejected and
paused activity. Its index type is countable without an assumed query cap.
Local bounds retain their unnormalized history mass and average into the
same actual score. This is a reduction theorem: the numerical cache-aware
charge and its physical-work interpretation must still be proved.
-/

namespace FormalProof4FHE.HasteBoots.OracleHistoryCharge

open MeasureTheory ProbabilityTheory
open InputIndexedOracle (World law)
open NativeTranscript (Execution Observation)
open ObservationReplay (Replayable)

noncomputable section

abbrev Histories {A : Type} (past : World → Execution A) := Set.range (fun world => (past world).run)

def fiber {A : Type} (past : World → Execution A) (history : Histories past) : Set World :=
  {world | (past world).run = history.val}

theorem histories_countable {A : Type} {past : World → Execution A} (replay : Replayable past) :
    Countable (Histories past) := (OracleExecutionLaw.range_countable replay).to_subtype

theorem fiber_measurable {A : Type} {past : World → Execution A} (replay : Replayable past)
    (history : Histories past) : MeasurableSet (fiber past history) := by
  obtain ⟨world, same⟩ := history.property
  unfold fiber
  rw [← same]
  exact ObservationReplay.fiber_measurable replay world

theorem fibers_disjoint {A : Type} (past : World → Execution A) : Pairwise (fun left right => Disjoint (fiber past left) (fiber past right)) := by
  intro left right different
  apply Set.disjoint_left.mpr
  intro world inLeft inRight
  apply different
  apply Subtype.ext
  exact inLeft.symm.trans inRight

theorem fibers_cover {A : Type} (past : World → Execution A) : (⋃ history, fiber past history) = Set.univ := by
  ext world
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨⟨(past world).run, ⟨world, rfl⟩⟩, rfl⟩

/-- An exact measure partition; there is no omitted or renormalized history. -/
theorem law_sum_fibers {A : Type} {past : World → Execution A} (replay : Replayable past) :
    law = Measure.sum (fun history : Histories past => law.restrict (fiber past history)) := by
  let := histories_countable replay
  have partition := Measure.restrict_iUnion (μ := law) (fibers_disjoint past) (fiber_measurable replay)
  rw [fibers_cover, Measure.restrict_univ] at partition
  exact partition

/-- Average bounds on the same actual score, including infinite costs.
No bounded history space, expected-work bound or success floor is assumed. -/
theorem average_bound {A : Type} {past : World → Execution A} (replay : Replayable past)
    (bad : Set World) (measurable : MeasurableSet bad) (score : World → ENNReal) (rate : ENNReal)
    (localBound : ∀ history : Histories past,
      law (fiber past history ∩ bad) ≤ rate * ∫⁻ world, score world ∂law.restrict (fiber past history)) :
    law bad ≤ rate * ∫⁻ world, score world ∂law := by
  let := histories_countable replay
  calc
    law bad = ∑' history : Histories past, law (fiber past history ∩ bad) := by
      conv_lhs => rw [law_sum_fibers replay]
      rw [Measure.sum_apply _ measurable]
      congr 1
      funext history
      rw [Measure.restrict_apply measurable, Set.inter_comm]
    _ ≤ ∑' history : Histories past, rate * ∫⁻ world, score world ∂law.restrict (fiber past history) :=
      ENNReal.tsum_le_tsum localBound
    _ = rate * ∫⁻ world, score world ∂law := by
      rw [ENNReal.tsum_mul_left, ← lintegral_sum_measure, ← law_sum_fibers replay]

/-- Already revealed bad luck remains an explicit unnormalized ledger.
It is not silently reset when conditioning on the later history. -/
theorem average_risk_bound {A : Type} {past : World → Execution A} (replay : Replayable past)
    (bad : Set World) (measurable : MeasurableSet bad) (score : World → ENNReal) (rate : ENNReal)
    (risk : Histories past → ENNReal)
    (localBound : ∀ history : Histories past,
      law (fiber past history ∩ bad) ≤ risk history + rate * ∫⁻ world, score world ∂law.restrict (fiber past history)) :
    law bad ≤ (∑' history : Histories past, risk history) + rate * ∫⁻ world, score world ∂law := by
  let := histories_countable replay
  calc
    law bad = ∑' history : Histories past, law (fiber past history ∩ bad) := by
      conv_lhs => rw [law_sum_fibers replay]
      rw [Measure.sum_apply _ measurable]
      congr 1
      funext history
      rw [Measure.restrict_apply measurable, Set.inter_comm]
    _ ≤ ∑' history : Histories past, (risk history + rate * ∫⁻ world, score world ∂law.restrict (fiber past history)) :=
      ENNReal.tsum_le_tsum localBound
    _ = _ := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← lintegral_sum_measure, ← law_sum_fibers replay]

/-- Measurability of a continuation selected from the entire past follows
from the countable partition and each branch's replay certificate. -/
theorem continuation_measurable {A B : Type} {past : World → Execution A} (replay : Replayable past)
    (next : (A × List Observation) → World → Execution B) (nextReplay : ∀ history, Replayable (next history))
    (event : B × List Observation → Prop) : MeasurableSet {world | event (next (past world).run world).run} := by
  let := histories_countable replay
  have equal : {world | event (next (past world).run world).run} =
      ⋃ history : Histories past, fiber past history ∩ {world | event (next history.val world).run} := by
    ext world
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, fiber]
    constructor
    · intro yes
      exact ⟨⟨(past world).run, ⟨world, rfl⟩⟩, rfl, yes⟩
    · rintro ⟨history, same, yes⟩
      rwa [same]
  rw [equal]
  apply MeasurableSet.iUnion
  intro history
  exact (fiber_measurable replay history).inter (OracleExecutionLaw.event_measurable (nextReplay _) event)

/-- Convert a proved cache-conditional probability/work inequality into a
global bound. Every prequery and cached answer remains in the history. -/
theorem cached_bound {A B : Type} {past : World → Execution A} (replay : Replayable past)
    (next : (A × List Observation) → World → Execution B) (nextReplay : ∀ history, Replayable (next history))
    (event : B × List Observation → Prop) (score : B × List Observation → ENNReal) (rate : ENNReal)
    (localBound : ∀ world : World,
      law {fresh | event (next (past world).run
        (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run} ≤
      rate * ∫⁻ fresh, score (next (past world).run
        (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run ∂law) :
    law {world | event (next (past world).run world).run} ≤
      rate * ∫⁻ world, score (next (past world).run world).run ∂law := by
  apply average_bound replay _ (continuation_measurable replay next nextReplay event) _ rate
  intro history
  obtain ⟨world, same⟩ := history.property
  change law ({other | (past other).run = history.val} ∩ {other | event (next (past other).run other).run}) ≤ _
  change _ ≤ rate * ∫⁻ other, score (next (past other).run other).run ∂law.restrict {other | (past other).run = history.val}
  rw [← same]
  change law {other | (past other).run = (past world).run ∧ event (next (past other).run other).run} ≤ _
  rw [OracleExecutionLaw.continuation_event replay next nextReplay world event,
    OracleExecutionLaw.continuation_lintegral replay next nextReplay world score]
  calc
    _ ≤ law {other | (past other).run = (past world).run} *
        (rate * ∫⁻ fresh, score (next (past world).run
          (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run ∂law) :=
      mul_le_mul_right (localBound world) _
    _ = _ := by ac_rfl

/-- The cache-conditional form keeps inherited risk at its true history
weight. Charging that ledger is an additional, explicit obligation. -/
theorem cached_risk_bound {A B : Type} {past : World → Execution A} (replay : Replayable past)
    (next : (A × List Observation) → World → Execution B) (nextReplay : ∀ history, Replayable (next history))
    (event : B × List Observation → Prop) (score : B × List Observation → ENNReal) (rate : ENNReal)
    (risk : (A × List Observation) → ENNReal)
    (localBound : ∀ world : World,
      law {fresh | event (next (past world).run
        (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run} ≤
      risk (past world).run + rate * ∫⁻ fresh, score (next (past world).run
        (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run ∂law) :
    law {world | event (next (past world).run world).run} ≤
      (∑' history : Histories past, law (fiber past history) * risk history.val) +
        rate * ∫⁻ world, score (next (past world).run world).run ∂law := by
  apply average_risk_bound replay _ (continuation_measurable replay next nextReplay event) _ rate
    (fun history => law (fiber past history) * risk history.val)
  intro history
  obtain ⟨world, same⟩ := history.property
  change law ({other | (past other).run = history.val} ∩ {other | event (next (past other).run other).run}) ≤
    law {other | (past other).run = history.val} * risk history.val +
      rate * ∫⁻ other, score (next (past other).run other).run ∂law.restrict {other | (past other).run = history.val}
  rw [← same]
  change law {other | (past other).run = (past world).run ∧ event (next (past other).run other).run} ≤ _
  rw [OracleExecutionLaw.continuation_event replay next nextReplay world event,
    OracleExecutionLaw.continuation_lintegral replay next nextReplay world score]
  calc
    _ ≤ law {other | (past other).run = (past world).run} *
        (risk (past world).run + rate * ∫⁻ fresh, score (next (past world).run
          (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run ∂law) :=
      mul_le_mul_right (localBound world) _
    _ = _ := by
      rw [mul_add]
      congr 1
      ac_rfl

end

end FormalProof4FHE.HasteBoots.OracleHistoryCharge
