module

public import FormalProof4FHE.HasteBoots.OraclePosterior
public import Mathlib.Tactic.DeriveCountable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-!
# Whole-history conditional laws for adaptive oracle continuations

Exact observable logs are countable and determine a replayable execution's
whole result. Thus all execution predicates are measurable, even when the
payload type itself is not countable. This does not put the discrete sigma
algebra on the world. Conditional continuation laws retain the probability
of the full past, rather than conditioning on verification success.
-/

namespace FormalProof4FHE.HasteBoots.OracleExecutionLaw

open MeasureTheory ProbabilityTheory
open InputIndexedOracle (World law)
open NativeTranscript (Execution Observation)
open ObservationReplay (Replayable)

deriving instance Countable for Observation

noncomputable section

theorem logs_determine_result {A : Type} {program : World → Execution A} (replay : Replayable program)
    (left right : World) (same : (program left).run.2 = (program right).run.2) :
    (program left).run = (program right).run := by
  apply replay.replay right left
  rw [← same]
  exact replay.truthful left

/-- Countability comes from actual finite byte logs, not an assumed small
payload type or a fixed bound on execution length. -/
theorem range_countable {A : Type} {program : World → Execution A} (replay : Replayable program) :
    (Set.range (fun world => (program world).run)).Countable := by
  have maps : Set.MapsTo (Prod.snd : A × List Observation → List Observation)
      (Set.range (fun world => (program world).run)) Set.univ := fun _ _ => Set.mem_univ _
  apply maps.countable_of_injOn ?_ Set.countable_univ
  rintro _ ⟨left, rfl⟩ _ ⟨right, rfl⟩ same
  exact logs_determine_result replay left right same

/-- Any predicate on a replayable complete result/log is measurable in the
original product sigma algebra. No measurable payload instance is required. -/
theorem event_measurable {A : Type} {program : World → Execution A} (replay : Replayable program)
    (event : A × List Observation → Prop) : MeasurableSet {world | event (program world).run} := by
  let selected := Set.range (fun world => (program world).run) ∩ {result | event result}
  have countable : selected.Countable := (range_countable replay).mono Set.inter_subset_left
  have equal : {world | event (program world).run} =
      ⋃ result ∈ selected, {world | (program world).run = result} := by
    ext world
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro yes
      exact ⟨(program world).run, ⟨⟨world, rfl⟩, yes⟩, rfl⟩
    · rintro ⟨result, ⟨_, yes⟩, same⟩
      rwa [same]
  rw [equal]
  apply MeasurableSet.biUnion countable
  intro result member
  obtain ⟨world, rfl⟩ := member.1
  exact ObservationReplay.fiber_measurable replay world

theorem score_measurable {A : Type} {program : World → Execution A} (replay : Replayable program)
    (score : A × List Observation → ENNReal) : Measurable (fun world => score (program world).run) := by
  intro event _
  exact event_measurable replay (fun result => score result ∈ event)

/-- Unnormalized work-score transfer on the complete history. Scores may
be infinite; neither a runtime cap nor a finite-mean premise is imposed. -/
theorem continuation_lintegral {A B : Type} {past : World → Execution A} (pastReplay : Replayable past)
    (next : (A × List Observation) → World → Execution B) (nextReplay : ∀ result, Replayable (next result))
    (world : World) (score : B × List Observation → ENNReal) :
    (∫⁻ other, score (next (past other).run other).run
      ∂law.restrict {other | (past other).run = (past world).run}) =
      law {other | (past other).run = (past world).run} *
        ∫⁻ fresh, score (next (past world).run
          (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run ∂law := by
  have equal : (fun other => score (next (past other).run other).run) =ᵐ[
      law.restrict {other | (past other).run = (past world).run}]
      (fun other => score (next (past world).run other).run) := by
    filter_upwards [ae_restrict_mem (ObservationReplay.fiber_measurable pastReplay world)] with other same
    rw [same]
  rw [lintegral_congr_ae equal, ObservationReplay.fiber_eq_assignment pastReplay world,
    OraclePosterior.restrict_eq_cached, lintegral_smul_measure,
    lintegral_map (score_measurable (nextReplay _) score) (OraclePosterior.override_measurable _ _), smul_eq_mul]

/-- A score of actual program output/log is transferred, not a count of
virtual fresh-world samples used by the mathematical generator. -/
theorem program_lintegral {A B : Type} (past : OracleProgram.Program A)
    (next : (A × List Observation) → OracleProgram.Program B) (world : World)
    (score : B × List Observation → ENNReal) :
    (∫⁻ other, score (OracleProgram.run (next (OracleProgram.run past other).run) other).run
      ∂law.restrict {other | (OracleProgram.run past other).run = (OracleProgram.run past world).run}) =
      law {other | (OracleProgram.run past other).run = (OracleProgram.run past world).run} *
        ∫⁻ fresh, score (OracleProgram.run (next (OracleProgram.run past world).run)
          (OraclePosterior.override (ObservationReplay.footprint (OracleProgram.run past world).run.2) world fresh)).run ∂law :=
  continuation_lintegral (OracleProgram.run_replay past) (fun result => OracleProgram.run (next result))
    (fun result => OracleProgram.run_replay (next result)) world score

/-- The independent-world generator installs the exact recorded cache and
then evaluates the actual continuation, including all repeated queries. -/
theorem continuation_event {A B : Type} {past : World → Execution A} (pastReplay : Replayable past)
    (next : (A × List Observation) → World → Execution B) (nextReplay : ∀ result, Replayable (next result))
    (world : World) (event : B × List Observation → Prop) :
    law {other | (past other).run = (past world).run ∧ event (next (past other).run other).run} =
      law {other | (past other).run = (past world).run} *
        law {fresh | event (next (past world).run
          (OraclePosterior.override (ObservationReplay.footprint (past world).run.2) world fresh)).run} := by
  have equal : {other | (past other).run = (past world).run ∧ event (next (past other).run other).run} =
      {other | (past other).run = (past world).run} ∩
        {other | event (next (past world).run other).run} := by
    ext other
    constructor
    · rintro ⟨same, yes⟩
      refine ⟨same, ?_⟩
      simp only [Set.mem_ofPred_eq]
      rw [same] at yes
      exact yes
    · rintro ⟨same, yes⟩
      refine ⟨same, ?_⟩
      rw [same]
      simpa only [Set.mem_ofPred_eq] using yes

  rw [equal, ObservationReplay.fiber_eq_assignment pastReplay world]
  exact OraclePosterior.assignment_event _ _ _ (event_measurable (nextReplay _) event)

/-- Specialization to any complete online mixed-oracle prefix and any
causal continuation selected from its actual retained result and log. -/
theorem program_continuation {A B : Type} (past : OracleProgram.Program A)
    (next : (A × List Observation) → OracleProgram.Program B) (world : World)
    (event : B × List Observation → Prop) :
    law {other | (OracleProgram.run past other).run = (OracleProgram.run past world).run ∧
      event (OracleProgram.run (next (OracleProgram.run past other).run) other).run} =
      law {other | (OracleProgram.run past other).run = (OracleProgram.run past world).run} *
        law {fresh | event (OracleProgram.run (next (OracleProgram.run past world).run)
          (OraclePosterior.override (ObservationReplay.footprint (OracleProgram.run past world).run.2) world fresh)).run} :=
  continuation_event (OracleProgram.run_replay past) (fun result => OracleProgram.run (next result))
    (fun result => OracleProgram.run_replay (next result)) world event

/-- A paused prefix keeps its residual program; this law imposes no runtime
query cap or successful-completion floor on its later continuation. -/
theorem prefix_continuation {A B : Type} (fuel : ℕ) (past : OracleProgram.Program A)
    (next : ((OracleProgram.Program A ⊕ A) × List Observation) → OracleProgram.Program B)
    (world : World) (event : B × List Observation → Prop) :
    law {other | (OracleProgram.runPrefix fuel past other).run = (OracleProgram.runPrefix fuel past world).run ∧
      event (OracleProgram.run (next (OracleProgram.runPrefix fuel past other).run) other).run} =
      law {other | (OracleProgram.runPrefix fuel past other).run = (OracleProgram.runPrefix fuel past world).run} *
        law {fresh | event (OracleProgram.run (next (OracleProgram.runPrefix fuel past world).run)
          (OraclePosterior.override (ObservationReplay.footprint (OracleProgram.runPrefix fuel past world).run.2) world fresh)).run} :=
  continuation_event (OracleProgram.prefix_replay fuel past) (fun result => OracleProgram.run (next result))
    (fun result => OracleProgram.run_replay (next result)) world event

end

end FormalProof4FHE.HasteBoots.OracleExecutionLaw
