module
public import FormalProof4FHE.HasteBoots.PrivateCoinMachine
@[expose] public section

/-! Jointly measurable scores of complete finite executions, including local
state that is absent from the oracle log. Unbounded nonnegative scores retain
all finite prefixes; expectations are never conditioned on acceptance. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinScores
open MeasureTheory
open InputIndexedOracle (World)
open NativeTranscript (Execution Observation)
open ObservationReplay (Replayable Agrees)
open PrivateCoinReplay (Tape Prefix cylinder)
open PrivateCoinMachine (FiniteResult)
noncomputable section

def Certified {A : Type} (program : Tape → World → Execution A)
    (seen : Prefix) (log : List Observation) (result : A × List Observation) : Prop :=
  ∀ tape world, tape ∈ cylinder seen → Agrees world log → (program tape world).run = result

theorem finite_certificate {A : Type} {program : Tape → World → Execution A}
    (replay : ∀ tape, Replayable (program tape)) (finiteResult : FiniteResult program)
    (tape : Tape) (world : World) :
    ∃ seen : Prefix, tape ∈ cylinder seen ∧
      Certified program seen (program tape world).run.2 (program tape world).run := by
  obtain ⟨count, fixed⟩ := finiteResult tape world
  refine ⟨⟨count, fun index => tape index⟩, fun _ => rfl, ?_⟩
  intro other fresh same agree
  have atWorld := fixed other same
  have atFresh := (replay other).replay world fresh (by rwa [atWorld])
  exact atFresh.trans atWorld

/-- No countability or measurable-space instance is required for the payload.
Countability comes from finite tape and oracle certificates, not from states. -/
theorem event_measurable {A : Type} {program : Tape → World → Execution A}
    (replay : ∀ tape, Replayable (program tape)) (finiteResult : FiniteResult program)
    (event : A × List Observation → Prop) :
    MeasurableSet {execution : Tape × World | event (program execution.1 execution.2).run} := by
  let selected : Set (Prefix × List Observation) :=
    {entry | ∃ result, Certified program entry.1 entry.2 result ∧ event result}
  have equal : {execution : Tape × World | event (program execution.1 execution.2).run} =
      ⋃ entry ∈ selected, cylinder entry.1 ×ˢ {world | Agrees world entry.2} := by
    ext execution
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod]
    constructor
    · intro yes
      obtain ⟨seen, member, certificate⟩ := finite_certificate replay finiteResult execution.1 execution.2
      exact ⟨(seen, (program execution.1 execution.2).run.2),
        ⟨(program execution.1 execution.2).run, certificate, yes⟩,
        member, (replay execution.1).truthful execution.2⟩
    · rintro ⟨entry, ⟨result, certificate, yes⟩, member, truthful⟩
      rwa [certificate execution.1 execution.2 member truthful]
  rw [equal]
  exact MeasurableSet.biUnion (Set.to_countable selected) fun entry _ =>
    (PrivateCoinReplay.cylinder_measurable entry.1).prod (PrivateCoinReplay.agrees_measurable entry.2)

theorem score_measurable {A : Type} {program : Tape → World → Execution A}
    (replay : ∀ tape, Replayable (program tape)) (finiteResult : FiniteResult program)
    (score : A × List Observation → ENNReal) :
    Measurable (fun execution : Tape × World => score (program execution.1 execution.2).run) := by
  intro event _
  exact event_measurable replay finiteResult (fun result => score result ∈ event)

/-- Nonnegative cumulative scores can diverge. A finite-mean or termination
assumption is not needed to establish measurability. -/
def lifetime {A : Type} (program : ℕ → Tape → World → Execution A)
    (score : ℕ → A × List Observation → ENNReal) (execution : Tape × World) : ENNReal :=
  ⨆ fuel : ℕ, score fuel (program fuel execution.1 execution.2).run

theorem lifetime_measurable {A : Type} {program : ℕ → Tape → World → Execution A}
    (replay : ∀ fuel tape, Replayable (program fuel tape))
    (finiteResult : ∀ fuel, FiniteResult (program fuel))
    (score : ℕ → A × List Observation → ENNReal) : Measurable (lifetime program score) :=
  Measurable.iSup (fun fuel => score_measurable (replay fuel) (finiteResult fuel) (score fuel))

/-- For cumulative prefix scores, expected lifetime work is exactly the
supremum of expected prefix scores, including nonterminating executions. -/
theorem lifetime_lintegral {A : Type} {program : ℕ → Tape → World → Execution A}
    (replay : ∀ fuel tape, Replayable (program fuel tape))
    (finiteResult : ∀ fuel, FiniteResult (program fuel))
    (score : ℕ → A × List Observation → ENNReal) (measure : Measure (Tape × World))
    (increasing : ∀ execution : Tape × World,
      Monotone (fun fuel => score fuel (program fuel execution.1 execution.2).run)) :
    (∫⁻ execution, lifetime program score execution ∂measure) =
      ⨆ fuel : ℕ, ∫⁻ execution, score fuel (program fuel execution.1 execution.2).run ∂measure := by
  apply lintegral_iSup (fun fuel => score_measurable (replay fuel) (finiteResult fuel) (score fuel))
  intro first later bounded execution
  exact increasing execution bounded

theorem lifetime_prod {A : Type} {program : ℕ → Tape → World → Execution A}
    (replay : ∀ fuel tape, Replayable (program fuel tape))
    (finiteResult : ∀ fuel, FiniteResult (program fuel))
    (score : ℕ → A × List Observation → ENNReal) (coins : Measure Tape) :
    (∫⁻ execution, lifetime program score execution ∂coins.prod InputIndexedOracle.law) =
      ∫⁻ tape, ∫⁻ world, lifetime program score (tape, world) ∂InputIndexedOracle.law ∂coins :=
  lintegral_prod _ (lifetime_measurable replay finiteResult score).aemeasurable
end
end FormalProof4FHE.HasteBoots.PrivateCoinScores
