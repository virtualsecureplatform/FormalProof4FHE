module
public import FormalProof4FHE.HasteBoots.PrivateCoinLifetime
@[expose] public section

/-! Finite executions inspect finitely many private tape coordinates, even
when their number depends on the tape and oracle responses. Combined with
oracle replay, this gives joint measurability on the two product spaces.
There is no uniform bound on coin use or on machine lifetime. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinReplay
open MeasureTheory
open InputIndexedOracle (Byte World)
open NativeTranscript (Execution Observation)
open ObservationReplay (Replayable Agrees)
noncomputable section

abbrev Tape := ℕ → Byte
abbrev Prefix := Σ count : ℕ, Fin count → Byte

def cylinder (seen : Prefix) : Set Tape :=
  {tape | ∀ index : Fin seen.1, tape index = seen.2 index}

theorem cylinder_measurable (seen : Prefix) : MeasurableSet (cylinder seen) := by
  have equal : cylinder seen = ⋂ index : Fin seen.1, {tape : Tape | tape index = seen.2 index} := by
    ext tape
    simp [cylinder]
  rw [equal]
  exact MeasurableSet.iInter fun index =>
    measurableSet_eq_fun (measurable_pi_apply index.val) measurable_const

theorem agrees_measurable (log : List Observation) : MeasurableSet {world | Agrees world log} := by
  classical
  by_cases possible : ∃ world, Agrees world log
  · obtain ⟨world, truthful⟩ := possible
    have equal : {other | Agrees other log} =
        InputIndexedOracle.assignment (ObservationReplay.footprint log) world := by
      ext other
      exact ⟨ObservationReplay.same_of_agrees world other log truthful,
        ObservationReplay.agrees_of_same world other log truthful⟩
    rw [equal]
    exact InputIndexedOracle.assignment_measurable _ _
  · have empty : {world | Agrees world log} = ∅ := by
      ext world
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun yes => possible ⟨world, yes⟩
    rw [empty]
    exact MeasurableSet.empty

/-- At each actual finite run, some finite tape prefix fixes the oracle log
at that oracle world. The prefix length may depend on both inputs. -/
def FiniteUse {A : Type} (program : Tape → World → Execution A) : Prop :=
  ∀ tape world, ∃ count : ℕ, ∀ other : Tape,
    (∀ index : Fin count, other index = tape index) →
      (program other world).run.2 = (program tape world).run.2

def Certified {A : Type} (program : Tape → World → Execution A)
    (seen : Prefix) (log : List Observation) : Prop :=
  ∀ tape world, tape ∈ cylinder seen → Agrees world log → (program tape world).run.2 = log

/-- A finite coin prefix together with the observed oracle log determines the
log throughout their entire product cylinder. -/
theorem finite_certificate {A : Type} {program : Tape → World → Execution A}
    (replay : ∀ tape, Replayable (program tape)) (finiteUse : FiniteUse program)
    (tape : Tape) (world : World) :
    ∃ seen : Prefix, tape ∈ cylinder seen ∧ Certified program seen (program tape world).run.2 := by
  obtain ⟨count, fixed⟩ := finiteUse tape world
  refine ⟨⟨count, fun index => tape index⟩, fun _ => rfl, ?_⟩
  intro other fresh same agree
  have atWorld := fixed other same
  have atFresh := (replay other).replay world fresh (by rwa [atWorld])
  exact (congrArg Prod.snd atFresh).trans atWorld

/-- Any predicate of the recorded log is jointly measurable. The proof takes
a countable union of finite byte certificates, not of infinite random tapes. -/
theorem event_measurable {A : Type} {program : Tape → World → Execution A}
    (replay : ∀ tape, Replayable (program tape)) (finiteUse : FiniteUse program)
    (event : List Observation → Prop) :
    MeasurableSet {execution : Tape × World | event (program execution.1 execution.2).run.2} := by
  let selected : Set (Prefix × List Observation) :=
    {entry | Certified program entry.1 entry.2 ∧ event entry.2}
  have equal : {execution : Tape × World | event (program execution.1 execution.2).run.2} =
      ⋃ entry ∈ selected, cylinder entry.1 ×ˢ {world | Agrees world entry.2} := by
    ext execution
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod]
    constructor
    · intro yes
      obtain ⟨seen, member, certificate⟩ := finite_certificate replay finiteUse execution.1 execution.2
      exact ⟨(seen, (program execution.1 execution.2).run.2), ⟨certificate, yes⟩,
        member, (replay execution.1).truthful execution.2⟩
    · rintro ⟨entry, ⟨certificate, yes⟩, member, truthful⟩
      rwa [certificate execution.1 execution.2 member truthful]
  rw [equal]
  exact MeasurableSet.biUnion (Set.to_countable selected) fun entry _ =>
    (cylinder_measurable entry.1).prod (agrees_measurable entry.2)

end
end FormalProof4FHE.HasteBoots.PrivateCoinReplay
