module

public import FormalProof4FHE.HasteBoots.OracleProgram
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

/-!
# Exact joint-world posterior after finite oracle observations

Conditioning on a finite assignment fixes those coordinates and leaves the
entire unobserved complement with its original joint product law. This
includes SHAKE/SHA-512 overlap, partial digests, reader restarts and arbitrary
prequeries; distinct reader instances do not create fresh coordinates.
Replay identifies an adaptive execution fiber with precisely that finite
assignment. The product sigma algebra is retained throughout.
-/

namespace FormalProof4FHE.HasteBoots.OraclePosterior

open MeasureTheory ProbabilityTheory
open InputIndexedOracle (Byte Coordinate World law assignment)

noncomputable section

/-- Install the known cache in an otherwise independently sampled world. -/
def restore (seen : Finset Coordinate) (values : World) (tail : {c : Coordinate // c ∉ seen} → Byte) : World :=
  fun coordinate => if member : coordinate ∈ seen then values coordinate else tail ⟨coordinate, member⟩

def override (seen : Finset Coordinate) (values fresh : World) : World :=
  fun coordinate => if coordinate ∈ seen then values coordinate else fresh coordinate

theorem restore_measurable (seen : Finset Coordinate) (values : World) : Measurable (restore seen values) := by
  apply Measurable.of_eval
  intro coordinate
  by_cases member : coordinate ∈ seen
  · simpa only [restore, member, dite_true] using (measurable_const : Measurable (fun _ : ({c : Coordinate // c ∉ seen} → Byte) => values coordinate))
  · simpa only [restore, member, dite_false] using (measurable_pi_apply (⟨coordinate, member⟩ : {c : Coordinate // c ∉ seen}))

theorem override_measurable (seen : Finset Coordinate) (values : World) : Measurable (override seen values) := by
  apply Measurable.of_eval
  intro coordinate
  by_cases member : coordinate ∈ seen
  · simpa only [override, member, ite_true] using (measurable_const : Measurable (fun _ : World => values coordinate))
  · simpa only [override, member, ite_false] using (measurable_pi_apply coordinate : Measurable (fun fresh : World => fresh coordinate))

theorem override_seen (seen : Finset Coordinate) (values fresh : World) (coordinate : Coordinate)
    (member : coordinate ∈ seen) : override seen values fresh coordinate = values coordinate := by
  simp only [override, member, ite_true]

theorem override_unseen (seen : Finset Coordinate) (values fresh : World) (coordinate : Coordinate)
    (member : coordinate ∉ seen) : override seen values fresh coordinate = fresh coordinate := by
  simp only [override, member, ite_false]

theorem override_of_assignment (seen : Finset Coordinate) (values world : World)
    (agrees : world ∈ assignment seen values) : override seen values world = world := by
  funext coordinate
  by_cases member : coordinate ∈ seen
  · rw [override_seen seen values world coordinate member]
    exact (agrees coordinate member).symm
  · exact override_unseen seen values world coordinate member

/-- Independence applies to the whole unobserved complement, rather than
only to a newly chosen single byte or a disjoint next block. -/
theorem old_independent_override (seen : Finset Coordinate) (values : World) :
    IndepFun (fun world : World => fun coordinate : seen => world coordinate)
      (override seen values) law := by
  have independent : iIndepFun (fun coordinate : Coordinate => fun world : World => world coordinate) law := by
    exact iIndepFun_infinitePi (P := fun _ : Coordinate => InputIndexedOracle.byteLaw)
      (X := fun (_ : Coordinate) (value : Byte) => value) (by fun_prop)
  have split := independent.indepFun_set (seen : Set Coordinate) (seen : Set Coordinate)ᶜ
    disjoint_compl_right (fun coordinate => measurable_pi_apply coordinate)
  have composed := split.comp measurable_id (restore_measurable seen values)
  exact composed

theorem assignment_restrict (seen : Finset Coordinate) (values : World) :
    assignment seen values =
      (fun world : World => fun coordinate : seen => world coordinate) ⁻¹'
        {fun coordinate : seen => values coordinate} := by
  ext world
  constructor
  · intro agrees
    funext coordinate
    exact agrees coordinate coordinate.property
  · intro agrees coordinate member
    exact congrFun agrees ⟨coordinate, member⟩

/-- Unnormalized factorization retains the exact mass of the whole history.
No successful-run normalization or success lower bound is assumed. -/
theorem assignment_event (seen : Finset Coordinate) (values : World) (event : Set World)
    (measurable : MeasurableSet event) :
    law (assignment seen values ∩ event) =
      law (assignment seen values) * law ((override seen values) ⁻¹' event) := by
  have equal : assignment seen values ∩ event =
      assignment seen values ∩ ((override seen values) ⁻¹' event) := by
    ext world
    constructor
    · rintro ⟨agrees, member⟩
      exact ⟨agrees, by simpa only [Set.mem_preimage, override_of_assignment seen values world agrees] using member⟩
    · rintro ⟨agrees, member⟩
      exact ⟨agrees, by simpa only [Set.mem_preimage, override_of_assignment seen values world agrees] using member⟩
  rw [equal, assignment_restrict]
  exact (old_independent_override seen values).measure_inter_preimage_eq_mul
    _ event (measurableSet_singleton _) measurable

theorem assignment_ne_zero (seen : Finset Coordinate) (values : World) : law (assignment seen values) ≠ 0 := by
  rw [InputIndexedOracle.assignment_mass]
  exact pow_ne_zero _ (by simp)

/-- The unnormalized posterior measure is useful for event and work
bounds, retaining arbitrarily small history mass without a floor. -/
theorem restrict_eq_cached (seen : Finset Coordinate) (values : World) :
    law.restrict (assignment seen values) = law (assignment seen values) • law.map (override seen values) := by
  ext event measurable
  rw [Measure.restrict_apply measurable, Set.inter_comm,
    assignment_event seen values event measurable, Measure.smul_apply,
    Measure.map_apply (override_measurable seen values) measurable, smul_eq_mul]

/-- Only the finite cached values matter; the witness world's other bytes
are not consulted by the posterior generator. -/
theorem override_cache_ext (seen : Finset Coordinate) (left right : World)
    (same : ∀ coordinate ∈ seen, left coordinate = right coordinate) :
    override seen left = override seen right := by
  funext fresh coordinate
  by_cases member : coordinate ∈ seen
  · simp only [override, member, ite_true, same coordinate member]
  · simp only [override, member, ite_false]

/-- Exact posterior of the entire mixed-oracle world. Seen bytes are cached;
unseen bytes remain independent under the original joint ideal law. -/
theorem assignment_posterior (seen : Finset Coordinate) (values : World) :
    law[|assignment seen values] = law.map (override seen values) := by
  ext event measurable
  rw [ProbabilityTheory.cond_apply (InputIndexedOracle.assignment_measurable seen values),
    assignment_event seen values event measurable,
    Measure.map_apply (override_measurable seen values) measurable, ← mul_assoc,
    ENNReal.inv_mul_cancel (assignment_ne_zero seen values) (measure_ne_top law _), one_mul]

/-- Adaptive observations fix exactly their distinct returned coordinates.
The fiber includes the whole result and ordered log, not merely acceptance. -/
theorem execution_posterior {A : Type} {program : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable program) (world : World) :
    law[|{other | (program other).run = (program world).run}] =
      law.map (override (ObservationReplay.footprint (program world).run.2) world) := by
  rw [ObservationReplay.fiber_eq_assignment replay world]
  exact assignment_posterior _ _

/-- Reinstalling the whole recorded cache preserves the past pointwise,
so every request selected from that past is fixed on this generator. -/
theorem replay_override {A : Type} {program : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable program) (world fresh : World) :
    (program (override (ObservationReplay.footprint (program world).run.2) world fresh)).run = (program world).run := by
  apply ObservationReplay.replay_of_same replay world
  intro coordinate member
  exact override_seen _ _ _ coordinate member

end

end FormalProof4FHE.HasteBoots.OraclePosterior
