module

public import FormalProof4FHE.HasteBoots.OracleExecutionLaw

@[expose] public section

/-!
# Cache-aware SHAKE/hash response laws given the whole observed past

A finite response uses earlier values on seen coordinates and a uniform
word on unseen coordinates. The old part is never resampled. Fixed byte
positions, not reader IDs or method labels, decide overlap. Uniform fresh
blocks and deterministic repeated blocks are derived corner cases.
-/

namespace FormalProof4FHE.HasteBoots.CachedOracleResponse

open MeasureTheory ProbabilityTheory
open InputIndexedOracle (Byte Input Coordinate World law assignment)

noncomputable section

variable {I : Type}

def observe (coordinates : I → Coordinate) (world : World) : I → Byte := fun i => world (coordinates i)

def mask (seen : Finset Coordinate) (values : World) (coordinates : I → Coordinate) (raw : I → Byte) : I → Byte :=
  fun i => if coordinates i ∈ seen then values (coordinates i) else raw i

theorem observe_measurable (coordinates : I → Coordinate) : Measurable (observe coordinates) := by
  unfold observe
  fun_prop

theorem mask_measurable (seen : Finset Coordinate) (values : World) (coordinates : I → Coordinate) :
    Measurable (mask seen values coordinates) := by
  apply Measurable.of_eval
  intro i
  by_cases member : coordinates i ∈ seen
  · simpa only [mask, member, ite_true] using (measurable_const : Measurable (fun _ : I → Byte => values (coordinates i)))
  · simpa only [mask, member, ite_false] using (measurable_pi_apply i : Measurable (fun raw : I → Byte => raw i))

/-- Full conditional response law with arbitrary partial overlap and mixed
prequeries. Only response coordinates must be distinct within this block. -/
theorem assignment_response [Fintype I] (seen : Finset Coordinate) (values : World) (coordinates : I → Coordinate)
    (distinct : Function.Injective coordinates) :
    (law[|assignment seen values]).map (observe coordinates) =
      (uniformOn (Set.univ : Set (I → Byte))).map (mask seen values coordinates) := by
  rw [OraclePosterior.assignment_posterior,
    Measure.map_map (observe_measurable coordinates) (OraclePosterior.override_measurable seen values)]
  have equal : observe coordinates ∘ OraclePosterior.override seen values =
      mask seen values coordinates ∘ observe coordinates := rfl
  rw [equal, ← Measure.map_map (mask_measurable seen values coordinates) (observe_measurable coordinates)]
  rw [show law.map (observe coordinates) = uniformOn (Set.univ : Set (I → Byte)) from
    InputIndexedOracle.finite_coordinates_uniform coordinates distinct]

theorem execution_response {A : Type} {program : World → NativeTranscript.Execution A}
    [Fintype I] (replay : ObservationReplay.Replayable program) (world : World)
    (coordinates : I → Coordinate) (distinct : Function.Injective coordinates) :
    (law[|{other | (program other).run = (program world).run}]).map (observe coordinates) =
      (uniformOn (Set.univ : Set (I → Byte))).map
        (mask (ObservationReplay.footprint (program world).run.2) world coordinates) := by
  rw [ObservationReplay.fiber_eq_assignment replay world]
  exact assignment_response _ _ coordinates distinct

theorem fresh_response [Fintype I] (seen : Finset Coordinate) (values : World) (coordinates : I → Coordinate)
    (distinct : Function.Injective coordinates) (fresh : ∀ i, coordinates i ∉ seen) :
    (law[|assignment seen values]).map (observe coordinates) = uniformOn (Set.univ : Set (I → Byte)) := by
  rw [assignment_response seen values coordinates distinct]
  have identity : mask seen values coordinates = id := by
    funext raw i
    exact ite_eq_right (fresh i)
  rw [identity, Measure.map_id]

theorem repeated_response [Fintype I] (seen : Finset Coordinate) (values : World) (coordinates : I → Coordinate)
    (distinct : Function.Injective coordinates) (known : ∀ i, coordinates i ∈ seen) :
    (law[|assignment seen values]).map (observe coordinates) = Measure.dirac (observe coordinates values) := by
  rw [assignment_response seen values coordinates distinct]
  have constant : mask seen values coordinates = fun _ : I → Byte => observe coordinates values := by
    funext raw i
    exact ite_eq_left (known i)
  simp only [constant, Measure.map_const, measure_univ, one_smul]

/-- SHAKE coordinates are selected by full input and offset, never a reader ID. -/
def shakeCoordinates (input : Input) (offset count : ℕ) : Fin count → Coordinate :=
  fun i => .inl (input, offset + i.val)

theorem shake_distinct (input : Input) (offset count : ℕ) : Function.Injective (shakeCoordinates input offset count) := by
  intro left right equal
  apply Fin.ext
  have positions := (Prod.mk.inj (Sum.inl.inj equal)).2
  omega

def hashCoordinates (input : Input) : Fin 64 → Coordinate := fun i => .inr (input, i)

theorem hash_distinct (input : Input) : Function.Injective (hashCoordinates input) := by
  intro left right equal
  exact (Prod.mk.inj (Sum.inr.inj equal)).2

theorem shake_response {A : Type} {program : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable program) (world : World) (input : Input) (offset count : ℕ) :
    (law[|{other | (program other).run = (program world).run}]).map
      (fun other => InputIndexedOracle.block other input offset count) =
      (uniformOn (Set.univ : Set (Fin count → Byte))).map
        (mask (ObservationReplay.footprint (program world).run.2) world (shakeCoordinates input offset count)) :=
  execution_response replay world _ (shake_distinct input offset count)

theorem hash_response {A : Type} {program : World → NativeTranscript.Execution A}
    (replay : ObservationReplay.Replayable program) (world : World) (input : Input) :
    (law[|{other | (program other).run = (program world).run}]).map
      (fun other => InputIndexedOracle.sha512 other input) =
      (uniformOn (Set.univ : Set (Fin 64 → Byte))).map
        (mask (ObservationReplay.footprint (program world).run.2) world (hashCoordinates input)) :=
  execution_response replay world _ (hash_distinct input)

end

end FormalProof4FHE.HasteBoots.CachedOracleResponse
