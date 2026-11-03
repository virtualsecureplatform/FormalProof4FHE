module

public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.OracleComp.ProbComp.Basic

@[expose] public section

/-!
# Increasing completed-observation laws

Completion restricts event mass without conditioning or discarding the actual
partial execution. The event can inspect the complete observation, including
all raw traces. Bind closure allows later adaptive work to depend on that
observation; increasing a value marginal alone would not justify this step.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.CompletedObservation

noncomputable section

variable {A B : Type}

def LE (left right : ProbComp A) (complete : A → Prop) : Prop :=
  ∀ event : A → Prop, Pr{let value ← left}[complete value ∧ event value] ≤
    Pr{let value ← right}[complete value ∧ event value]

theorem refl (step : ProbComp A) (complete : A → Prop) : LE step step complete := fun _ => le_rfl

theorem trans {first second third : ProbComp A} {complete : A → Prop}
    (left : LE first second complete) (right : LE second third complete) : LE first third complete :=
  fun event => (left event).trans (right event)

/-- A suspended pure result contributes no completed observation mass, while
its partial trace remains an output of the actual program. -/
theorem pure_incomplete (value : A) (complete : A → Prop) (suspended : ¬complete value) (right : ProbComp A) :
    LE (pure value) right complete := by
  intro event
  have zero : Pr{let result ← (pure value : ProbComp A)}[complete result ∧ event result] = 0 := by
    simp [prEvent_norm, suspended]
  rw [zero]
  exact bot_le

/-- A completed singleton is compared with its actual unconditional mass. -/
theorem singleton {left right : ProbComp A} {complete : A → Prop} (ordered : LE left right complete)
    (value : A) (done : complete value) :
    Pr{let result ← left}[result = value] ≤ Pr{let result ← right}[result = value] := by
  have same (step : ProbComp A) : Pr{let result ← step}[complete result ∧ result = value] =
      Pr{let result ← step}[result = value] := by
    apply prEvent_congr
    intro result
    constructor
    · exact And.right
    · intro equal
      exact ⟨equal ▸ done, equal⟩
  simpa only [same] using ordered (fun result => result = value)

/-- Pure assembly can alter values and metadata, but must preserve completion. -/
theorem map {left right : ProbComp A} {complete : A → Prop} (ordered : LE left right complete)
    (f : A → B) (finished : B → Prop) (preserves : ∀ value, finished (f value) ↔ complete value) :
    LE (f <$> left) (f <$> right) finished := by
  intro event
  have same (step : ProbComp A) : Pr{let value ← f <$> step}[finished value ∧ event value] =
      Pr{let value ← step}[complete value ∧ event (f value)] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ (fun value => and_congr_left (fun _ => preserves value))
  rw [same, same]
  exact ordered _

/-- Equivalent completion predicates describe the same restricted law. -/
theorem complete_congr {left right : ProbComp A} {first second : A → Prop}
    (same : ∀ value, first value ↔ second value) (ordered : LE left right first) : LE left right second := by
  intro event
  have predicate : (fun value => second value ∧ event value) = (fun value => first value ∧ event value) := by
    funext value
    exact propext (and_congr_left (fun _ => (same value).symm))
  rw [predicate]
  exact ordered event

/-- Observation-sensitive continuations preserve the completed order. Only
completed heads may contribute a completed final result. No independence
between the head's trace and its continuation is assumed. -/
theorem bind {left right : ProbComp A} {complete : A → Prop} (ordered : LE left right complete)
    (leftNext rightNext : A → ProbComp B) (finished : B → Prop)
    (next_ordered : ∀ value, complete value → LE (leftNext value) (rightNext value) finished)
    (skip : ∀ value, ¬complete value → Pr{let result ← leftNext value}[finished result] = 0) :
    LE (left >>= leftNext) (right >>= rightNext) finished := by
  intro event
  rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases done : complete value
  · exact mul_le_mul' (singleton ordered value done) (next_ordered value done event)
  · have zero : Pr{let result ← leftNext value}[finished result ∧ event result] = 0 := by
      apply le_antisymm
      · exact (prEvent_mono _ _ _ (fun _ present => present.1)).trans (by rw [skip value done])
      · exact bot_le
    rw [zero, mul_zero]
    exact bot_le

/-- A common fresh first draw can be followed by pointwise ordered branches. -/
theorem bind_same (step : ProbComp A) (leftNext rightNext : A → ProbComp B) (finished : B → Prop)
    (branches : ∀ value, LE (leftNext value) (rightNext value) finished) :
    LE (step >>= leftNext) (step >>= rightNext) finished := by
  apply bind (refl step (fun _ => True)) leftNext rightNext finished
  · intro value _
    exact branches value
  · intro value impossible
    exact (impossible trivial).elim

/-- Lifting through an injective observation erasure does not require choosing
or resampling an inverse. This handles proof-only typed observations. -/
theorem of_map_injective (f : A → B) (injective : Function.Injective f)
    {left right : ProbComp A} (complete : A → Prop) (finished : B → Prop)
    (preserves : ∀ value, finished (f value) ↔ complete value)
    (ordered : LE (f <$> left) (f <$> right) finished) : LE left right complete := by
  intro event
  have same (step : ProbComp A) :
      Pr{let value ← f <$> step}[finished value ∧ ∃ original, f original = value ∧ event original] =
        Pr{let value ← step}[complete value ∧ event value] := by
    rw [prEvent_map]
    apply prEvent_congr
    intro value
    constructor
    · rintro ⟨done, original, equal, present⟩
      have eqOriginal := injective equal
      subst original
      exact ⟨(preserves value).mp done, present⟩
    · rintro ⟨done, present⟩
      exact ⟨(preserves value).mpr done, value, rfl, present⟩
  rw [← same left, ← same right]
  exact ordered _

end

end FormalProof4FHE.HasteBoots.CompletedObservation
