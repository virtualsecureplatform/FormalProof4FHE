module

public import FormalProof4FHE.HasteBoots.OptionalUniformSequence
public import FormalProof4FHE.HasteBoots.OptionalRejectionWork

@[expose] public section

/-!
# Fresh optional samples with ordered retained observations

A suspended sample stops the vector, preserving all earlier completed values
and every started observation. The optional view erases only metadata and
has exactly the same primitive queries. Independence is between fresh calls,
not between coordinates inside one sample. No scaled uniform law is assumed.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.ObservedOptionalVector

noncomputable section

variable {A Observation : Type}

structure Result (A Observation : Type) (count : ℕ) where
  values : Option (Fin count → A)
  completed : List A
  trials : List Observation

def cons {count : ℕ} (first : Observation) (head : A) (tail : Result A Observation count) : Result A Observation (count + 1) :=
  ⟨tail.values.map (Fin.cons head), head :: tail.completed, first :: tail.trials⟩

def program (step : ProbComp Observation) (candidate : Observation → Option A) :
    (count : ℕ) → ProbComp (Result A Observation count)
  | 0 => pure ⟨some Fin.elim0, [], []⟩
  | count + 1 => do
    let first ← step
    match candidate first with
    | none => pure ⟨none, [], [first]⟩
    | some head => cons first head <$> program step candidate count

/-- The optional view is a monadic sequence of fresh calls, rather than a
uniform sample or reuse of a previously sampled value. -/
def view (step : ProbComp Observation) (candidate : Observation → Option A) :
    (count : ℕ) → OptionT ProbComp (Fin count → A)
  | 0 => pure Fin.elim0
  | count + 1 => do
    let head ← (OptionT.mk (candidate <$> step) : OptionT ProbComp A)
    Fin.cons head <$> view step candidate count

/-- Exact query-program equality; the view preserves the suspension gate. -/
theorem values_erasure (step : ProbComp Observation) (candidate : Observation → Option A) (count : ℕ) :
    (fun result => result.values) <$> program step candidate count = (view step candidate count).run := by
  induction count with
  | zero => simp [program, view]
  | succ count ih =>
    rw [program, map_bind]
    simp only [view, OptionT.run_bind, OptionT.run_map, OptionT.run_mk, Option.elimM, Option.elim]
    rw [bind_map_left]
    congr 1
    funext first
    cases candidate first with
    | none => simp
    | some head =>
      simp only [cons, Functor.map_map]
      simpa only [Functor.map_map] using congrArg (fun computation : ProbComp (Option (Fin count → A)) =>
        (Option.map (Fin.cons (n := count) (α := fun _ => A) head)) <$> computation) ih

def All {count : ℕ} (event : A → Prop) (values : Fin count → A) : Prop := ∀ index, event (values index)

theorem all_cons {count : ℕ} (event : A → Prop) (head : A) (tail : Fin count → A) :
    All event (Fin.cons head tail) ↔ event head ∧ All event tail := by simp [All, Fin.forall_fin_succ]

/-- The exact all-pass probability is a power of the actual successful
single-draw event mass, including its incomplete mass. -/
theorem view_probability (step : ProbComp Observation) (candidate : Observation → Option A)
    (count : ℕ) (event : A → Prop) :
    Pr{let values ← view step candidate count}[All event values] =
      Pr{let first ← step}[(candidate first).elim False event] ^ count := by
  induction count with
  | zero => simp [view, All, prEvent_norm]
  | succ count ih =>
    have independent := prEvent_bind_and_eq_mul (OptionT.mk (candidate <$> step) : OptionT ProbComp A)
      (fun _ : A => view step candidate count) (All event) event (fun _ => rfl)
    calc _ = Pr{let head ← (OptionT.mk (candidate <$> step) : OptionT ProbComp A); let tail ← view step candidate count}[All event tail ∧ event head] := by
            simp only [view, prEvent_norm, all_cons, and_comm]
         _ = Pr{let tail ← view step candidate count}[All event tail] *
           Pr{let head ← (OptionT.mk (candidate <$> step) : OptionT ProbComp A)}[event head] := independent
         _ = _ := by
          rw [ih, OptionT.prEvent_eq_run]
          change _ * Pr{let value ← candidate <$> step}[value.elim False event] = _
          rw [prEvent_map, pow_succ]

theorem probability (step : ProbComp Observation) (candidate : Observation → Option A) (count : ℕ) (event : A → Prop) :
    Pr{let result ← program step candidate count}[result.values.elim False (All event)] =
      Pr{let first ← step}[(candidate first).elim False event] ^ count := by
  have law := view_probability step candidate count event
  rw [OptionT.prEvent_eq_run, ← values_erasure, prEvent_map] at law
  exact law

/-- A property established for supported successful single draws holds for
every coordinate of a supported completed vector. Suspension proves nothing
about a fabricated fallback value. -/
theorem returned_property (step : ProbComp Observation) (candidate : Observation → Option A)
    (event : A → Prop)
    (safe : ∀ first, first ∈ support step → ∀ value, candidate first = some value → event value)
    (count : ℕ) (result : Result A Observation count) (supported : result ∈ support (program step candidate count))
    (values : Fin count → A) (returned : result.values = some values) : All event values := by
  induction count with
  | zero => exact fun index => Fin.elim0 index
  | succ count ih =>
    simp only [program, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, reached, branch⟩ := supported
    cases tag : candidate first with
    | none =>
      simp only [tag, support_pure, Set.mem_singleton_iff] at branch
      subst result
      simp at returned
    | some head =>
      simp only [tag, support_map, Set.mem_image] at branch
      obtain ⟨tail, tailReached, equal⟩ := branch
      subst result
      cases tailTag : tail.values with
      | none => simp [cons, tailTag] at returned
      | some rest =>
        have equalValues : Fin.cons head rest = values := by
          simpa only [cons, tailTag, Option.map_some, Option.some.injEq] using returned
        rw [← equalValues, all_cons]
        exact ⟨safe first reached head tag, ih tail tailReached rest tailTag⟩

def consumed (cost : Observation → ℕ) {count : ℕ} (result : Result A Observation count) : ℕ := (result.trials.map cost).sum

theorem consumed_cons (cost : Observation → ℕ) {count : ℕ} (first : Observation) (head : A) (tail : Result A Observation count) :
    consumed cost (cons first head tail) = cost first + consumed cost tail := by simp [consumed, cons]

def expectedCost (step : ProbComp Observation) (candidate : Observation → Option A) (cost : Observation → ℕ) (count : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (consumed cost result : ENNReal)) <$> program step candidate count]

private theorem expected_const {B : Type} (step : ProbComp B) (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun _ => cost) <$> step]) = cost := by
  let _ : MeasurableSpace B := ⊤
  rw [lintegral_id_evalDist_map]
  simp

private theorem expected_ite {B : Type} (step : ProbComp B) (event : B → Prop) [DecidablePred event] (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun value => if event value then cost else 0) <$> step]) =
      Pr{let value ← step}[event value] * cost := by
  let _ : MeasurableSpace B := ⊤
  rw [lintegral_id_evalDist_map, prEvent_eq_evalDist_of_discrete]
  have same : (fun value => if event value then cost else 0) = {value | event value}.indicator (fun _ => cost) := by
    funext value
    by_cases present : event value <;> simp [present, Set.indicator]
  rw [same, lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

theorem expectedCost_zero (step : ProbComp Observation) (candidate : Observation → Option A) (cost : Observation → ℕ) :
    expectedCost step candidate cost 0 = 0 := by simp [expectedCost, program, consumed, evalDist_pure]

/-- Every started draw is charged even when it suspends. Completion gates
only the cost of subsequent draws; no cost/value independence is needed. -/
theorem expectedCost_succ (step : ProbComp Observation) (candidate : Observation → Option A) (cost : Observation → ℕ) (count : ℕ) :
    expectedCost step candidate cost (count + 1) = OptionalRejectionWork.headCost step cost +
      Pr{let first ← step}[(candidate first).elim False (fun _ => True)] * expectedCost step candidate cost count := by
  rw [expectedCost, program, lintegral_id_evalDist_map_bind]
  have point : ∀ first : Observation,
      (∫⁻ value, value ∂𝒟[(fun result : Result A Observation (count + 1) => (consumed cost result : ENNReal)) <$>
        (match candidate first with
         | none => pure (⟨none, [], [first]⟩ : Result A Observation (count + 1))
         | some head => cons first head <$> program step candidate count)]) =
      (cost first : ENNReal) + if (candidate first).elim False (fun _ => True)
        then expectedCost step candidate cost count else 0 := by
    intro first
    cases candidate first with
    | none => simp [consumed, evalDist_pure]
    | some head =>
      simp only [Functor.map_map]
      have splitCost : (fun tail : Result A Observation count => (consumed cost (cons first head tail) : ENNReal)) =
          (fun tail => (cost first : ENNReal) + (consumed cost tail : ENNReal)) := by
        funext tail
        rw [consumed_cons, Nat.cast_add]
      rw [splitCost, lintegral_id_evalDist_map_add, expected_const]
      simp [expectedCost]
  have observed := congrArg (fun observation : Observation → ENNReal =>
    ∫⁻ value, value ∂𝒟[observation <$> step]) (funext point)
  refine observed.trans ?_
  rw [lintegral_id_evalDist_map_add, expected_ite]
  rfl

/-- Finite work is the single-draw mean times the actual completion-prefix
sum, rather than count times a mean conditioned on successful output. -/
theorem expectedCost_formula (step : ProbComp Observation) (candidate : Observation → Option A) (cost : Observation → ℕ) (count : ℕ) :
    expectedCost step candidate cost count = OptionalRejectionWork.headCost step cost *
      (∑ index ∈ Finset.range count, Pr{let first ← step}[(candidate first).elim False (fun _ => True)] ^ index) := by
  induction count with
  | zero => simp [expectedCost_zero]
  | succ count ih =>
    rw [expectedCost_succ, ih, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', mul_add, mul_one]
    rw [← Finset.mul_sum]
    ac_rfl

end

end FormalProof4FHE.HasteBoots.ObservedOptionalVector
