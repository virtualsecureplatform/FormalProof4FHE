module

public import FormalProof4FHE.HasteBoots.OptionalUniformSequence

@[expose] public section

/-!
# Retrying completed candidates while preserving optional-sampler observations

A trial can itself suspend. Only an actually completed rejected candidate
starts another trial. The complete list of trial observations, including a
partial last trial, stays in the result. Both inner and outer prefix lengths
are analysis approximations, not runtime rejection or retry budgets.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.OptionalRejectionLoop

noncomputable section

structure Result (A Observation : Type) where
  value : Option A
  trials : List Observation

variable {A Observation : Type}

def cons (first : Observation) (tail : Result A Observation) : Result A Observation :=
  ⟨tail.value, first :: tail.trials⟩

def program (step : ProbComp Observation) (candidate : Observation → Option A) (accept : A → Prop)
    [DecidablePred accept] : ℕ → ProbComp (Result A Observation)
  | 0 => pure ⟨none, []⟩
  | fuel + 1 => do
    let first ← step
    match candidate first with
    | none => pure ⟨none, [first]⟩
    | some value => if accept value then pure ⟨some value, [first]⟩
                    else cons first <$> program step candidate accept fuel

def valueProgram (step : ProbComp (Option A)) (accept : A → Prop) [DecidablePred accept] : ℕ → ProbComp (Option A)
  | 0 => pure none
  | fuel + 1 => OptionalUniformSequence.bindProgram step
      (fun value => if accept value then pure (some value) else valueProgram step accept fuel)

/-- The exact query tree survives value projection. Partial trial work and
all retries stay in the execution even when their observation fields erase. -/
theorem value_erasure (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) :
    (fun result => result.value) <$> program step candidate accept fuel = valueProgram (candidate <$> step) accept fuel := by
  induction fuel with
  | zero => simp [program, valueProgram]
  | succ fuel ih =>
    rw [program, valueProgram, OptionalUniformSequence.bindProgram, map_bind, bind_map_left]
    congr 1
    funext first
    cases candidate first with
    | none => simp
    | some value =>
      by_cases accepted : accept value
      · simp [accepted]
      · simpa only [accepted, ite_false, cons, Functor.map_map] using ih

/-- A returned value came from an actually completed accepted trial. -/
theorem returned_accept (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) (result : Result A Observation)
    (supported : result ∈ support (program step candidate accept fuel)) (value : A)
    (returned : result.value = some value) : accept value := by
  induction fuel generalizing result with
  | zero =>
    simp only [program, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp at returned
  | succ fuel ih =>
    simp only [program, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, _, branch⟩ := supported
    cases tag : candidate first with
    | none =>
      simp only [tag, support_pure, Set.mem_singleton_iff] at branch
      subst result
      simp at returned
    | some head =>
      by_cases allowed : accept head
      · simp only [tag, allowed, ite_true, support_pure, Set.mem_singleton_iff] at branch
        subst result
        exact Option.some.inj returned ▸ allowed
      · simp only [tag, allowed, ite_false, support_map, Set.mem_image] at branch
        obtain ⟨tail, reached, equal⟩ := branch
        subst result
        exact ih tail reached returned

section Probability

variable [Fintype A] [SampleableType A]

/-- The finite accepted set is for analysis; the program checks the original
predicate directly instead of enumerating the field. -/
def accepted (accept : A → Prop) [DecidablePred accept] : Finset A := Finset.univ.filter accept

theorem value_success_succ (step : ProbComp (Option A)) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) (event : A → Prop) :
    Pr{let value ← valueProgram step accept (fuel + 1)}[value.elim False event] =
      completion * RejectionSampling.hit (accepted accept) event +
      (completion * RejectionSampling.reject (accepted accept)) *
        Pr{let value ← valueProgram step accept fuel}[value.elim False event] := by
  rw [valueProgram, OptionalUniformSequence.bind_probability step completion law]
  have branch := RejectionSampling.one_step_probability (accepted accept) (valueProgram step accept fuel) event
  simp only [accepted, Finset.mem_filter, Finset.mem_univ, true_and] at branch
  rw [branch, mul_add, mul_assoc]
  rfl

theorem value_probability (step : ProbComp (Option A)) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let value ← step}[value.elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) (event : A → Prop) :
    Pr{let value ← valueProgram step accept fuel}[value.elim False event] =
      (∑ attempt ∈ Finset.range fuel, (completion * RejectionSampling.reject (accepted accept)) ^ attempt) *
        (completion * RejectionSampling.hit (accepted accept) event) := by
  induction fuel with
  | zero => simp [valueProgram, prEvent_norm]
  | succ fuel ih =>
    rw [value_success_succ step completion law, ih, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, pow_succ', add_mul]
    rw [← Finset.mul_sum]
    ac_rfl

/-- Successful trial values keep the whole nested completion/rejection law;
no failed inner trial is replaced by a dummy candidate or retried as rejection. -/
theorem probability (step : ProbComp Observation) (candidate : Observation → Option A) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let first ← step}[(candidate first).elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) (event : A → Prop) :
    Pr{let result ← program step candidate accept fuel}[result.value.elim False event] =
      (∑ attempt ∈ Finset.range fuel, (completion * RejectionSampling.reject (accepted accept)) ^ attempt) *
        (completion * RejectionSampling.hit (accepted accept) event) := by
  have kernel : ∀ event : A → Prop, Pr{let first ← candidate <$> step}[first.elim False event] =
      completion * Pr{let value ← $ᵗ A}[event value] := by intro event; simpa only [prEvent_map] using law event
  have bounded := value_probability (candidate <$> step) completion kernel accept fuel event
  rw [← value_erasure] at bounded
  simpa only [prEvent_map] using bounded

variable [DecidableEq A]

/-- Finite nested prefixes retain their real completion mass. Accepted
values have the exact normalized domain law, even when inner trials suspend. -/
theorem success_scaled (step : ProbComp Observation) (candidate : Observation → Option A) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let first ← step}[(candidate first).elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (nonempty : (accepted accept).Nonempty) (fuel : ℕ) (event : A → Prop) :
    Pr{let result ← program step candidate accept fuel}[result.value.elim False event] =
      Pr{let result ← program step candidate accept fuel}[result.value.elim False (fun _ => True)] *
        RejectionSampling.eventProbability (accepted accept) event := by
  have positive : 0 < RejectionSampling.hit (accepted accept) (fun _ => True) :=
    (SampleableType.prEvent_uniformSample_pos_iff _).mpr (by
      obtain ⟨value, member⟩ := nonempty
      exact ⟨value, member, trivial⟩)
  have finite : RejectionSampling.hit (accepted accept) (fun _ => True) ≠ ⊤ := ne_of_lt (prEvent_lt_top _)
  rw [probability step candidate completion law, probability step candidate completion law,
    RejectionSampling.eventProbability_eq_ratio, div_eq_mul_inv]
  calc _ = ((∑ attempt ∈ Finset.range fuel, (completion * RejectionSampling.reject (accepted accept)) ^ attempt) *
          (completion * RejectionSampling.hit (accepted accept) event)) *
        (RejectionSampling.hit (accepted accept) (fun _ => True) *
          (RejectionSampling.hit (accepted accept) (fun _ => True))⁻¹) := by
            rw [ENNReal.mul_inv_cancel positive.ne' finite, mul_one]
       _ = _ := by ac_rfl

/-- Every finite approximation is dominated by the same full accepted-domain
law. No normalized-away suspension or protocol retry cap is introduced. -/
theorem event_le_uniform (step : ProbComp Observation) (candidate : Observation → Option A) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let first ← step}[(candidate first).elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (nonempty : (accepted accept).Nonempty) (fuel : ℕ) (event : A → Prop) :
    Pr{let result ← program step candidate accept fuel}[result.value.elim False event] ≤
      Pr{let value ← ($ (accepted accept) : OptionT ProbComp A)}[event value] := by
  rw [success_scaled step candidate completion law accept nonempty fuel event, RejectionSampling.eventProbability_eq_uniform]
  exact (mul_le_mul_left (prEvent_le_one _) _).trans_eq (one_mul _)

end Probability

end

end FormalProof4FHE.HasteBoots.OptionalRejectionLoop
