module

public import FormalProof4FHE.HasteBoots.ObservedOptionalVector

@[expose] public section

/-!
# Work and suspension bounds for actual sequential observed vectors

Every fresh call retains its observation, including the final suspended call.
The support bound and failure union bound follow from the program's gate.
-/

open OracleSpec OracleComp
open scoped Classical
open FormalProof4FHE.HasteBoots.ObservedOptionalVector

namespace FormalProof4FHE.HasteBoots.ObservedVectorTail

noncomputable section

variable {A Observation : Type}

/-- The full vector work includes every started observation, even on failure. -/
theorem consumed_le (step : ProbComp Observation) (candidate : Observation → Option A)
    (cost : Observation → ℕ) (bound : ℕ) (head_le : ∀ first ∈ support step, cost first ≤ bound)
    (count : ℕ) (result : Result A Observation count) (supported : result ∈ support (program step candidate count)) :
    consumed cost result ≤ count * bound := by
  induction count with
  | zero =>
    simp only [program, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp [consumed]
  | succ count ih =>
    simp only [program, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, reached, branch⟩ := supported
    have head := head_le first reached
    cases tag : candidate first with
    | none =>
      simp only [tag, support_pure, Set.mem_singleton_iff] at branch
      subst result
      simpa only [consumed, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
        head.trans (by rw [Nat.succ_mul]; omega)
    | some value =>
      simp only [tag, support_map, Set.mem_image] at branch
      obtain ⟨tail, tail_reached, equal⟩ := branch
      subst result
      rw [consumed_cons, Nat.succ_mul]
      exact (Nat.add_le_add head (ih tail tail_reached)).trans_eq (Nat.add_comm _ _)

/-- Only a completed head starts the suffix. The failure bound is derived
from this actual sequential query syntax, not supplied as independence. -/
theorem suspended_le (step : ProbComp Observation) (candidate : Observation → Option A) (count : ℕ) :
    Pr{let result ← program step candidate count}[result.values = none] ≤
      (count : ENNReal) * Pr{let first ← step}[candidate first = none] := by
  induction count with
  | zero => simp [program]
  | succ count ih =>
    rw [program]
    have bound := prEvent_bind_le_prEvent_add step
      (fun first => match candidate first with
        | none => pure (⟨none, [], [first]⟩ : Result A Observation (count + 1))
        | some value => cons first value <$> program step candidate count)
      (fun first => candidate first = none) (fun result => result.values = none)
      (ε := (count : ENNReal) * Pr{let first ← step}[candidate first = none]) (by
        intro first completed
        cases tag : candidate first with
        | none => exact (completed tag).elim
        | some value => simpa [tag, cons] using ih)
    have scalar : Pr{let first ← step}[candidate first = none] +
        (count : ENNReal) * Pr{let first ← step}[candidate first = none] =
        ((count + 1 : ℕ) : ENNReal) * Pr{let first ← step}[candidate first = none] := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    exact bound.trans_eq scalar

end

end FormalProof4FHE.HasteBoots.ObservedVectorTail
