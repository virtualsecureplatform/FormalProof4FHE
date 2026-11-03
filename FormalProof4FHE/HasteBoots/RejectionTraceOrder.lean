module

public import FormalProof4FHE.HasteBoots.CompletedObservation
public import FormalProof4FHE.HasteBoots.CanonicalByteSampler

@[expose] public section

/-!
# Completed rejection traces survive larger operational approximations

The observation includes every rejected draw and the final accepted draw.
The order therefore applies to arbitrary trace-sensitive events, rather
than only to the marginal accepted field value.
-/

open OracleSpec OracleComp
open scoped Classical

namespace FormalProof4FHE.HasteBoots.RejectionTraceOrder

noncomputable section

variable {A : Type} [DecidableEq A] [SampleableType A]

def complete (result : RejectionSampling.Result A) : Prop := result.1 ≠ none

/-- One more rejection approximation preserves every earlier completed trace. -/
theorem step (accepted : Finset A) (fuel : ℕ) :
    CompletedObservation.LE (RejectionSampling.runPrefix accepted fuel)
      (RejectionSampling.runPrefix accepted (fuel + 1)) complete := by
  induction fuel with
  | zero => exact CompletedObservation.pure_incomplete (none, []) complete (by simp [complete]) _
  | succ fuel ih =>
    change CompletedObservation.LE
      (($ᵗ A) >>= fun raw => if raw ∈ accepted then pure (some raw, [raw])
        else (fun result => (result.1, raw :: result.2)) <$> RejectionSampling.runPrefix accepted fuel)
      (($ᵗ A) >>= fun raw => if raw ∈ accepted then pure (some raw, [raw])
        else (fun result => (result.1, raw :: result.2)) <$> RejectionSampling.runPrefix accepted (fuel + 1)) complete
    apply CompletedObservation.bind_same
    intro raw
    by_cases member : raw ∈ accepted
    · simp only [member, ite_true]
      exact CompletedObservation.refl _ _
    · simp only [member, ite_false]
      exact CompletedObservation.map ih _ complete (fun _ => Iff.rfl)

/-- Any larger prefix preserves all completed raw observations. -/
theorem monotone (accepted : Finset A) {first second : ℕ} (ordered : first ≤ second) :
    CompletedObservation.LE (RejectionSampling.runPrefix accepted first)
      (RejectionSampling.runPrefix accepted second) complete := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
  clear ordered
  induction extra with
  | zero => exact CompletedObservation.refl _ _
  | succ extra ih => exact CompletedObservation.trans ih (step accepted (first + extra))

/-- Native masked-byte rejection inherits the full completed-trace order by
exact query-program equality with the generic rejection loop. -/
theorem canonical (p : ℕ) {first second : ℕ} (ordered : first ≤ second) :
    CompletedObservation.LE (CanonicalByteSampler.runPrefix p first)
      (CanonicalByteSampler.runPrefix p second) complete := by
  rw [CanonicalByteSampler.runPrefix_eq, CanonicalByteSampler.runPrefix_eq]
  exact monotone _ ordered

end

end FormalProof4FHE.HasteBoots.RejectionTraceOrder
