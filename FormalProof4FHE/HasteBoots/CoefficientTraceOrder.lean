module

public import FormalProof4FHE.HasteBoots.RejectionTraceOrder
public import FormalProof4FHE.HasteBoots.CanonicalExtensionSampler

@[expose] public section

/-!
# Completed coefficient and extension observations under larger byte prefixes

Every accepted coefficient, rejected raw chunk, and completed extension value
is part of the ordered observation. Later code may inspect all of them.
-/

open OracleSpec OracleComp
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CoefficientTraceOrder

noncomputable section

def complete {p count : ℕ} (result : CanonicalCoefficientVector.Result p count) : Prop := result.values ≠ none

/-- Sequential coefficient assembly preserves completed raw observations as
the per-coefficient byte approximation grows. -/
theorem coefficients (p count : ℕ) {first second : ℕ} (ordered : first ≤ second) :
    CompletedObservation.LE (CanonicalCoefficientVector.program p first count)
      (CanonicalCoefficientVector.program p second count) complete := by
  induction count with
  | zero => exact CompletedObservation.refl _ _
  | succ count ih =>
    change CompletedObservation.LE
      (CanonicalByteSampler.runPrefix p first >>= fun head => match head.1 with
        | none => pure ⟨none, [], head.2⟩
        | some raw => CanonicalCoefficientVector.cons raw head.2 <$> CanonicalCoefficientVector.program p first count)
      (CanonicalByteSampler.runPrefix p second >>= fun head => match head.1 with
        | none => pure ⟨none, [], head.2⟩
        | some raw => CanonicalCoefficientVector.cons raw head.2 <$> CanonicalCoefficientVector.program p second count) complete
    apply CompletedObservation.bind (RejectionTraceOrder.canonical p ordered)
    · intro head done
      cases tag : head.1 with
      | none => simp [RejectionTraceOrder.complete, tag] at done
      | some raw =>
        simp only
        apply CompletedObservation.map ih _ complete
        intro tail
        cases tag : tail.values <;> simp [complete, CanonicalCoefficientVector.cons, tag]
    · intro head suspended
      have tag : head.1 = none := by simpa only [RejectionTraceOrder.complete, not_not] using suspended
      simp [tag, complete, prEvent_norm]

/-- Pure basis assembly retains the same full coefficient observation. -/
theorem extension {p degree : ℕ} {K : Type} [AddCommGroup K] [Module (ZMod p) K]
    (basis : Module.Basis (Fin degree) (ZMod p) K) (count : ℕ) {first second : ℕ} (ordered : first ≤ second) :
    CompletedObservation.LE (CanonicalExtensionSampler.program basis first count)
      (CanonicalExtensionSampler.program basis second count) (fun result => result.1 ≠ none) := by
  unfold CanonicalExtensionSampler.program
  apply CompletedObservation.map (coefficients p (count * degree) ordered)
  intro coefficients
  cases tag : coefficients.values <;> simp [complete, tag]

end

end FormalProof4FHE.HasteBoots.CoefficientTraceOrder
