module

public import FormalProof4FHE.HasteBoots.CompletedObservation
public import FormalProof4FHE.HasteBoots.OptionalRejectionLoop
public import FormalProof4FHE.HasteBoots.ObservedOptionalVector

@[expose] public section

/-!
# Nested optional loops and fresh vectors retain completed observations

The order includes all completed and rejected trial records. Only a completed
head can lead to completion, and arbitrary observation-sensitive events are
allowed. No uniform value law or cost/value independence is required.
-/

open OracleSpec OracleComp
open scoped Classical

namespace FormalProof4FHE.HasteBoots.OptionalTraceOrder

noncomputable section

variable {A Observation : Type}

def loopComplete (result : OptionalRejectionLoop.Result A Observation) : Prop := result.value ≠ none

/-- Improving each completed inner observation improves the entire completed
outer rejection observation, including every rejected inner trace. -/
theorem loop_steps {left right : ProbComp Observation} (candidate : Observation → Option A)
    (ordered : CompletedObservation.LE left right (fun first => candidate first ≠ none))
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) :
    CompletedObservation.LE (OptionalRejectionLoop.program left candidate accept fuel)
      (OptionalRejectionLoop.program right candidate accept fuel) loopComplete := by
  induction fuel with
  | zero => exact CompletedObservation.refl _ _
  | succ fuel ih =>
    change CompletedObservation.LE
      (left >>= fun first => match candidate first with
        | none => pure ⟨none, [first]⟩
        | some value => if accept value then pure ⟨some value, [first]⟩
            else OptionalRejectionLoop.cons first <$> OptionalRejectionLoop.program left candidate accept fuel)
      (right >>= fun first => match candidate first with
        | none => pure ⟨none, [first]⟩
        | some value => if accept value then pure ⟨some value, [first]⟩
            else OptionalRejectionLoop.cons first <$> OptionalRejectionLoop.program right candidate accept fuel) loopComplete
    apply CompletedObservation.bind ordered
    · intro first done
      cases tag : candidate first with
      | none => exact (done tag).elim
      | some value =>
        simp only
        by_cases accepted : accept value
        · simp only [accepted, ite_true]
          exact CompletedObservation.refl _ _
        · simp only [accepted, ite_false]
          exact CompletedObservation.map ih _ loopComplete (fun _ => Iff.rfl)
    · intro first suspended
      have tag : candidate first = none := by simpa only [not_not] using suspended
      simp [tag, loopComplete, prEvent_norm]

/-- Extending the outer approximation preserves earlier completed trials. -/
theorem loop_step (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) :
    CompletedObservation.LE (OptionalRejectionLoop.program step candidate accept fuel)
      (OptionalRejectionLoop.program step candidate accept (fuel + 1)) loopComplete := by
  induction fuel with
  | zero => exact CompletedObservation.pure_incomplete (⟨none, []⟩ : OptionalRejectionLoop.Result A Observation) loopComplete (by simp [loopComplete]) _
  | succ fuel ih =>
    change CompletedObservation.LE
      (step >>= fun first => match candidate first with
        | none => pure ⟨none, [first]⟩
        | some value => if accept value then pure ⟨some value, [first]⟩
            else OptionalRejectionLoop.cons first <$> OptionalRejectionLoop.program step candidate accept fuel)
      (step >>= fun first => match candidate first with
        | none => pure ⟨none, [first]⟩
        | some value => if accept value then pure ⟨some value, [first]⟩
            else OptionalRejectionLoop.cons first <$> OptionalRejectionLoop.program step candidate accept (fuel + 1)) loopComplete
    apply CompletedObservation.bind_same
    intro first
    cases tag : candidate first with
    | none => simp only; exact CompletedObservation.refl _ _
    | some value =>
      simp only
      by_cases accepted : accept value
      · simp only [accepted, ite_true]
        exact CompletedObservation.refl _ _
      · simp only [accepted, ite_false]
        exact CompletedObservation.map ih _ loopComplete (fun _ => Iff.rfl)

theorem loop_outer (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] {first second : ℕ} (ordered : first ≤ second) :
    CompletedObservation.LE (OptionalRejectionLoop.program step candidate accept first)
      (OptionalRejectionLoop.program step candidate accept second) loopComplete := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
  clear ordered
  induction extra with
  | zero => exact CompletedObservation.refl _ _
  | succ extra ih => exact CompletedObservation.trans ih (loop_step step candidate accept (first + extra))

def vectorComplete {count : ℕ} (result : ObservedOptionalVector.Result A Observation count) : Prop := result.values ≠ none

/-- Fresh repetition preserves the full ordered observation law, not just an
all-coordinate value event or a successful completion normalization factor. -/
theorem vector {left right : ProbComp Observation} (candidate : Observation → Option A)
    (ordered : CompletedObservation.LE left right (fun first => candidate first ≠ none)) (count : ℕ) :
    CompletedObservation.LE (ObservedOptionalVector.program left candidate count)
      (ObservedOptionalVector.program right candidate count) vectorComplete := by
  induction count with
  | zero => exact CompletedObservation.refl _ _
  | succ count ih =>
    change CompletedObservation.LE
      (left >>= fun first => match candidate first with
        | none => pure ⟨none, [], [first]⟩
        | some head => ObservedOptionalVector.cons first head <$> ObservedOptionalVector.program left candidate count)
      (right >>= fun first => match candidate first with
        | none => pure ⟨none, [], [first]⟩
        | some head => ObservedOptionalVector.cons first head <$> ObservedOptionalVector.program right candidate count) vectorComplete
    apply CompletedObservation.bind ordered
    · intro first done
      cases tag : candidate first with
      | none => exact (done tag).elim
      | some head =>
        simp only
        apply CompletedObservation.map ih _ vectorComplete
        intro tail
        cases tail.values <;> simp [vectorComplete, ObservedOptionalVector.cons]
    · intro first suspended
      have tag : candidate first = none := by simpa only [not_not] using suspended
      simp [tag, vectorComplete, prEvent_norm]

end

end FormalProof4FHE.HasteBoots.OptionalTraceOrder
