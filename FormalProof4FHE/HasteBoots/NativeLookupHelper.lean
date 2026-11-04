module

public import FormalProof4FHE.HasteBoots.NativeLookupReciprocals
public import FormalProof4FHE.HasteBoots.ReciprocalMask

@[expose] public section

/-!
# Native helper-vector filling from the retained reciprocal table

The native zero-initialized vector is filled by a zip with witness table
indices, truncating at capacity. Invalid accessed indices are explicit
failure in this checked mathematical model, never default zero. Accepted
native witnesses must discharge that index-safety condition. Packed basis
serialization, helper commitment, and checked source refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeLookupHelper

noncomputable section

variable {K : Type} [Field K]

/-- Checked version of the native fill loop. Unread trailing indices are
ignored exactly as by the native zip. -/
def fill : ℕ → List K → List ℕ → Option (List K)
  | 0, _, _ => some []
  | capacity + 1, _, [] => some (List.replicate (capacity + 1) 0)
  | capacity + 1, table, index :: tail =>
      (table[index]?).bind (fun value =>
        (fill capacity table tail).bind (fun rest => some (value :: rest)))

/-- Successful filling always returns precisely the requested capacity. -/
theorem fill_length (capacity : ℕ) (table : List K) (indices : List ℕ) (values : List K)
    (filled : fill capacity table indices = some values) : values.length = capacity := by
  induction capacity generalizing indices values with
  | zero =>
    simp only [fill, Option.some.injEq] at filled
    subst values
    rfl
  | succ capacity ih =>
    cases indices with
    | nil =>
      simp only [fill, Option.some.injEq] at filled
      subst values
      exact List.length_replicate
    | cons index tail =>
      cases found : table[index]? with
      | none => simp only [fill, found, Option.bind_none] at filled; cases filled
      | some value =>
        cases restEq : fill capacity table tail with
        | none => simp only [fill, found, Option.bind_some, restEq, Option.bind_none] at filled; cases filled
        | some rest =>
          simp only [fill, found, Option.bind_some, restEq, Option.some.injEq] at filled
          subst values
          simp only [List.length_cons, ih tail rest restEq]

/-- The exact copy/truncate/zero-pad result for safe immutable indices.
The certificate links each source index to its actual table lookup. -/
theorem fill_spec (capacity : ℕ) (table : List K) (indices : List ℕ) (values : List K)
    (lookups : List.Forall₂ (fun index value => table[index]? = some value) indices values) :
    fill capacity table indices = some (values.take capacity ++ List.replicate (capacity - values.length) 0) := by
  induction lookups generalizing capacity with
  | nil => cases capacity <;> simp [fill]
  | @cons index value indices values known related ih =>
    cases capacity with
    | zero => simp [fill]
    | succ capacity =>
      simp only [fill, known, Option.bind_some, ih, List.take_succ_cons, List.length_cons,
        Nat.add_sub_add_right, List.cons_append]

variable [DecidableEq K]

/-- Every safe witness table index selects the same mathematical reciprocal
that the native public table sum uses. -/
theorem fill_reciprocals (policy : NativeLookupReciprocals.Policy) (r : K) (table : List K)
    (allowed : NativeLookupChallenge.allowed table r = true)
    (indices : List ℕ) (selected : List K)
    (lookups : List.Forall₂ (fun index value => table[index]? = some value) indices selected)
    (capacity : ℕ) :
    fill capacity (NativeLookupReciprocals.inverses policy r table) indices =
      some ((selected.map (fun value => (r + value)⁻¹)).take capacity ++
        List.replicate (capacity - selected.length) 0) := by
  have related : List.Forall₂
      (fun index inverse => (NativeLookupReciprocals.inverses policy r table)[index]? = some inverse)
      indices (selected.map (fun value => (r + value)⁻¹)) := by
    induction lookups with
    | nil => exact .nil
    | @cons index value indices values known rest ih =>
      apply List.Forall₂.cons ?_ ih
      rw [NativeLookupReciprocals.inverses_correct policy r table allowed, List.getElem?_map, known]
      rfl
  simpa only [List.length_map] using fill_spec capacity _ indices _ related

omit [DecidableEq K] in
/-- Active helper cells satisfy the literal native reciprocal identity;
zero padding satisfies the inactive branch without an inverse assumption. -/
theorem helper_identity (r source : K) (nonzero : r + source ≠ 0) :
    ReciprocalMask.residual r source ((r + source)⁻¹) true = 0 :=
  ReciprocalMask.honest_active r source nonzero

omit [DecidableEq K] in
/-- Native zero padding satisfies the inactive identity for every source. -/
theorem helper_inactive_identity (r source : K) :
    ReciprocalMask.residual r source 0 false = 0 :=
  ReciprocalMask.honest_inactive r source

variable {p degree : ℕ} [Algebra (ZMod p) K]

/-- The compiled batch's existing validity theorem supplies the precise
nonzero-denominator premise for either native inverse policy. -/
theorem completed_inverses (basis : Module.Basis (Fin degree) (ZMod p) K)
    (machine : NativeLookupBatch.Machine p K) (valid : NativeLookupBatch.Valid basis machine)
    (completed : NativeLookupBatch.Completed p K) (member : completed ∈ machine.completed)
    (y r : K) (weights table : List K) (transcript : NativeTranscript.Transcript)
    (finished : completed.selection.control = .finished y r weights table transcript)
    (policy : NativeLookupReciprocals.Policy) :
    NativeLookupReciprocals.inverses policy r table = table.map (fun value => (r + value)⁻¹) := by
  have selected := (valid.2 completed member).1.2.1
  unfold NativeLookupChallenge.SelectionValid at selected
  rw [finished] at selected
  exact NativeLookupReciprocals.inverses_correct policy r table selected.2.2

end

end FormalProof4FHE.HasteBoots.NativeLookupHelper
