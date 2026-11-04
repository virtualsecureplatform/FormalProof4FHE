module

public import FormalProof4FHE.HasteBoots.NativeGoldInterpolationPolynomial

@[expose] public section

/-!
# Literal ordered scalar-batch claim updates

Native verification mutates the expected vector through a zip with the round
messages. Missing messages leave the remaining claims untouched and extra
messages are ignored. The preflight count invariant eliminates both malformed
cases; it is not replaced by a truncating map of the messages.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchUpdate

open NativeGoldExtensionArithmetic NativeScalarBatchWire

/-- Exact partial interpolation and zip-update order of the native verifier. -/
def update : List Word → List Message → Word → Option (List Word)
  | [], _, _ => some []
  | expected, [], _ => some expected
  | _ :: expected, message :: messages, point =>
      (NativeGoldInterpolation.interpolate message.evaluations.val point).bind (fun value =>
        (update expected messages point).map (fun rest => value :: rest))

theorem update_length (expected : List Word) (messages : List Message) (point : Word) (output : List Word)
    (success : update expected messages point = some output) : output.length = expected.length := by
  induction expected generalizing messages output with
  | nil => simp only [update, Option.some.injEq] at success; subst output; rfl
  | cons prior expected ih =>
    cases messages with
    | nil => simp only [update, Option.some.injEq] at success; subst output; rfl
    | cons message messages =>
      simp only [update] at success
      cases found : NativeGoldInterpolation.interpolate message.evaluations.val point with
      | none => simp only [found, Option.bind_none] at success; contradiction
      | some value =>
        simp only [found, Option.bind_some] at success
        cases rest : update expected messages point with
        | none => simp only [rest, Option.map_none] at success; contradiction
        | some values =>
          simp only [rest, Option.map_some, Option.some.injEq] at success
          subst output
          simp only [List.length_cons, ih messages values rest]

/-- Under the native count invariant every received message updates its
own claim, in statement order. No message or output is dropped. -/
theorem update_related (expected : List Word) (messages : List Message) (point : Word) (output : List Word)
    (count : expected.length = messages.length) (success : update expected messages point = some output) :
    List.Forall₂ (fun message value => NativeGoldInterpolation.interpolate message.evaluations.val point = some value)
      messages output := by
  induction expected generalizing messages output with
  | nil =>
    have empty : messages = [] := by simpa only [List.length_nil, List.length_eq_zero_iff] using count.symm
    subst messages
    simp only [update, Option.some.injEq] at success
    subst output
    exact .nil
  | cons prior expected ih =>
    cases messages with
    | nil => simp at count
    | cons message messages =>
      simp only [update] at success
      cases found : NativeGoldInterpolation.interpolate message.evaluations.val point with
      | none => simp only [found, Option.bind_none] at success; contradiction
      | some value =>
        simp only [found, Option.bind_some] at success
        cases rest : update expected messages point with
        | none => simp only [rest, Option.map_none] at success; contradiction
        | some values =>
          simp only [rest, Option.map_some, Option.some.injEq] at success
          subst output
          exact .cons found (ih messages values (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using count) rest)

theorem update_success (expected : List Word) (messages : List Message) (point : Word)
    (safe : ∀ message ∈ messages, ∃ value, NativeGoldInterpolation.interpolate message.evaluations.val point = some value) :
    ∃ output, update expected messages point = some output := by
  induction expected generalizing messages with
  | nil => exact ⟨[], rfl⟩
  | cons prior expected ih =>
    cases messages with
    | nil => exact ⟨prior :: expected, rfl⟩
    | cons message messages =>
      obtain ⟨value, found⟩ := safe message (by simp)
      obtain ⟨rest, later⟩ := ih messages (fun entry member => safe entry (by simp [member]))
      exact ⟨value :: rest, by simp only [update, found, Option.bind_some, later, Option.map_some]⟩

end FormalProof4FHE.HasteBoots.NativeScalarBatchUpdate
