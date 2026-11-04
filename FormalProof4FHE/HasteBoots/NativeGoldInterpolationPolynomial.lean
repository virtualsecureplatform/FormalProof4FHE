module

public import FormalProof4FHE.HasteBoots.NativeGoldInterpolationSafety
public import FormalProof4FHE.HasteBoots.NativeInterpolationPolynomial

@[expose] public section

/-!
# Polynomial semantics of actual raw Goldilocks interpolation

Every received width-valid vector supplies its own bounded-degree polynomial.
The literal raw interpolation maps to its evaluation, using the actual native
node check. The scalar recurrence then has the polynomial semantics required
by the soundness argument.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldInterpolationPolynomial

open NativeFields NativeExtensionFields NativeFieldWire NativeGoldExtensionArithmetic
open NativeScalarBatchWire NativeScalarBatchPreflight

noncomputable section

def polynomial (degree : ℕ) (values : List Word) (width : values.length = degree + 1) : Polynomial Goldilocks3 :=
  NativeInterpolationPolynomial.polynomial degree (values.map goldExtensionValue)
    (by simpa only [List.length_map] using width)

theorem nodes_nonzero (degree : ℕ) (nodes : nodesFrom degree NativeGoldLookup.zero = true) :
    ∀ j, 0 < j → j ≤ degree → (j : Goldilocks3) ≠ 0 := by
  simpa only [NativeGoldLookup.zero_value, zero_add] using (nodesFrom_iff _ _).mp nodes

theorem polynomial_degree (degree : ℕ) (values : List Word) (width : values.length = degree + 1)
    (nodes : nodesFrom degree NativeGoldLookup.zero = true) :
    (polynomial degree values width).natDegree ≤ degree :=
  NativeInterpolationPolynomial.polynomial_degree degree (values.map goldExtensionValue) _
    (nodes_nonzero degree nodes)

theorem polynomial_node (degree : ℕ) (values : List Word) (width : values.length = degree + 1)
    (nodes : nodesFrom degree NativeGoldLookup.zero = true) (node : Fin (degree + 1)) :
    (polynomial degree values width).eval (node.val : Goldilocks3) =
      goldExtensionValue (values[node.val]'(by rw [width]; exact node.isLt)) := by
  have atNode := NativeInterpolationPolynomial.polynomial_node degree (values.map goldExtensionValue)
    (by simpa only [List.length_map] using width) (nodes_nonzero degree nodes) node
  simpa only [polynomial, List.getElem_map] using atNode

/-- The full partial raw computation evaluates the received polynomial; its
degree bound and successful evaluation are derived, not supplied by the caller. -/
theorem interpolate_value (degree : ℕ) (values : List Word) (width : values.length = degree + 1)
    (nodes : nodesFrom degree NativeGoldLookup.zero = true) (point : Word) :
    (NativeGoldInterpolation.interpolate values point).map goldExtensionValue =
      some ((polynomial degree values width).eval (goldExtensionValue point)) := by
  rw [NativeGoldInterpolation.interpolate_value]
  exact NativeInterpolationPolynomial.interpolate_value degree (values.map goldExtensionValue)
    (by simpa only [List.length_map] using width) (nodes_nonzero degree nodes) (goldExtensionValue point)

/-- The native first-two-entry check is exactly the polynomial recurrence. -/
theorem recurrence_polynomial (degree : ℕ) (message : Message)
    (width : message.evaluations.val.length = degree + 1) (positive : 0 < degree)
    (nodes : nodesFrom degree NativeGoldLookup.zero = true) (claim : Word) :
    recurrence message claim = true ↔
      (polynomial degree message.evaluations.val width).eval 0 +
        (polynomial degree message.evaluations.val width).eval 1 = goldExtensionValue claim := by
  rcases message with ⟨⟨values, fits⟩⟩
  cases values with
  | nil => simp at width
  | cons first rest =>
    cases rest with
    | nil => simp only [List.length_cons, List.length_nil] at width; omega
    | cons second tail =>
      have atZero := polynomial_node degree (first :: second :: tail) width nodes ⟨0, by omega⟩
      have atOne := polynomial_node degree (first :: second :: tail) width nodes ⟨1, by omega⟩
      simp only [Nat.cast_zero, List.getElem_cons_zero] at atZero
      simp only [Nat.cast_one, List.getElem_cons_succ, List.getElem_cons_zero] at atOne
      rw [atZero, atOne]
      exact NativeScalarBatchPreflight.recurrence_iff first second tail fits claim

/-- Actual successful dimensions provide the node check for every matched
message; no alternative public parameter or polynomial is assumed. -/
theorem message_value (statement : Statement) (accepted : dimensions statement = true)
    (info : Info) (member : info ∈ statement.infos.val) (message : Message)
    (width : message.evaluations.val.length = info.maxMultiplicands.val + 1) (point : Word) :
    (polynomial info.maxMultiplicands.val message.evaluations.val width).natDegree ≤ info.maxMultiplicands.val ∧
      (NativeGoldInterpolation.interpolate message.evaluations.val point).map goldExtensionValue =
        some ((polynomial info.maxMultiplicands.val message.evaluations.val width).eval (goldExtensionValue point)) := by
  have nodeChecks : interpolationNodes statement = true := by
    rw [dimensions, Bool.and_eq_true] at accepted
    exact accepted.2
  change statement.infos.val.all (fun info => nodesFrom info.maxMultiplicands.val NativeGoldLookup.zero) = true at nodeChecks
  have nodes := (List.all_eq_true.mp nodeChecks) info member
  exact ⟨polynomial_degree _ _ width nodes, interpolate_value _ _ width nodes point⟩

/-- Accepted actual metadata supplies positivity and the node condition for
the native check's polynomial recurrence. -/
theorem message_recurrence (statement : Statement) (accepted : dimensions statement = true)
    (info : Info) (member : info ∈ statement.infos.val) (message : Message)
    (width : message.evaluations.val.length = info.maxMultiplicands.val + 1) (claim : Word) :
    recurrence message claim = true ↔
      (polynomial info.maxMultiplicands.val message.evaluations.val width).eval 0 +
        (polynomial info.maxMultiplicands.val message.evaluations.val width).eval 1 = goldExtensionValue claim := by
  obtain ⟨_, _, _, _, metadata⟩ := dimensions_success statement accepted
  have positive : 0 < info.maxMultiplicands.val := by have nonzero := (metadata info member).2.1; omega
  have nodeChecks : interpolationNodes statement = true := by
    rw [dimensions, Bool.and_eq_true] at accepted
    exact accepted.2
  change statement.infos.val.all (fun info => nodesFrom info.maxMultiplicands.val NativeGoldLookup.zero) = true at nodeChecks
  exact recurrence_polynomial _ message width positive ((List.all_eq_true.mp nodeChecks) info member) claim

end

end FormalProof4FHE.HasteBoots.NativeGoldInterpolationPolynomial
