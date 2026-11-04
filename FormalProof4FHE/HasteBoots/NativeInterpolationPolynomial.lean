module

public import FormalProof4FHE.HasteBoots.NativeInterpolationAccumulator

@[expose] public section

/-!
# Polynomial meaning of the literal native scalar interpolation

A received degree-plus-one vector defines its own Lagrange polynomial.
The actual scan and descending accumulator are connected to that polynomial;
no independent degree or evaluation-correctness certificate is supplied.
-/

namespace FormalProof4FHE.HasteBoots.NativeInterpolationPolynomial

open NativeInterpolationCore NativeInterpolationField NativeInterpolationSafety
open NativeInterpolationWeights NativeInterpolationAccumulator
open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type} [Field K]

def polynomial (degree : ℕ) (values : List K) (width : values.length = degree + 1) : K[X] :=
  Lagrange.interpolate Finset.univ (fun node : Fin (degree + 1) => (node.val : K))
    (fun node => values[node.val]'(by rw [width]; exact node.isLt))

theorem polynomial_degree (degree : ℕ) (values : List K) (width : values.length = degree + 1)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) :
    (polynomial degree values width).natDegree ≤ degree := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [polynomial, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] using
    Lagrange.degree_interpolate_le (s := Finset.univ)
      (fun node : Fin (degree + 1) => values[node.val]'(by rw [width]; exact node.isLt))
      (nodes_injective degree nodes).injOn

theorem polynomial_node (degree : ℕ) (values : List K) (width : values.length = degree + 1)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) (node : Fin (degree + 1)) :
    (polynomial degree values width).eval (node.val : K) =
      values[node.val]'(by rw [width]; exact node.isLt) :=
  Lagrange.eval_interpolate_at_node _ (nodes_injective degree nodes).injOn (Finset.mem_univ node)

theorem nodeProduct (point : K) (degree : ℕ) :
    (nodeState point degree).product = ∏ node : Fin (degree + 1), (point - (node.val : K)) := by
  induction degree with
  | zero => simp [nodeState]
  | succ degree ih =>
    calc
      (nodeState point (degree + 1)).product =
          (nodeState point degree).product * (point - ((degree + 1 : ℕ) : K)) := by
        rw [← extend_nodeState]
        simp only [extend, arithmetic, nodeState, Nat.cast_add, Nat.cast_one]
      _ = _ := by
        rw [ih]
        exact (Fin.prod_univ_castSucc (fun node : Fin (degree + 1 + 1) => point - (node.val : K))).symm

theorem nodeProduct_nodal (point : K) (degree : ℕ) :
    (nodeState point degree).product =
      (Lagrange.nodal Finset.univ (fun node : Fin (degree + 1) => (node.val : K))).eval point := by
  rw [Lagrange.eval_nodal]
  exact nodeProduct point degree

/-- The complete literal accumulator sum is the barycentric form of the
received vector's polynomial, at every off-node challenge. -/
theorem fullSum_polynomial (degree : ℕ) (values : List K) (width : values.length = degree + 1)
    (point : K) (offNodes : ∀ j, j ≤ degree → point ≠ (j : K)) :
    partialSum degree values point (nodeState point degree).product (degree + 1) width.ge =
      (polynomial degree values width).eval point := by
  have away : ∀ node ∈ (Finset.univ : Finset (Fin (degree + 1))), point ≠ (node.val : K) := by
    intro node _
    exact offNodes node.val (by have bound := node.isLt; omega)
  rw [polynomial, Lagrange.eval_interpolate_not_at_node _ away, ← nodeProduct_nodal]
  simp only [partialSum, Finset.mul_sum, nodalWeight_value, div_eq_mul_inv, mul_inv_rev]
  apply Finset.sum_congr rfl
  intro node _
  ring

/-- The literal scan, factorial and reverse accumulator evaluate the received
vector's polynomial at every challenge, including all early-return nodes. -/
theorem interpolate_value (degree : ℕ) (values : List K) (width : values.length = degree + 1)
    (nodes : ∀ j, 0 < j → j ≤ degree → (j : K) ≠ 0) (point : K) :
    interpolate (arithmetic K) values point = some ((polynomial degree values width).eval point) := by
  cases values with
  | nil => simp at width
  | cons first rest =>
    have degreeSize : degree = rest.length := by simp only [List.length_cons] at width; omega
    subst degree
    simp only [interpolate, List.length_cons, Nat.add_sub_cancel,
      show (arithmetic K).zero = (0 : K) from rfl, show (arithmetic K).one = (1 : K) from rfl]
    have spec := scan_nodes point rest.length 0
    rw [nodeState_zero] at spec
    cases finished : scan (arithmetic K) point rest.length 0 ⟨0, point, [point]⟩ with
    | atNode index =>
      rw [finished] at spec
      have bounds := scan_bounds (arithmetic K) point rest.length 0 ⟨0, point, [point]⟩
      rw [finished] at bounds
      have inside : index < rest.length + 1 := by omega
      have inValues : index < (first :: rest).length := by simp only [List.length_cons]; omega
      change (first :: rest)[index]? = some ((polynomial rest.length (first :: rest) width).eval point)
      rw [List.getElem?_eq_getElem inValues, spec, polynomial_node _ _ width nodes ⟨index, inside⟩]
    | offNodes scanned =>
      rw [finished] at spec
      simp only [Nat.zero_add] at spec
      obtain ⟨same, away⟩ := spec
      subst scanned
      let initial : ReverseState K :=
        ⟨0, (factorial (arithmetic K) rest.length).1, 1, (rest.length : K), 1⟩
      have ratio : initial.up = initial.down * denominator rest.length rest.length := by
        change (factorial (arithmetic K) rest.length).1 = 1 * denominator rest.length rest.length
        rw [NativeInterpolationField.factorial_value, denominator_top, one_mul]
      have execution := reverse_value rest.length (first :: rest) point (nodeState point rest.length).product
        (rest.length + 1) initial (by omega) (by simp) (by omega)
        (by simp only [initial, Nat.add_sub_cancel])
        (by simp only [initial, Nat.add_sub_cancel, Nat.sub_self, Nat.zero_add, Nat.cast_one])
        (by simpa only [Nat.add_sub_cancel] using ratio) one_ne_zero nodes
        (fun j small => away j (Nat.zero_le _) small)
      change (reverse (arithmetic K) (first :: rest) (nodeState point rest.length).differences
        (nodeState point rest.length).product (rest.length + 1) initial).map ReverseState.result = _
      rw [execution]
      simp only [initial, zero_add]
      rw [fullSum_polynomial rest.length (first :: rest) width point (fun j small => away j (Nat.zero_le _) small)]

end

end FormalProof4FHE.HasteBoots.NativeInterpolationPolynomial
