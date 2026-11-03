module

public import FormalProof4FHE.HasteBoots.MatrixFold
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

/-!
# Semantic packed-sumcheck round and its native matrix challenge

Each factor interpolates the 2*k Boolean/lane values. A single sum-of-products
polynomial is sent in a round, checked at adjacent lane nodes, and evaluated at
k independent challenges. The induced matrix pair folds each factor to exactly
those evaluations. Product indices need not be distinct.

This models `sumcheck/src/packed.rs`. Nodes are explicit and injective; the
consecutive-node and native interpolation algorithms are separate adapters.
No production transcript law or commitment authentication is assumed here.
-/

open scoped BigOperators
open Polynomial Matrix

namespace FormalProof4FHE.HasteBoots.PackedSumcheckRound

noncomputable section

variable {F Factor Suffix Term : Type} [Field F] [Fintype Suffix] [Fintype Term]
  {k : ℕ}

/-- The two adjacent interpolation nodes belonging to each original lane. -/
abbrev Node (k : ℕ) := Bool × Fin k

/-- A factor interpolates the Boolean value first and its original lane second. -/
def factorPolynomial (nodes : Node k ↪ F) (values : Bool → Fin k → F) : F[X] :=
  Lagrange.interpolate Finset.univ nodes (fun node => values node.1 node.2)

theorem factorPolynomial_node (nodes : Node k ↪ F) (values : Bool → Fin k → F)
    (bit : Bool) (lane : Fin k) :
    (factorPolynomial nodes values).eval (nodes (bit, lane)) = values bit lane :=
  Lagrange.eval_interpolate_at_node (fun node => values node.1 node.2)
    nodes.injective.injOn (Finset.mem_univ _)

theorem factorPolynomial_degree (nodes : Node k ↪ F) (values : Bool → Fin k → F) :
    (factorPolynomial nodes values).natDegree ≤ 2 * k - 1 := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [factorPolynomial, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using
    (Lagrange.degree_interpolate_le (s := Finset.univ) (fun node => values node.1 node.2) nodes.injective.injOn)

/-- The native challenge matrices have one row per independently sampled lane. -/
def challengePair (nodes : Node k ↪ F) (challenge : Fin k → F) :
    MatrixFold.Pair (F := F) (Lane := Fin k) :=
  fun bit outLane inLane => (Lagrange.basis Finset.univ nodes (bit, inLane)).eval (challenge outLane)

/-- Matrix folding uses precisely the Lagrange-interpolated factor evaluation. -/
theorem challengePair_fold (nodes : Node k ↪ F) (challenge : Fin k → F)
    (values : Bool → Fin k → F) (lane : Fin k) :
    (∑ bit : Bool, challengePair nodes challenge bit *ᵥ values bit) lane =
      (factorPolynomial nodes values).eval (challenge lane) := by
  simp only [factorPolynomial, Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Fintype.sum_prod_type, challengePair,
    Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- Sum of coefficient-weighted products. Repeated factor indices are allowed. -/
def expression {R : Type} [CommSemiring R] (arity : Term → ℕ)
    (coefficient : Term → R) (indices : (term : Term) → Fin (arity term) → Factor)
    (values : Factor → R) : R :=
  ∑ term, coefficient term * ∏ j, values (indices term j)

/-- Honest scalar round polynomial, summed over all remaining Boolean cells. -/
def polynomial (nodes : Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) : F[X] :=
  ∑ suffix, expression arity (fun term => C (coefficient term)) indices
    (fun factor => factorPolynomial nodes (fun bit lane => tables factor bit suffix lane))

/-- Actual hypercube sum at the beginning of a round, one value per lane. -/
def claim (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (lane : Fin k) : F :=
  ∑ suffix, (expression arity coefficient indices (fun factor => tables factor false suffix lane) +
    expression arity coefficient indices (fun factor => tables factor true suffix lane))

/-- The honest round satisfies the native adjacent-node consistency check. -/
theorem polynomial_check (nodes : Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (lane : Fin k) :
    (polynomial nodes arity coefficient indices tables).eval (nodes (false, lane)) +
      (polynomial nodes arity coefficient indices tables).eval (nodes (true, lane)) =
        claim arity coefficient indices tables lane := by
  simp only [polynomial, expression, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod, factorPolynomial_node, claim, Finset.sum_add_distrib]

/-- The next truthful claim is the same round polynomial at each challenge. -/
theorem polynomial_fold (nodes : Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (challenge : Fin k → F) (lane : Fin k) :
    (polynomial nodes arity coefficient indices tables).eval (challenge lane) =
      ∑ suffix, expression arity coefficient indices
        (fun factor => (∑ bit : Bool, challengePair nodes challenge bit *ᵥ
          (fun inLane => tables factor bit suffix inLane)) lane) := by
  simp only [challengePair_fold, polynomial, expression, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]

/-- The validated native round degree is (2*k-1) times the largest arity. -/
theorem polynomial_degree (nodes : Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (degree : ℕ)
    (bounded : ∀ term, arity term ≤ degree) :
    (polynomial nodes arity coefficient indices tables).natDegree ≤ (2 * k - 1) * degree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro suffix _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro term _
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ j : Fin (arity term),
        (factorPolynomial nodes (fun bit lane => tables (indices term j) bit suffix lane)).natDegree ≤
        ∑ _j : Fin (arity term), (2 * k - 1) :=
      Finset.sum_le_sum (fun _ _ => factorPolynomial_degree nodes _)
    _ = (2 * k - 1) * arity term := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (bounded term)

end

end FormalProof4FHE.HasteBoots.PackedSumcheckRound
