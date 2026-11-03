module

public import FormalProof4FHE.HasteBoots.PackedSumcheckExecution

@[expose] public section

/-!
# Packed ZeroCheck's special first-round algebra

Each equality point has its own weighted scalar polynomial. The first message
must vanish at all 2*k Boolean/lane nodes. A fresh mixing matrix and one fresh
challenge per output lane reduce those polynomials to the next claim. The
truthful reduction equals the sum of the folded original expression times the
mixed public equality table. This is the native special round, rather than k
independent executions of scalar ZeroCheck.

Equality-table sampling, probability, terminal authentication and transcript
compilation are separate adapters.
-/

open scoped BigOperators
open Polynomial Matrix

namespace FormalProof4FHE.HasteBoots.PackedZeroFirst

noncomputable section

variable {F Factor Suffix Term : Type} [Field F] [Fintype Suffix] [Fintype Term] {k : ℕ}

def cellPolynomial (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (suffix : Suffix) : F[X] :=
  PackedSumcheckRound.expression arity (fun term => C (coefficient term)) indices
    (fun factor => PackedSumcheckRound.factorPolynomial nodes (fun bit lane => tables factor bit suffix lane))

/-- One honest polynomial for each independently sampled equality point. -/
def polynomial (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (equality : Fin k → Suffix → F) (point : Fin k) : F[X] :=
  ∑ suffix, C (equality point suffix) * cellPolynomial nodes arity coefficient indices tables suffix

def Boundary (nodes : PackedSumcheckRound.Node k ↪ F) (message : Fin k → F[X]) : Prop :=
  ∀ point bit lane, (message point).eval (nodes (bit, lane)) = 0

def Vanishes (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) : Prop :=
  ∀ bit suffix lane, PackedSumcheckRound.expression arity coefficient indices
    (fun factor => tables factor bit suffix lane) = 0

/-- Honest first-message boundary entries are equality-weighted original
constraint values, at exactly the interleaved Boolean/lane nodes. -/
theorem polynomial_node (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (equality : Fin k → Suffix → F)
    (point : Fin k) (bit : Bool) (lane : Fin k) :
    (polynomial nodes arity coefficient indices tables equality point).eval (nodes (bit, lane)) =
      ∑ suffix, equality point suffix * PackedSumcheckRound.expression arity coefficient indices
        (fun factor => tables factor bit suffix lane) := by
  simp only [polynomial, cellPolynomial, PackedSumcheckRound.expression, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, PackedSumcheckRound.factorPolynomial_node]

/-- A valid zero relation always satisfies the special first-round boundary. -/
theorem boundary_of_vanishes (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (equality : Fin k → Suffix → F)
    (zero : Vanishes arity coefficient indices tables) :
    Boundary nodes (polynomial nodes arity coefficient indices tables equality) := by
  intro point bit lane
  rw [polynomial_node]
  apply Finset.sum_eq_zero
  intro suffix _
  rw [zero bit suffix lane, mul_zero]

/-- The first-round degree does not yet include the extra public EQ factor. -/
theorem polynomial_degree (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (equality : Fin k → Suffix → F)
    (productDegree : ℕ) (bounded : ∀ term, arity term ≤ productDegree) (point : Fin k) :
    (polynomial nodes arity coefficient indices tables equality point).natDegree ≤ (2 * k - 1) * productDegree := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro suffix _
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  have cellDegree := PackedSumcheckRound.polynomial_degree nodes arity coefficient indices
    (Suffix := Unit) (fun factor bit _ lane => tables factor bit suffix lane) productDegree bounded
  simpa only [PackedSumcheckRound.polynomial, Finset.univ_unique, Finset.sum_singleton, cellPolynomial] using cellDegree

/-- Native row-major mixing, with column c multiplying equality table c. -/
def mixedEquality (mixing : Fin k → Fin k → F) (equality : Fin k → Suffix → F) : Suffix → Fin k → F :=
  fun suffix lane => ∑ point, mixing lane point * equality point suffix

/-- The first-row claims evaluate all first polynomials at that row's single
challenge, then take its independently mixed linear combination. -/
def reduce (message : Fin k → F[X]) (mixing : Fin k → Fin k → F) (challenge : Fin k → F) : Fin k → F :=
  fun lane => ∑ point, mixing lane point * (message point).eval (challenge lane)

/-- `reduced_shape` appends the new public equality factor to each product. -/
def reducedIndices (arity : Term → ℕ) (indices : (term : Term) → Fin (arity term) → Factor)
    (term : Term) : Fin (arity term + 1) → Factor ⊕ Unit :=
  Fin.lastCases (.inr ()) (fun index => .inl (indices term index))

/-- Appending the equality factor multiplies the original expression by its
public value, including repeated original factors and arbitrary coefficients. -/
theorem reduced_expression (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor) (values : Factor → F) (equality : F) :
    PackedSumcheckRound.expression (fun term => arity term + 1) coefficient (reducedIndices arity indices)
      (Sum.elim values (fun _ => equality)) =
        equality * PackedSumcheckRound.expression arity coefficient indices values := by
  simp only [PackedSumcheckRound.expression, reducedIndices, Fin.prod_univ_castSucc,
    Fin.lastCases_last, Fin.lastCases_castSucc, Sum.elim_inl, Sum.elim_inr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term _
  ring

/-- The truthful reduced claim is the reduced relation, with the EQ factor
mixed across points but the original factors folded by the native matrix pair. -/
theorem reduce_honest (nodes : PackedSumcheckRound.Node k ↪ F) (arity : Term → ℕ)
    (coefficient : Term → F) (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F) (equality : Fin k → Suffix → F)
    (mixing : Fin k → Fin k → F) (challenge : Fin k → F) (lane : Fin k) :
    reduce (polynomial nodes arity coefficient indices tables equality) mixing challenge lane =
      ∑ suffix, mixedEquality mixing equality suffix lane *
        PackedSumcheckRound.expression arity coefficient indices
          (fun factor => (∑ bit : Bool, PackedSumcheckRound.challengePair nodes challenge bit *ᵥ
            (fun inLane => tables factor bit suffix inLane)) lane) := by
  simp only [reduce, polynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Finset.mul_sum, mixedEquality, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro suffix _
  apply Finset.sum_congr rfl
  intro point _
  rw [mul_assoc]
  congr 2
  simp only [cellPolynomial, PackedSumcheckRound.expression, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, PackedSumcheckRound.challengePair_fold]

/-- A boundary-valid message differs from the honest family whenever an
honest boundary entry detects a nonzero relation. -/
theorem boundary_distinct (nodes : PackedSumcheckRound.Node k ↪ F)
    (message honest : Fin k → F[X]) (checked : Boundary nodes message)
    (detected : ¬Boundary nodes honest) : message ≠ honest := by
  intro equal
  exact detected (equal ▸ checked)

end

end FormalProof4FHE.HasteBoots.PackedZeroFirst
