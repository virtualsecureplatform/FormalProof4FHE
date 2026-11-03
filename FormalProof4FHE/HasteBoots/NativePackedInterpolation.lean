module

public import FormalProof4FHE.HasteBoots.PackedSumcheckProbability
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Consecutive nodes, Lagrange weights and native packed messages

The Boolean/lane interpolation address is 2*lane+bit. Consecutive field nodes
are injective below the characteristic. A received vector of D+1 evaluations
therefore denotes a polynomial of degree at most D, automatically; its native
adjacent-entry check is exactly the semantic polynomial check. The challenge
pair's entries equal the literal product/quotient Lagrange weights.

These are typed field/array semantics. Native finite-field representations,
optimized interpolation and forward-difference loop refinement remain open.
-/

open scoped BigOperators
open Polynomial

namespace FormalProof4FHE.HasteBoots.NativePackedInterpolation

noncomputable section

variable {F : Type} [Field F] {k count degree : ℕ}

/-- Positive native width and nonempty products leave enough round entries
for all adjacent lane checks, exactly as the shape validator requires. -/
theorem interpolation_capacity (widthPositive : 0 < k) (degreePositive : 0 < degree) :
    2 * k ≤ (2 * k - 1) * degree + 1 := by
  have monotone := Nat.mul_le_mul_left (2 * k - 1) degreePositive
  omega

/-- Native interleaving: even node for bit zero, odd node for bit one. -/
def nodeIndex (node : PackedSumcheckRound.Node k) : Fin (2 * k) :=
  ⟨2 * node.2.val + if node.1 then 1 else 0, by
    have bound := node.2.isLt
    split <;> omega⟩

theorem nodeIndex_val (bit : Bool) (lane : Fin k) :
    (nodeIndex (bit, lane)).val = 2 * lane.val + if bit then 1 else 0 := rfl

theorem nodeIndex_injective : Function.Injective (nodeIndex (k := k)) := by
  rintro ⟨firstBit, firstLane⟩ ⟨secondBit, secondLane⟩ equal
  have values := congrArg Fin.val equal
  simp only [nodeIndex] at values
  cases firstBit <;> cases secondBit <;> simp only [Bool.false_eq_true, reduceIte] at values
  all_goals first | exact False.elim (by omega) | congr 1; exact Fin.ext (by omega)

/-- The field characteristic validates the consecutive-node interpolation. -/
def consecutive (p : ℕ) [CharP F p] (small : count ≤ p) : Fin count ↪ F where
  toFun node := (node.val : F)
  inj' := by
    intro first second equal
    apply Fin.ext
    have mods := (CharP.cast_eq_iff_mod_eq F p).mp equal
    simpa only [Nat.mod_eq_of_lt (first.isLt.trans_le small),
      Nat.mod_eq_of_lt (second.isLt.trans_le small)] using mods

/-- Native Boolean/lane nodes interpreted inside the base field. -/
def nodes (p : ℕ) [CharP F p] (small : 2 * k ≤ p) : PackedSumcheckRound.Node k ↪ F :=
  ⟨fun node => consecutive p small (nodeIndex node),
    (consecutive p small).injective.comp nodeIndex_injective⟩

/-- Each Lagrange basis evaluates to the same product quotient as the native
`lagrange_weights` loop. The identity also holds at interpolation nodes. -/
theorem basis_eval {Index : Type} [Fintype Index] [DecidableEq Index]
    (points : Index ↪ F) (point : F) (index : Index) :
    (Lagrange.basis Finset.univ points index).eval point =
      (∏ other ∈ Finset.univ.erase index, (point - points other)) /
        (∏ other ∈ Finset.univ.erase index, (points index - points other)) := by
  simp only [Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  simp only [mul_comm, ← div_eq_mul_inv, Finset.prod_div_distrib]

/-- Received D+1 evaluations have their own degree bound by construction. -/
def messagePolynomial (points : Fin (degree + 1) ↪ F) (message : Fin (degree + 1) → F) : F[X] :=
  Lagrange.interpolate Finset.univ points message

theorem messagePolynomial_degree (points : Fin (degree + 1) ↪ F) (message : Fin (degree + 1) → F) :
    (messagePolynomial points message).natDegree ≤ degree := by
  apply Polynomial.natDegree_le_of_degree_le
  simpa only [messagePolynomial, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] using
    Lagrange.degree_interpolate_le (s := Finset.univ) message points.injective.injOn

theorem messagePolynomial_node (points : Fin (degree + 1) ↪ F) (message : Fin (degree + 1) → F)
    (index : Fin (degree + 1)) :
    (messagePolynomial points message).eval (points index) = message index :=
  Lagrange.eval_interpolate_at_node message points.injective.injOn (Finset.mem_univ _)

/-- The native round checker reads exactly the first 2*k interleaved entries. -/
def Checks (enough : 2 * k ≤ degree + 1) (claimed : Fin k → F) (message : Fin (degree + 1) → F) : Prop :=
  ∀ lane, message (Fin.castLE enough (nodeIndex (false, lane))) +
    message (Fin.castLE enough (nodeIndex (true, lane))) = claimed lane

/-- Consecutive interpolation identifies the literal native array check with
the semantic polynomial check. No independent degree premise is required. -/
theorem checks_iff (p : ℕ) [CharP F p] (small : degree + 1 ≤ p) (enough : 2 * k ≤ degree + 1)
    (claimed : Fin k → F) (message : Fin (degree + 1) → F) :
    Checks enough claimed message ↔ PackedSumcheckProbability.Checks (nodes p (enough.trans small)) claimed
      (messagePolynomial (consecutive p small) message) := by
  have evalAt (node : PackedSumcheckRound.Node k) :
      (messagePolynomial (consecutive p small) message).eval (nodes p (enough.trans small) node) =
        message (Fin.castLE enough (nodeIndex node)) :=
    messagePolynomial_node (consecutive p small) message (Fin.castLE enough (nodeIndex node))
  simp only [Checks, PackedSumcheckProbability.Checks, evalAt]

/-- Native evaluation-vector messages supply their degree bound automatically.
Only the interactive fresh independent challenge law is used. -/
theorem round_healing_bound [Fintype F] [DecidableEq F]
    {Factor Suffix Term : Type} [Fintype Suffix] [Fintype Term]
    (p : ℕ) [CharP F p] (productDegree : ℕ)
    (small : (2 * k - 1) * productDegree + 1 ≤ p)
    (enough : 2 * k ≤ (2 * k - 1) * productDegree + 1)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : Factor → Bool → Suffix → Fin k → F)
    (bounded : ∀ term, arity term ≤ productDegree) (claimed : Fin k → F)
    (message : Fin ((2 * k - 1) * productDegree + 1) → F)
    [SampleableType (Fin k → F)]
    (falseClaim : claimed ≠ PackedSumcheckRound.claim arity coefficient indices tables) :
    Pr{let challenge ← $ᵗ (Fin k → F)}[
      Checks enough claimed message ∧ ∀ lane,
        (messagePolynomial (consecutive p small) message).eval (challenge lane) =
          (PackedSumcheckRound.polynomial (nodes p (enough.trans small)) arity coefficient indices tables).eval
            (challenge lane)] ≤
      ((((2 * k - 1) * productDegree : ℕ) : ENNReal) / Fintype.card F) ^ k := by
  simpa only [← checks_iff p small enough claimed message] using
    PackedSumcheckProbability.round_healing_bound (nodes p (enough.trans small)) arity coefficient indices tables
      productDegree bounded claimed (messagePolynomial (consecutive p small) message) falseClaim
      (messagePolynomial_degree _ _)

end

end FormalProof4FHE.HasteBoots.NativePackedInterpolation
