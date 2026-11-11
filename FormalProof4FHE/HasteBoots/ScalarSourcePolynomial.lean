module
public import FormalProof4FHE.HasteBoots.PackedSumcheckRound
public import FormalProof4FHE.HasteBoots.LookupSourceFlattening
@[expose] public section

/-! Honest scalar polynomials from original factor tables and their native
low-bit-first common point prefix. No independently supplied honest polynomial
or node/evaluation certificate is part of this construction. -/
namespace FormalProof4FHE.HasteBoots.ScalarSourcePolynomial
open scoped BigOperators
open MatrixFold (Cube)
open PackedSumcheckRound (expression)
noncomputable section
variable {K Factor Term : Type} [Field K] [Fintype Term]

def fold {n : ℕ} (x : K) (tables : Factor → Cube (n+1) → K) : Factor → Cube n → K :=
  fun factor suffix => (1-x)*tables factor (false,suffix) + x*tables factor (true,suffix)

def truth (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor) :
    (n : ℕ) → List K → (Factor → Cube n → K) → K
  | _n,[],tables => ∑ cell, expression arity coefficient indices (fun factor => tables factor cell)
  | 0,_::_,tables => ∑ cell, expression arity coefficient indices (fun factor => tables factor cell)
  | n+1,x::point,tables => truth arity coefficient indices n point (fold x tables)

def linear (low high : K) : Polynomial K := (1-Polynomial.X)*Polynomial.C low + Polynomial.X*Polynomial.C high

def honest (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor) :
    (n : ℕ) → List K → (Factor → Cube n → K) → Polynomial K
  | 0,_,tables => Polynomial.C (∑ cell, expression arity coefficient indices (fun factor => tables factor cell))
  | n+1,[],tables => ∑ suffix : Cube n,
      expression arity (fun term => Polynomial.C (coefficient term)) indices
        (fun factor => linear (tables factor (false,suffix)) (tables factor (true,suffix)))
  | n+1,x::point,tables => honest arity coefficient indices n point (fold x tables)

theorem linear_eval (low high x : K) : (linear low high).eval x = (1-x)*low+x*high := by
  simp only [linear,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C]

theorem linear_degree (low high : K) : (linear low high).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_mul_le).trans
    simpa using (Polynomial.natDegree_sub_le (1 : Polynomial K) Polynomial.X)
  · simpa using (Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Polynomial.C high))

/-- Every honest round uses the same degree bound as its largest product.
Repeated factor indices and nonzero unused source lanes are allowed. -/
theorem degree (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (degree : ℕ) (bounded : ∀ term, arity term ≤ degree) (n : ℕ) (point : List K) (tables : Factor → Cube n → K) :
    (honest arity coefficient indices n point tables).natDegree ≤ degree := by
  induction n generalizing point with
  | zero => simp only [honest,Polynomial.natDegree_C]; exact Nat.zero_le _
  | succ n ih =>
    cases point with
    | cons x point => exact ih point (fold x tables)
    | nil =>
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro suffix _
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro term _
      apply (Polynomial.natDegree_mul_le).trans
      simp only [Polynomial.natDegree_C,zero_add]
      apply (Polynomial.natDegree_prod_le _ _).trans
      exact (Finset.sum_le_sum (fun j _ => linear_degree _ _)).trans (by simpa using bounded term)

/-- The actual zero/one consistency sum is the remaining source-table sum. -/
theorem check (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (n : ℕ) (point : List K) (tables : Factor → Cube n → K) (pending : point.length < n) :
    (honest arity coefficient indices n point tables).eval 0 +
      (honest arity coefficient indices n point tables).eval 1 = truth arity coefficient indices n point tables := by
  induction n generalizing point with
  | zero => omega
  | succ n ih =>
    cases point with
    | cons x point => exact ih point (fold x tables) (by simpa using pending)
    | nil =>
      change _ + _ = ∑ cell : Bool × Cube n, expression arity coefficient indices (fun factor => tables factor cell)
      simp only [honest,expression,Polynomial.eval_finsetSum,Polynomial.eval_mul,
        Polynomial.eval_C,Polynomial.eval_prod,linear_eval,sub_zero,one_mul,zero_mul,add_zero,
        sub_self,zero_add,Fintype.sum_prod_type,Fintype.sum_bool]
      exact add_comm _ _

/-- Evaluating the honest round at the retained challenge extends the same
low-bit-first source prefix by exactly that coordinate. -/
theorem challenge (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (n : ℕ) (point : List K) (tables : Factor → Cube n → K) (pending : point.length < n) (x : K) :
    (honest arity coefficient indices n point tables).eval x = truth arity coefficient indices n (point ++ [x]) tables := by
  induction n generalizing point with
  | zero => omega
  | succ n ih =>
    cases point with
    | cons first point => exact ih point (fold first tables) (by simpa using pending)
    | nil =>
      simp only [honest,truth,List.nil_append,expression,Polynomial.eval_finsetSum,Polynomial.eval_mul,
        Polynomial.eval_C,Polynomial.eval_prod,linear_eval,fold]

/-- At the full point, the remaining truthful sum is the original expression
of factor MLEs; no new tables are committed by scalar interpolation. -/
theorem terminal (arity : Term → ℕ) (coefficient : Term → K) (indices : (term : Term) → Fin (arity term) → Factor)
    (n : ℕ) (point : Fin n → K) (tables : Factor → Cube n → K) :
    truth arity coefficient indices n (List.ofFn point) tables =
      expression arity coefficient indices (fun factor => ExtensionQuery.evaluate n point (tables factor)) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero,truth,ExtensionQuery.evaluate]
    exact Fintype.sum_subsingleton _ ()
  | succ n ih =>
    rw [List.ofFn_succ]
    change truth arity coefficient indices n (List.ofFn (fun i => point i.succ)) (fold (point 0) tables) =
      expression arity coefficient indices (fun factor => ExtensionQuery.evaluate n (fun i => point i.succ) (fold (point 0) tables factor))
    exact ih (fun i => point i.succ) (fold (point 0) tables)

end
end FormalProof4FHE.HasteBoots.ScalarSourcePolynomial
