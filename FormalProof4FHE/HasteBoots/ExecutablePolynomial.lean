module
public import Mathlib.Algebra.Polynomial.FieldDivision
public import FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
public import Mathlib.Tactic
@[expose] public section

/-! Explicit polynomial operations with executable coefficient storage.
Mathlib's polynomial ring operations are noncomputable. These definitions
construct finite supports directly and are proved equal to the ring operations.
They are intended as a reference implementation for extraction, not as a
refinement of the native NTT or a claim about physical running time. -/
namespace FormalProof4FHE.HasteBoots.ExecutablePolynomial
open Polynomial
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem vector_get_ofFn {length : ℕ} (values : Fin length → F) (i : Fin length) :
    (Vector.ofFn values).get i = values i := by
  simp [Vector.get]
  congr 1

def ofCoefficients (length : ℕ) (values : ℕ → F) : F[X] :=
  let coefficients := Vector.ofFn (fun i : Fin length => values i.val)
  ⟨(Finset.range length).filter (fun i => values i ≠ 0),
   fun i => if h : i < length then coefficients.get ⟨i,h⟩ else 0,
   by intro i; simp only [coefficients,vector_get_ofFn,Finset.mem_filter,Finset.mem_range]; split_ifs <;> simp_all⟩

@[simp] theorem coeff_ofCoefficients (length : ℕ) (values : ℕ → F) (i : ℕ) :
    (ofCoefficients length values).coeff i = if i < length then values i else 0 := by
  simp only [ofCoefficients,Polynomial.coeff,vector_get_ofFn]
  rfl

def zero : F[X] := ofCoefficients 0 (fun _ => 0)
def constant (value : F) : F[X] := ofCoefficients 1 (fun _ => value)
def add (left right : F[X]) : F[X] :=
  ofCoefficients (max left.natDegree right.natDegree + 1) (fun i => left.coeff i + right.coeff i)
def sub (left right : F[X]) : F[X] :=
  ofCoefficients (max left.natDegree right.natDegree + 1) (fun i => left.coeff i - right.coeff i)
def mul (left right : F[X]) : F[X] :=
  ofCoefficients (left.natDegree + right.natDegree + 1)
    (fun i => ∑ pair ∈ Finset.antidiagonal i, left.coeff pair.1 * right.coeff pair.2)
def term (value : F) (exponent : ℕ) : F[X] :=
  ofCoefficients (exponent+1) (fun i => if i = exponent then value else 0)
/-- Evaluation charge starts from prepared coefficients. Discovering the degree
and materializing the polynomial's coefficient function are separate costs. -/
def evaluateWithCost (p : F[X]) (point : F) : SolverOperationCost.Run F :=
  PolynomialEvaluationCost.evaluate (Vector.ofFn (fun i : Fin (p.natDegree+1) => p.coeff i.val)) point

def evaluate (p : F[X]) (point : F) : F := (evaluateWithCost p point).value

omit [DecidableEq F] in
theorem evaluateWithCost_cost (p : F[X]) (point : F) :
    (evaluateWithCost p point).cost = 7*(p.natDegree+1)+3 :=
  PolynomialEvaluationCost.evaluate_cost _ _

theorem zero_eq : (zero : F[X]) = 0 := by ext i; simp [zero]
theorem constant_eq (value : F) : constant value = C value := by
  ext i
  simp only [constant,coeff_ofCoefficients,coeff_C]
  split_ifs <;> simp_all

theorem add_eq (left right : F[X]) : add left right = left + right := by
  ext i
  simp only [add,coeff_ofCoefficients,coeff_add]
  split_ifs with bound
  · rfl
  · have hl : left.natDegree < i := by omega
    have hr : right.natDegree < i := by omega
    simp [coeff_eq_zero_of_natDegree_lt hl,coeff_eq_zero_of_natDegree_lt hr]

theorem sub_eq (left right : F[X]) : sub left right = left - right := by
  ext i
  simp only [sub,coeff_ofCoefficients,coeff_sub]
  split_ifs with bound
  · rfl
  · have hl : left.natDegree < i := by omega
    have hr : right.natDegree < i := by omega
    simp [coeff_eq_zero_of_natDegree_lt hl,coeff_eq_zero_of_natDegree_lt hr]

theorem mul_eq (left right : F[X]) : mul left right = left * right := by
  ext i
  simp only [mul,coeff_ofCoefficients,coeff_mul]
  split_ifs with bound
  · rfl
  · symm
    apply Finset.sum_eq_zero
    intro pair present
    have sum := Finset.mem_antidiagonal.mp present
    by_cases hl : left.natDegree < pair.1
    · simp [coeff_eq_zero_of_natDegree_lt hl]
    · have hr : right.natDegree < pair.2 := by omega
      simp [coeff_eq_zero_of_natDegree_lt hr]

theorem term_eq (value : F) (exponent : ℕ) : term value exponent = C value * X ^ exponent := by
  ext i
  simp only [term,coeff_ofCoefficients,coeff_C_mul_X_pow]
  split_ifs <;> simp_all

omit [DecidableEq F] in
theorem evaluate_eq (p : F[X]) (point : F) : evaluate p point = p.eval point := by
  have expansion := congrArg (Polynomial.eval point) p.as_sum_range_C_mul_X_pow
  simp only [evaluate,evaluateWithCost,PolynomialEvaluationCost.evaluate_value,FiniteLinearSolver.get_ofFn]
  rw [Fin.sum_univ_eq_sum_range (fun i => p.coeff i * point^i)]
  simpa only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X] using expansion.symm

/-- Coefficients and point inputs are prepared once; their preparation is not
included in the charge for the materialized Horner evaluations. -/
def evaluateManyWithCost {n : ℕ} (p : F[X]) (points : Vector F n) : SolverOperationCost.Run (Vector F n) :=
  PolynomialEvaluationCost.evaluateMany (Vector.ofFn (fun i : Fin (p.natDegree+1) => p.coeff i.val)) points

def evaluateMany {n : ℕ} (p : F[X]) (points : Fin n → F) : Vector F n :=
  (evaluateManyWithCost p (Vector.ofFn points)).value

omit [DecidableEq F] in
theorem evaluateMany_get {n : ℕ} (p : F[X]) (points : Fin n → F) (i : Fin n) :
    (evaluateMany p points).get i = p.eval (points i) := by
  simp only [evaluateMany,evaluateManyWithCost,PolynomialEvaluationCost.evaluateMany_get,
    FiniteLinearSolver.get_ofFn]
  have pointValue := evaluate_eq p (points i)
  simpa only [evaluate,evaluateWithCost,PolynomialEvaluationCost.evaluate_value,
    FiniteLinearSolver.get_ofFn] using pointValue

omit [DecidableEq F] in
theorem evaluateManyWithCost_cost {n : ℕ} (p : F[X]) (points : Vector F n) :
    (evaluateManyWithCost p points).cost = n*(7*(p.natDegree+1)+5)+1 :=
  PolynomialEvaluationCost.evaluateMany_cost _ _
end FormalProof4FHE.HasteBoots.ExecutablePolynomial
