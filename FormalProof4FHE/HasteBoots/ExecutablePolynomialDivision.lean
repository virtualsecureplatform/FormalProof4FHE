module
public import FormalProof4FHE.HasteBoots.ExecutablePolynomialDivisionAux
public import FormalProof4FHE.HasteBoots.DensePolynomialDivision
@[expose] public section
namespace FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
open Polynomial
open ExecutablePolynomial
variable {F : Type} [Field F] [DecidableEq F]

def coefficientVector (p : F[X]) (length : ℕ) : Vector F length :=
  Vector.ofFn (fun i : Fin length => p.coeff i.val)

theorem coefficientVector_polynomial (p : F[X]) (length : ℕ) (bound : p.natDegree < length) :
    PolynomialShapeCost.polynomial (coefficientVector p length) = p := by
  ext i
  by_cases inside : i < length
  · rw [DensePolynomialStepCost.polynomial_coeff_fin _ ⟨i,inside⟩]
    simp only [coefficientVector,FiniteLinearSolver.get_ofFn]
  · rw [DensePolynomialStepCost.polynomial_coeff_above _ i (by omega),coeff_eq_zero_of_natDegree_lt (by omega)]

def inputWidth (p q : F[X]) : ℕ := max p.natDegree q.natDegree+1

/-- Charge for the dense division core after input vectors have been prepared.
Degree discovery, coefficient materialization and output polynomial conversion
are separate costs. -/
def divModWithCost (p q : F[X]) :
    SolverOperationCost.Run (Vector F (inputWidth p q) × Vector F (inputWidth p q)) :=
  DensePolynomialDivision.divMod (coefficientVector p (inputWidth p q)) (coefficientVector q (inputWidth p q))

/-- One measured dense division supplies both reconstructed polynomials. -/
def divMod (p q : F[X]) : F[X] × F[X] :=
  let result := divModWithCost p q
  (PolynomialShapeCost.polynomial result.value.1,PolynomialShapeCost.polynomial result.value.2)

theorem divMod_fst_eq (p q : F[X]) : (divMod p q).1 = p / q := by
  simp only [divMod,divModWithCost,DensePolynomialDivision.divMod_fst_eq]
  rw [coefficientVector_polynomial p _ (by unfold inputWidth; omega),
    coefficientVector_polynomial q _ (by unfold inputWidth; omega)]

theorem divMod_snd_eq (p q : F[X]) : (divMod p q).2 = p % q := by
  simp only [divMod,divModWithCost,DensePolynomialDivision.divMod_snd_eq]
  rw [coefficientVector_polynomial p _ (by unfold inputWidth; omega),
    coefficientVector_polynomial q _ (by unfold inputWidth; omega)]

theorem divModWithCost_cost (p q : F[X]) :
    (divModWithCost p q).cost ≤ 50*(inputWidth p q+1)^2+14*inputWidth p q+19 :=
  DensePolynomialDivision.divMod_cost _ _

theorem divMod_eq (p q : F[X]) : divMod p q = (p / q,p % q) := by
  exact Prod.ext (divMod_fst_eq p q) (divMod_snd_eq p q)

theorem divMod_reconstruct (p q : F[X]) : q * (divMod p q).1 + (divMod p q).2 = p := by
  rw [divMod_fst_eq,divMod_snd_eq]
  exact EuclideanDomain.div_add_mod p q

theorem divMod_remainder_degree (p q : F[X]) (nonzero : q ≠ 0) :
    (divMod p q).2.degree < q.degree := by
  rw [divMod_snd_eq]
  exact Polynomial.degree_mod_lt p nonzero

def divide (p q : F[X]) : F[X] := (divMod p q).1

def remainder (p q : F[X]) : F[X] := (divMod p q).2

theorem divide_eq (p q : F[X]) : divide p q = p / q := divMod_fst_eq p q

theorem remainder_eq (p q : F[X]) : remainder p q = p % q := divMod_snd_eq p q
end FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
