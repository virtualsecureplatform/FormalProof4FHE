module
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def points (i : Fin 5) : ZMod 7 := i.val
private def corrupted (i : Fin 5) : ZMod 7 := if i = 2 then 0 else 2 + 3 * points i

-- Recover 2 + 3X with one corrupt evaluation, using executable elimination and division.
/-- info: true -/
#guard_msgs in
#eval match ExecutableBerlekampWelch.decoder 1 2 points corrupted with
  | some polynomial => decide (polynomial.coeff 0 = 2 ∧ polynomial.coeff 1 = 3 ∧ polynomial.natDegree = 1)
  | none => false

/-- info: true -/
#guard_msgs in
#eval (ExecutableBerlekampWelch.decoder 1 0 points corrupted).isNone

-- The zero message is accepted even with one nonzero error.
/-- info: true -/
#guard_msgs in
#eval match ExecutableBerlekampWelch.decoder 1 2 points (fun i => if i = 3 then 4 else 0) with
  | some polynomial => decide (polynomial.support = ∅)
  | none => false

-- A quadratic is too far from any affine polynomial for this radius.
/-- info: true -/
#guard_msgs in
#eval (ExecutableBerlekampWelch.decoder 1 2 points (fun i => points i ^ 2)).isNone

private def numerator : Polynomial (ZMod 7) := ExecutablePolynomial.ofCoefficients 3 (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
private def divisor : Polynomial (ZMod 7) := ExecutablePolynomial.ofCoefficients 2 (fun i => if i = 0 then 2 else 2)

-- Nonmonic division: (X²+1)/(2X+2) = 4X+3, remainder 2 over F7.
/-- info: true -/
#guard_msgs in
#eval let q := ExecutablePolynomialDivision.divide numerator divisor
      let r := ExecutablePolynomialDivision.remainder numerator divisor
      decide (q.coeff 0 = 3 ∧ q.coeff 1 = 4 ∧ r.coeff 0 = 2 ∧ r.natDegree = 0)

/-- info: true -/
#guard_msgs in
#eval let z : Polynomial (ZMod 7) := ExecutablePolynomial.zero
      let q := ExecutablePolynomialDivision.divide numerator z
      let r := ExecutablePolynomialDivision.remainder numerator z
      decide (q.support = ∅ ∧ r.coeff 0 = 1 ∧ r.coeff 2 = 1)
