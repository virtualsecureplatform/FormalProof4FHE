/-
Adapted from Mathlib.Algebra.Polynomial.Div (Apache 2.0).
The recursion uses explicit executable coefficient operations and equality.
-/
module
public import FormalProof4FHE.HasteBoots.ExecutablePolynomial
@[expose] public section
namespace FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
open Polynomial
open ExecutablePolynomial
variable {F : Type} [Field F] [DecidableEq F]

def monicAux : (p : F[X]) → {q : F[X]} → Monic q → F[X] × F[X]
  | p,q,hq =>
    if h : degree q ≤ degree p ∧ p.support.Nonempty then
      let z := term (leadingCoeff p) (natDegree p - natDegree q)
      have _wf : (sub p (mul q z)).degree < p.degree := by
        simpa only [z,sub_eq,mul_eq,term_eq] using div_wf_lemma ⟨h.1,support_nonempty.mp h.2⟩ hq
      let dm := monicAux (sub p (mul q z)) hq
      (add z dm.1,dm.2)
    else (zero,p)
  termination_by p => p

theorem monicAux_eq (p q : F[X]) (monic : Monic q) :
    monicAux p monic = divModByMonicAux p monic := by
  induction p using WellFounded.induction Polynomial.degree_lt_wf with
  | h p ih =>
    rw [monicAux,divModByMonicAux]
    simp only [support_nonempty]
    split_ifs with h
    · simp only [sub_eq,mul_eq,term_eq,add_eq]
      rw [ih _ (div_wf_lemma h monic)]
    · simp only [zero_eq]

end FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
