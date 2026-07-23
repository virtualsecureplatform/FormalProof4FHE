/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Basic
import LatticeCrypto.Ring.SchoolbookCert
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# Decisional Ring Learning With Errors

This module defines the finite negacyclic ring
`R_q = ZMod q[X] / (X^degree + 1)` used by power-of-two cyclotomic RLWE
instantiations and packages decisional RLWE as rank-one matrix LWE over that ring.

The executable carrier is a length-`degree` coefficient vector with negacyclic
convolution. `rqSemantics` maps it into Mathlib's polynomial quotient; for a positive degree and
nontrivial coefficient ring, the map is bijective by monic polynomial remainder.  It also
certifies that the executable ring operations agree with quotient-ring operations.

An RLWE challenge with `sampleCount` samples is represented as a one-row matrix.
Thus `problem` is definitionally the existing `LWE.batchProblem` with dimension one,
and all generic LWE game and reduction theorems apply without a new probabilistic bridge.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE

/-- The bundled executable negacyclic ring over `ZMod q`. -/
abbrev negacyclicRing (q degree : ℕ) : LatticeCrypto.NegacyclicRing (ZMod q) :=
  LatticeCrypto.vectorNegacyclicRing (ZMod q) degree

/-- The coefficient-vector carrier for `R_q = ZMod q[X] / (X^degree + 1)`.

Multiplication is negacyclic convolution, supplied by `negacyclicRing`. -/
abbrev Rq (q degree : ℕ) := (negacyclicRing q degree).Poly

instance rqDecidableEq (q degree : ℕ) : DecidableEq (Rq q degree) := by
  change DecidableEq (LatticeCrypto.Poly (ZMod q) degree)
  infer_instance

instance rqFintype (q degree : ℕ) [NeZero q] : Fintype (Rq q degree) :=
  inferInstanceAs (Fintype (Vector (ZMod q) degree))

instance rqSampleableType (q degree : ℕ) [NeZero q] :
    SampleableType (Rq q degree) :=
  inferInstanceAs (SampleableType (Vector (ZMod q) degree))

/-- The proof-facing interpretation of the executable carrier in the polynomial quotient.

Positivity is required because at degree zero the modulus is `X^0 + 1 = 2`, while the
zero-length executable carrier is the trivial ring. -/
noncomputable abbrev rqSemantics (q : ℕ) {degree : ℕ} (hdegree : 0 < degree) :
    LatticeCrypto.NegacyclicRingSemantics (negacyclicRing q degree) :=
  LatticeCrypto.vectorNegacyclicSemantics (ZMod q) hdegree

/-- Mathlib's semantic quotient corresponding to `Rq q degree`. -/
abbrev QuotientRq (q degree : ℕ) :=
  LatticeCrypto.NegacyclicQuotient (ZMod q) degree

/-- Embed an executable coefficient vector into the semantic quotient ring. -/
noncomputable abbrev quotientOf {q degree : ℕ} (hdegree : 0 < degree)
    (f : Rq q degree) : QuotientRq q degree :=
  (rqSemantics q hdegree).quotientOf f

/-- The quotient interpretation preserves all information in the coefficient vector. -/
theorem quotientOf_injective {q degree : ℕ} (hdegree : 0 < degree) :
    Function.Injective (quotientOf (q := q) hdegree) :=
  LatticeCrypto.NegacyclicQuotient.ofBackend_injective
    (LatticeCrypto.vectorBackend (ZMod q) degree)

/-- The zero executable polynomial maps to zero in the semantic quotient. -/
theorem quotientOf_zero {q degree : ℕ} (hdegree : 0 < degree) :
    quotientOf (q := q) hdegree (0 : Rq q degree) = 0 :=
  (rqSemantics q hdegree).zero_sound

/-- Executable coefficientwise addition agrees with addition in the semantic quotient. -/
theorem quotientOf_add {q degree : ℕ} (hdegree : 0 < degree)
    (left right : Rq q degree) :
    quotientOf hdegree (left + right) =
      quotientOf hdegree left + quotientOf hdegree right :=
  (rqSemantics q hdegree).add_sound left right

/-- Negacyclic multiplication on the executable carrier agrees with multiplication in
`ZMod q[X] / (X^degree + 1)`. -/
theorem quotientOf_mul {q degree : ℕ} (hdegree : 0 < degree) (f g : Rq q degree) :
    quotientOf hdegree ((negacyclicRing q degree).mul f g) =
      quotientOf hdegree f * quotientOf hdegree g :=
  (rqSemantics q hdegree).mul_sound f g

/-- The `CommRing` multiplication used by generic matrix-LWE code has the same quotient
interpretation as the explicitly bundled executable multiplication. -/
theorem quotientOf_commRing_mul {q degree : ℕ} (hdegree : 0 < degree)
    (left right : Rq q degree) :
    quotientOf hdegree
        (@Mul.mul (Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toMul left right) =
      quotientOf hdegree left * quotientOf hdegree right := by
  cases degree with
  | zero => omega
  | succ degree => exact quotientOf_mul hdegree left right

/-- Bundled ring homomorphism from the executable negacyclic coefficient representation to its
semantic polynomial quotient. -/
noncomputable def quotientRingHom {q degree : ℕ} (hdegree : 0 < degree) :
    Rq q degree →+* QuotientRq q degree where
  toFun := quotientOf hdegree
  map_one' := by
    cases degree with
    | zero => omega
    | succ degree =>
        change quotientOf hdegree
          ((negacyclicRing q (degree + 1)).one) = 1
        exact (rqSemantics q hdegree).one_sound
  map_zero' := by
    cases degree with
    | zero => omega
    | succ degree =>
        change quotientOf hdegree
          ((negacyclicRing q (degree + 1)).zero) = 0
        exact quotientOf_zero hdegree
  map_add' left right := by
    cases degree with
    | zero => omega
    | succ degree =>
        change quotientOf hdegree
            ((negacyclicRing q (degree + 1)).add left right) =
          quotientOf hdegree left + quotientOf hdegree right
        exact quotientOf_add hdegree left right
  map_mul' left right := quotientOf_commRing_mul hdegree left right

/-- The bundled executable-to-semantic ring homomorphism is injective. -/
theorem quotientRingHom_injective {q degree : ℕ} (hdegree : 0 < degree) :
    Function.Injective (quotientRingHom (q := q) hdegree) :=
  by
    change Function.Injective (quotientOf hdegree)
    exact quotientOf_injective hdegree

/-- The executable coefficient carrier covers every class of the semantic quotient when the
coefficient ring is nontrivial.  The preimage of a polynomial is its remainder modulo the monic
polynomial `X^degree + 1`, represented by its first `degree` coefficients. -/
theorem quotientOf_surjective {q degree : ℕ} [Nontrivial (ZMod q)]
    (hdegree : 0 < degree) :
    Function.Surjective (quotientOf (q := q) hdegree) := by
  intro quotient
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective quotient
  let modulus : Polynomial (ZMod q) :=
    LatticeCrypto.negacyclicModulus (ZMod q) degree
  have hmonic : modulus.Monic := by
    simpa [modulus, LatticeCrypto.negacyclicModulus] using
      (Polynomial.monic_X_pow_add_C (R := ZMod q) (a := (1 : ZMod q)) hdegree.ne')
  have hdegreeModulus : modulus.degree ≤ (degree : WithBot ℕ) := by
    rw [show modulus = Polynomial.X ^ degree + Polynomial.C (1 : ZMod q) by
      simp [modulus, LatticeCrypto.negacyclicModulus]]
    rw [Polynomial.degree_X_pow_add_C hdegree]
  let remainder : Polynomial (ZMod q) := polynomial %ₘ modulus
  let representative : Rq q degree :=
    LatticeCrypto.Poly.ofPi fun coefficient ↦ remainder.coeff coefficient
  refine ⟨representative, ?_⟩
  have hrepresentative :
      (LatticeCrypto.vectorBackend (ZMod q) degree).toPolynomial representative =
        remainder := by
    have hcoeff (coefficient : Fin degree) :
        (LatticeCrypto.vectorBackend (ZMod q) degree).coeff representative coefficient =
          remainder.coeff coefficient := by
      change LatticeCrypto.Poly.toPi representative coefficient =
        remainder.coeff coefficient
      dsimp only [representative]
      rw [LatticeCrypto.Poly.toPi_ofPi]
    rw [LatticeCrypto.PolyBackend.toPolynomial]
    change (∑ coefficient : Fin degree,
      Polynomial.monomial coefficient.val
        ((LatticeCrypto.vectorBackend (ZMod q) degree).coeff representative coefficient)) =
      remainder
    simp_rw [hcoeff]
    apply Polynomial.ext
    intro coefficient
    rw [Polynomial.finsetSum_coeff]
    by_cases hcoefficient : coefficient < degree
    · let index : Fin degree := ⟨coefficient, hcoefficient⟩
      rw [Finset.sum_eq_single index]
      · simp [index]
      · intro other _ hother
        simp only [Polynomial.coeff_monomial]
        rw [if_neg]
        intro heq
        apply hother
        apply Fin.ext
        exact heq
      · simp
    · have hdegreeRemainder : remainder.degree < (coefficient : WithBot ℕ) := by
        exact lt_of_lt_of_le
          ((Polynomial.degree_modByMonic_lt polynomial hmonic).trans_le hdegreeModulus)
          (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hcoefficient))
      rw [Polynomial.coeff_eq_zero_of_degree_lt hdegreeRemainder]
      apply Finset.sum_eq_zero
      intro index _
      simp [Polynomial.coeff_monomial,
        ne_of_lt (index.isLt.trans_le (Nat.le_of_not_gt hcoefficient))]
  change Ideal.Quotient.mk _
      ((LatticeCrypto.vectorBackend (ZMod q) degree).toPolynomial representative) =
    Ideal.Quotient.mk _ polynomial
  rw [hrepresentative, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
    Ideal.mem_span_singleton]
  refine ⟨-(polynomial /ₘ modulus), ?_⟩
  change remainder - polynomial = modulus * -(polynomial /ₘ modulus)
  dsimp only [remainder]
  rw [Polynomial.modByMonic_eq_sub_mul_div]
  ring

/-- The executable carrier and its semantic quotient are in bijection. -/
theorem quotientOf_bijective {q degree : ℕ} [Nontrivial (ZMod q)]
    (hdegree : 0 < degree) :
    Function.Bijective (quotientOf (q := q) hdegree) :=
  ⟨quotientOf_injective hdegree, quotientOf_surjective hdegree⟩

/-- The executable coefficient carrier is equivalent to its semantic polynomial quotient.  The
separate soundness theorems record preservation of the executable ring operations. -/
noncomputable def quotientEquiv {q degree : ℕ} [Nontrivial (ZMod q)]
    (hdegree : 0 < degree) : Rq q degree ≃ QuotientRq q degree :=
  Equiv.ofBijective (quotientOf hdegree) (quotientOf_bijective hdegree)

/-- The one-row public challenge containing `sampleCount` ring elements. -/
abbrev Sample (q degree sampleCount : ℕ) :=
  Matrix (Fin 1) (Fin sampleCount) (Rq q degree)

/-- The rank-one RLWE secret, represented in the matrix-LWE interface. -/
abbrev Secret (q degree : ℕ) := Fin 1 → Rq q degree

/-- The noisy right-hand sides of `sampleCount` RLWE samples. -/
abbrev Output (q degree sampleCount : ℕ) := Fin sampleCount → Rq q degree

/-- A rank-`rank` module-LWE public challenge over the same negacyclic ring. -/
abbrev ModuleSample (q degree rank sampleCount : ℕ) :=
  Matrix (Fin rank) (Fin sampleCount) (Rq q degree)

/-- A rank-`rank` module-LWE secret over the same negacyclic ring. -/
abbrev ModuleSecret (q degree rank : ℕ) := Fin rank → Rq q degree

/-- The output vector for a rank-`rank` module-LWE challenge. -/
abbrev ModuleOutput (q degree sampleCount : ℕ) := Fin sampleCount → Rq q degree

/-- A one-row matrix is equivalent to the usual vector of public RLWE elements. -/
def sampleEquiv (q degree sampleCount : ℕ) :
    Sample q degree sampleCount ≃ (Fin sampleCount → Rq q degree) where
  toFun matrix := matrix 0
  invFun vector := fun _ j ↦ vector j
  left_inv matrix := by
    funext i j
    rw [Subsingleton.elim i 0]
  right_inv _ := rfl

/-- A rank-one matrix-LWE secret is equivalent to one ring element. -/
def secretEquiv (q degree : ℕ) : Secret q degree ≃ Rq q degree where
  toFun secret := secret 0
  invFun value := fun _ ↦ value
  left_inv secret := by
    funext i
    exact congrArg secret (Subsingleton.elim 0 i)
  right_inv _ := rfl

/-- Finite module-LWE over the negacyclic ring, with a uniform module secret. -/
noncomputable def moduleProblem (q degree rank sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (Rq q degree)) :
    LearningWithErrors.Problem
      (ModuleSample q degree rank sampleCount) (ModuleSecret q degree rank)
      (ModuleOutput q degree sampleCount) :=
  LearningWithErrors.moduleMatrixProblem
    (α := Rq q degree) rank sampleCount errorSampler

/-- Decisional RLWE with an explicit secret and error sampler.

For public ring elements `aⱼ`, a shared secret `s`, and independent errors `eⱼ`, the
real branch returns `(aⱼ, s * aⱼ + eⱼ)` and the uniform branch returns
`(aⱼ, uⱼ)`. The one-row representation makes this exactly rank-one batch LWE over
the finite commutative ring `Rq q degree`. -/
noncomputable def problem (q degree sampleCount : ℕ) [NeZero q]
    (secretSampler : ProbComp (Secret q degree))
    (errorSampler : ProbComp (Rq q degree)) :
    LearningWithErrors.Problem
      (Sample q degree sampleCount) (Secret q degree) (Output q degree sampleCount) := by
  exact LWE.batchProblem 1 sampleCount secretSampler errorSampler

/-- The finite quotient-ring decisional problem with a uniform ring secret. -/
noncomputable def uniformSecretProblem (q degree sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (Rq q degree)) :
    LearningWithErrors.Problem
      (Sample q degree sampleCount) (Secret q degree) (Output q degree sampleCount) := by
  exact problem q degree sampleCount ($ᵗ (Secret q degree)) errorSampler

/-- The explicit-secret RLWE problem is definitionally rank-one batch LWE over `Rq`. -/
theorem problem_eq_batchProblem (q degree sampleCount : ℕ) [NeZero q]
    (secretSampler : ProbComp (Secret q degree))
    (errorSampler : ProbComp (Rq q degree)) :
    problem q degree sampleCount secretSampler errorSampler =
      LWE.batchProblem 1 sampleCount secretSampler errorSampler := by
  rfl

/-- Uniform-secret finite RLWE is the rank-one specialization of VCVio's module-LWE problem. -/
theorem uniformSecretProblem_eq_moduleMatrixProblem
    (q degree sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (Rq q degree)) :
    uniformSecretProblem q degree sampleCount errorSampler =
      LearningWithErrors.moduleMatrixProblem
        (α := Rq q degree) 1 sampleCount errorSampler := by
  rfl

/-- Uniform-secret finite RLWE is exactly rank-one module-LWE over the same ring. -/
theorem uniformSecretProblem_eq_moduleProblem_one
    (q degree sampleCount : ℕ) [NeZero q]
    (errorSampler : ProbComp (Rq q degree)) :
    uniformSecretProblem q degree sampleCount errorSampler =
      moduleProblem q degree 1 sampleCount errorSampler := by
  rfl

end FormalProof4FHE.RLWE
