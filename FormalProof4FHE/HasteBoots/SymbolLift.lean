module

public import FormalProof4FHE.HasteBoots.BlockEncoder
public import Mathlib.LinearAlgebra.Basis.Defs
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Lifting base-field symbol coordinates to a field alphabet

The symbol field K is an analysis device with a fixed F-basis. It is separate
from the extension field used by lookups. No relationship between their degrees
is assumed. In native full-width tests, b independently sampled coordinates
per source row assemble to one uniform K coefficient. Freshness of production
XOF phases remains separate. `RowSpanSampling` handles the coefficient-to-span
pushforward, including dependent source rows.
-/

open scoped BigOperators
open ProbabilityTheory Module

namespace FormalProof4FHE.HasteBoots.SymbolLift

noncomputable section

variable {F K Row Position : Type} [Field F] [Field K] [Algebra F K] {b m : ℕ}

/-- Assemble one whole base-field symbol using a fixed basis. -/
def pack (basis : Basis (Fin b) F K) : (Fin b → F) ≃ₗ[F] K := basis.equivFun.symm

/-- Assemble the coordinates of every encoded symbol. -/
def packWord (basis : Basis (Fin b) F K) (word : Position → Fin b → F) : Position → K :=
  fun pos => pack basis (word pos)

/-- Whole-symbol disagreements are exactly field-alphabet disagreements. -/
theorem distance_eq [Fintype Position] [DecidableEq F] [DecidableEq K]
    (basis : Basis (Fin b) F K) (left right : Position → Fin b → F) :
    hammingDist (packWord basis left) (packWord basis right) = hammingDist left right :=
  hammingDist_comp (fun _ => pack basis) (fun _ => (pack basis).injective)

/-- Base-linear coordinate evaluation is scalar RS evaluation over the symbol field. -/
theorem pack_encode (basis : Basis (Fin b) F K) (domain : Position → F)
    (input : Fin m → Fin b → F) (pos : Position) :
    packWord basis (BlockEncoder.encode domain input) pos =
      ∑ j : Fin m, pack basis (input j) * (algebraMap F K (domain pos)) ^ j.val := by
  classical
  have h : BlockEncoder.encode domain input pos =
      ∑ j : Fin m, (domain pos ^ j.val) • input j := by
    ext lane
    simp [BlockEncoder.encode, Finset.sum_apply, mul_comm]
  change pack basis (BlockEncoder.encode domain input pos) = _
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(pack basis).map_smul]
  simp only [Algebra.smul_def, map_pow]
  exact mul_comm _ _

/-- The base evaluation domain embeds injectively into the symbol field. -/
def liftedDomain (domain : Position ↪ F) : Position ↪ K :=
  ⟨fun pos => algebraMap F K (domain pos), (algebraMap F K).injective.comp domain.injective⟩

theorem encode_mem_scalarCode (basis : Basis (Fin b) F K) (domain : Position ↪ F)
    (input : Fin m → Fin b → F) :
    packWord basis (BlockEncoder.encode domain input) ∈
      ReedSolomon.code (liftedDomain (K := K) domain) m := by
  let p : Polynomial K := ∑ j : Fin m,
    Polynomial.C (pack basis (input j)) * Polynomial.X ^ j.val
  apply ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval p
    (Polynomial.degree_sum_fin_lt _)
  intro pos
  rw [pack_encode]
  simp [p, liftedDomain, Polynomial.eval_finsetSum]

/-- Native test matrices are lane-major; assembly transposes then applies the basis bijection. -/
def coefficients (basis : Basis (Fin b) F K) : (Fin b → Row → F) ≃ (Row → K) :=
  (Equiv.piComm (fun _ : Fin b => fun _ : Row => F)).trans
    (Equiv.piCongrRight (fun _ => (pack basis).toEquiv))

theorem coefficients_apply (basis : Basis (Fin b) F K)
    (matrix : Fin b → Row → F) (row : Row) :
    coefficients basis matrix row = pack basis (fun lane => matrix lane row) := rfl

/-- Combining the b base test rows yields exactly a scalar K-linear row test. -/
theorem combine_tests [Fintype Row] (basis : Basis (Fin b) F K)
    (matrix : Fin b → Row → F) (rows : Row → K) :
    (∑ lane : Fin b, basis lane *
      (∑ row : Row, algebraMap F K (matrix lane row) * rows row)) =
      ∑ row : Row, coefficients basis matrix row * rows row := by
  classical
  simp only [coefficients_apply, pack, Basis.equivFun_symm_apply, Algebra.smul_def,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro lane _
  ring

/-- The alphabet size follows from the basis; it is not a guessed security parameter. -/
theorem cardinality [Fintype F] [Fintype K] (basis : Basis (Fin b) F K) :
    Fintype.card K = Fintype.card F ^ b := by
  rw [Fintype.card_congr basis.equivFun.toEquiv]
  simp

/-- Uniform full-width matrices give exactly uniform symbol-field coefficients. -/
theorem uniform_coefficients (basis : Basis (Fin b) F K)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)] :
    coefficients basis <$> ($ᵗ (Fin b → Row → F) : ProbComp (Fin b → Row → F)) =ᵈ
      ($ᵗ (Row → K) : ProbComp (Row → K)) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective (coefficients basis).bijective

end

end FormalProof4FHE.HasteBoots.SymbolLift
