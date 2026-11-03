module

public import FormalProof4FHE.HasteBoots.SymbolLift
public import FormalProof4FHE.HasteBoots.UniformImage
public import FormalProof4FHE.HasteBoots.RowSpanProximity
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
# Actual linear-combination sampling versus uniform row-span sampling

Dependencies between source rows are allowed: a surjective linear map has
uniform fibers. This removes the abstract row-span sampler from the proximity
bound. `matrix_bound` also incorporates symbol-basis assembly. Fresh canonical
production coins and the authenticated fixed-word interpretation remain open.
-/

open ProbabilityTheory
open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.RowSpanSampling

noncomputable section

variable {K Row Position : Type} [Field K] [Fintype Row]

def rowFamily (word : Code.WordStack (A := K) Row Position) : Row → Position → K :=
  Matrix.of.symm word

def toSpan (word : Code.WordStack (A := K) Row Position) : (Row → K) →ₗ[K] Matrix.rowSpan word :=
  (Fintype.linearCombination K (rowFamily word)).codRestrict (Matrix.rowSpan word) (fun coefficients => by
    apply Submodule.sum_mem
    intro row _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨row, rfl⟩))

theorem toSpan_surjective (word : Code.WordStack (A := K) Row Position) : Function.Surjective (toSpan word) := by
  intro value
  have member : value.val ∈ Submodule.span K (Set.range (rowFamily word)) := value.property
  obtain ⟨coefficients, h⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp member
  exact ⟨coefficients, Subtype.ext h⟩

theorem coefficient_event (word : Code.WordStack (A := K) Row Position)
    [SampleableType (Row → K)] [SampleableType (Matrix.rowSpan word)]
    [SampleableType (toSpan word).toAddMonoidHom.ker] (event : (Position → K) → Prop) :
    Pr{let coefficients ← $ᵗ (Row → K)}[event (Fintype.linearCombination K (rowFamily word) coefficients)] =
      Pr{let sampled ← $ᵗ (Matrix.rowSpan word)}[event (sampled : Position → K)] :=
  UniformImage.uniform_event (toSpan word).toAddMonoidHom (toSpan_surjective word)
    (fun value => event value.val)

/-- The fixed-word bound now applies directly to uniformly sampled coefficient vectors. -/
theorem coefficient_bound [Fintype K] [DecidableEq K] [Fintype Position]
    (domain : Position ↪ K) (m radius : ℕ) (word : Code.WordStack (A := K) Row Position)
    [SampleableType (Row → K)] [SampleableType (Matrix.rowSpan word)]
    [SampleableType (toSpan word).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code domain m : Set (Position → K)) : ℚ≥0) / 3)
    (far : radius < Code.distFromCode (⋈|word) ((ReedSolomon.code domain m)^⋈Row)) :
    Pr{let coefficients ← $ᵗ (Row → K)}[
      Code.distFromCode (Fintype.linearCombination K (rowFamily word) coefficients)
        (ReedSolomon.code domain m : Set (Position → K)) ≤ radius] ≤
      (Code.minDist (ReedSolomon.code domain m : Set (Position → K)) : ENNReal) /
        Fintype.card K := by
  exact (coefficient_event word (fun value => Code.distFromCode value
    (ReedSolomon.code domain m : Set (Position → K)) ≤ radius)).trans_le
      (RowSpanProximity.fixedWord_bound domain m radius word small far)

/-- Full-width base-field test matrices inherit the RS row-span bound with denominator |F|^b.
This is conditional on a fixed available word and fresh uniform matrix coins. -/
theorem matrix_bound {F : Type} [Field F] [Fintype F] [Algebra F K]
    [Fintype K] [DecidableEq K] [Fintype Position] {b : ℕ}
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ K)
    (m radius : ℕ) (word : Code.WordStack (A := K) Row Position)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Matrix.rowSpan word)]
    [SampleableType (toSpan word).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code domain m : Set (Position → K)) : ℚ≥0) / 3)
    (far : radius < Code.distFromCode (⋈|word) ((ReedSolomon.code domain m)^⋈Row)) :
    Pr{let matrix ← $ᵗ (Fin b → Row → F)}[
      Code.distFromCode (Fintype.linearCombination K (rowFamily word)
        (SymbolLift.coefficients basis matrix))
        (ReedSolomon.code domain m : Set (Position → K)) ≤ radius] ≤
      (Code.minDist (ReedSolomon.code domain m : Set (Position → K)) : ENNReal) /
        (Fintype.card F ^ b) := by
  have transport := SampleableType.prEvent_uniformSample_equiv
    (SymbolLift.coefficients basis) (fun coefficients =>
      Code.distFromCode (Fintype.linearCombination K (rowFamily word) coefficients)
        (ReedSolomon.code domain m : Set (Position → K)) ≤ radius)
  have bound := coefficient_bound domain m radius word small far
  rw [SymbolLift.cardinality basis] at bound
  simp only [Nat.cast_pow] at bound
  exact transport.trans_le bound

end

end FormalProof4FHE.HasteBoots.RowSpanSampling
