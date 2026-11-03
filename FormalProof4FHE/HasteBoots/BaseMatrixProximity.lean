module

public import FormalProof4FHE.HasteBoots.CodeCorrespondence
public import FormalProof4FHE.HasteBoots.RowSpanSampling

@[expose] public section

/-!
# Proximity testing with a base-coordinate common-source premise

The matrix sampler bound applies to the complete base-field column layout.
Neither a fresh production XOF law nor Merkle availability is assumed proved here.
-/

open ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.BaseMatrixProximity

noncomputable section

variable {F K Row Position : Type} [Field F] [Field K] [Algebra F K]
  [Fintype Row] [Fintype Position] [DecidableEq F] [DecidableEq K] {m b : ℕ}

/-- ArkLib's row-major stack for the same complete base-coordinate word. -/
def stack (basis : Module.Basis (Fin b) F K)
    (word : Position → Row → Fin b → F) : Code.WordStack (A := K) Row Position :=
  Matrix.of (fun row pos => SymbolLift.pack basis (word pos row))

/-- A base word with no common nearby coded source is also far from the lifted
interleaved code. No per-row choice of error columns is permitted. -/
theorem far_lift [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius : ℕ) (word : Position → Row → Fin b → F)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧
      hammingDist word source ≤ radius) :
    radius < Code.distFromCode (⋈|stack basis word)
      ((ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m)^⋈Row) := by
  classical
  by_contra notFar
  have close := (Code.closeToCode_iff_closeToCodeword_of_minDist
    (⋈|stack basis word) radius).mp (not_lt.mp notFar)
  obtain ⟨source, coded, close⟩ := close
  apply far
  apply (CodeCorrespondence.nearby_iff basis domain radius word).mpr
  refine ⟨fun pos row => source pos row, ?_, ?_⟩
  · exact coded
  · exact_mod_cast close

/-- Full-width base-field coins test a base-coordinate word with the AHIV22
bound. The far premise is now stated on the same layout as the common decoder. -/
theorem matrix_bound [Fintype F] [Fintype K] [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius : ℕ) (word : Position → Row → Fin b → F)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Matrix.rowSpan (stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧
      hammingDist word source ≤ radius) :
    Pr{let matrix ← $ᵗ (Fin b → Row → F)}[
      Code.distFromCode
        (Fintype.linearCombination K (RowSpanSampling.rowFamily (stack basis word))
          (SymbolLift.coefficients basis matrix))
        (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
          Set (Position → K)) ≤ radius] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) := by
  exact RowSpanSampling.matrix_bound basis _ m radius (stack basis word) small
    (far_lift basis domain radius word far)

end

end FormalProof4FHE.HasteBoots.BaseMatrixProximity
