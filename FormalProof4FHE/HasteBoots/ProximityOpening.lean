module

public import FormalProof4FHE.HasteBoots.BaseMatrixProximity
public import FormalProof4FHE.HasteBoots.ColumnOpening

@[expose] public section

/-!
# Fixed far-word opening bound with adaptive coded responses

The response may be any function of the full-width random test matrix. Columns
are sampled afterwards and are shared by all verifier checks. The bound is a
sum of a row-span proximity term and one column-avoidance term, not a product
of independent test probabilities. This is an interactive fixed-available-word
lemma; authentication and production transcript compilation remain open.
-/

open ProbabilityTheory

namespace FormalProof4FHE.HasteBoots.ProximityOpening

noncomputable section

variable {F K Row Position : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Row] [Fintype Position] [DecidableEq Position] {m b : ℕ}

/-- Scalar symbol-field word produced by the native full-width matrix test. -/
def randomWord (basis : Module.Basis (Fin b) F K)
    (word : Position → Row → Fin b → F) (matrix : Fin b → Row → F) : Position → K :=
  Fintype.linearCombination K (RowSpanSampling.rowFamily (BaseMatrixProximity.stack basis word))
    (SymbolLift.coefficients basis matrix)

/-- The far branch, allowing an arbitrary coded response chosen after seeing
the random matrix. No uniform law for that response is required. -/
theorem far_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius queries : ℕ) (word : Position → Row → Fin b → F)
    (claimed : (Fin b → Row → F) → Position → K)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧
      hammingDist word source ≤ radius)
    (coded : ∀ matrix, claimed matrix ∈
      ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m) :
    Pr{let matrix ← $ᵗ (Fin b → Row → F); let draw ← $ᵗ (Fin queries → Position)}[
      ColumnOpening.Agrees (randomWord basis word matrix) (claimed matrix) draw] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      (((Fintype.card Position - (radius + 1) : ℕ) : ENNReal) /
        Fintype.card Position) ^ queries := by
  have columnBound := ColumnOpening.adaptive_far_bound ($ᵗ (Fin b → Row → F))
    (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m)
    (randomWord basis word) claimed radius queries coded
  exact columnBound.trans (add_le_add
    (BaseMatrixProximity.matrix_bound basis domain radius word small far) le_rfl)

/-- Encoded responses satisfy the code premise by construction, including
malicious response coefficients selected as a function of the random matrix. -/
theorem encoded_far_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (radius queries : ℕ) (word : Position → Row → Fin b → F)
    (response : (Fin b → Row → F) → Fin m → Fin b → F)
    [SampleableType (Fin b → Row → F)] [SampleableType (Row → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m b) source ∧
      hammingDist word source ≤ radius) :
    Pr{let matrix ← $ᵗ (Fin b → Row → F); let draw ← $ᵗ (Fin queries → Position)}[
      ColumnOpening.Agrees (randomWord basis word matrix)
        (SymbolLift.packWord basis (BlockEncoder.encode domain (response matrix))) draw] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      (((Fintype.card Position - (radius + 1) : ℕ) : ENNReal) /
        Fintype.card Position) ^ queries :=
  far_bound basis domain radius queries word _ small far
    (fun matrix => SymbolLift.encode_mem_scalarCode basis domain (response matrix))

end

end FormalProof4FHE.HasteBoots.ProximityOpening
