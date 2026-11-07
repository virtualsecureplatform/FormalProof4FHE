module
public import FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixExtraction
@[expose] public section
namespace FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixSoundness
open ProbabilityTheory Matrix OracleComp
variable {F Response : Type} [Field F] [Fintype F] [DecidableEq F]
  {n leftSize m packingWidth codeWidth size : ℕ}

/-! The existing interactive matrix-opening bound with an executable extracted
table. The probability experiment and both independent widths are unchanged;
this is not a Fiat–Shamir or native implementation refinement. -/
theorem soundness_bound [NeZero m] [NeZero codeWidth] (domain : Fin n ↪ F)
    (enough : m ≤ Fintype.card (Fin n)) (capacity : size ≤ m*codeWidth) (radius testWidth queries : ℕ)
    (word : Fin n → (Fin leftSize × Fin packingWidth) → Fin codeWidth → F)
    (left : Fin leftSize → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (respond : (Fin testWidth → (Fin leftSize × Fin packingWidth) → F) → ProbComp Response)
    (testResponse : (Fin testWidth → (Fin leftSize × Fin packingWidth) → F) → Response → Fin testWidth → Fin size → F)
    (structuredResponse : (Fin testWidth → (Fin leftSize × Fin packingWidth) → F) → Response → Fin packingWidth → Fin size → F)
    [SampleableType ((Fin leftSize × Fin packingWidth) → F)]
    [SampleableType (Fin testWidth → (Fin leftSize × Fin packingWidth) → F)] [SampleableType (Fin queries → Fin n)]
    [SampleableType (Submodule.span F (Set.range (RectangularBaseProximity.stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (RectangularBaseProximity.stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Fin n → Fin codeWidth → F))) :
    Pr{let pair ← RectangularOpeningKernel.experiment (F := F) (Row := Fin leftSize × Fin packingWidth) (Position := Fin n) testWidth queries respond}[
      RectangularMatrixResponse.finishMessage right (structuredResponse pair.1.1 pair.1.2) ≠
        matrixEvaluation left right (ExecutableRectangularMatrixExtraction.table radius domain capacity word) ∧
      RectangularMatrixOpeningKernel.Checks (m := m) domain word pair.1.1 (testResponse pair.1.1 pair.1.2) pair.2 ∧
      RectangularMatrixOpeningKernel.Checks (m := m) domain word (RectangularMatrixResponse.weights left) (structuredResponse pair.1.1 pair.1.2) pair.2] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Fin n → Fin codeWidth → F)) : ENNReal) / Fintype.card F)^testWidth +
      max (ColumnOpening.missBound (Fin n) queries (Code.minDist (BlockCode.code domain m codeWidth : Set (Fin n → Fin codeWidth → F)) - radius))
        (ColumnOpening.missBound (Fin n) queries (radius+1)) := by
  have positive : 0 < n := lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne m)) (by simpa using enough)
  let : NeZero n := ⟨Nat.ne_of_gt positive⟩
  have uniqueRadius : 2 * radius < n - m + 1 := by
    rw [BlockCode.minDist domain m codeWidth (Nat.pos_of_ne_zero (NeZero.ne m)),Fintype.card_fin] at small
    omega
  rw [ExecutableRectangularMatrixExtraction.table_eq_analysis radius domain capacity word uniqueRadius (by simpa using enough)]
  exact RectangularMatrixOpeningKernel.soundness_bound domain enough capacity radius testWidth queries word
    left right respond testResponse structuredResponse large small
end FormalProof4FHE.HasteBoots.ExecutableRectangularMatrixSoundness
