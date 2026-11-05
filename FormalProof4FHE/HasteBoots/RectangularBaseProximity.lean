module

public import FormalProof4FHE.HasteBoots.ModuleCodeProximity
public import FormalProof4FHE.HasteBoots.StructuredOpening

@[expose] public section

/-! Rectangular base-field tests on the actual whole-column block-code layout.
`codeWidth` is the symbol width; `testWidth` is the number of independent
random rows. They need not agree. This is a fixed-word interactive law;
production oracle causality and availability remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.RectangularBaseProximity

open Code ProbabilityTheory

noncomputable section

variable {F Position Row : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Position] [Fintype Row] {codeWidth : ℕ}

def stack (word : Position → Row → Fin codeWidth → F) : WordStack (A := Fin codeWidth → F) Row Position :=
  Matrix.of (fun row position => word position row)

omit [Fintype F] [DecidableEq F] [Fintype Position] in
/-- Every row combination uses precisely the native complete-symbol layout. -/
theorem combination (word : Position → Row → Fin codeWidth → F) (weights : Row → F) :
    Fintype.linearCombination F (Matrix.of.symm (stack word)) weights =
      StructuredOpening.combine weights word := by
  ext position coordinate
  simp only [Fintype.linearCombination_apply,stack,Matrix.of_symm_apply,
    Matrix.of_apply,StructuredOpening.combine,Finset.sum_apply,Pi.smul_apply]

omit [Fintype F] in
/-- The far premise is measured on common columns containing every row and
symbol coordinate, exactly as for the common-source decoder. -/
theorem far_lift (domain : Position ↪ F) (m radius : ℕ)
    (word : Position → Row → Fin codeWidth → F)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧
      hammingDist word source ≤ radius) :
    radius < Code.distFromCode (⋈|stack word) ((BlockCode.code domain m codeWidth)^⋈Row) := by
  classical
  by_contra notFar
  obtain ⟨source,coded,close⟩ := (Code.closeToCode_iff_closeToCodeword_of_minDist
    (u := (⋈|stack word)) (C := ((BlockCode.code domain m codeWidth)^⋈Row)) (e := radius)).mp
      (not_lt.mp notFar)
  apply far
  refine ⟨fun position row => source position row, ?_, ?_⟩
  · exact (Code.mem_moduleInterleavedCode_iff (F := F) (A := Fin codeWidth → F)
      (κ := Row) (ι := Position) (MC := BlockCode.code domain m codeWidth) (v := source)).mp coded
  · exact close

/-- Independent base-field rows yield a conservative rectangular bound. No
extension-field identification or equality of the two widths is required. -/
theorem matrix_bound (domain : Position ↪ F) (m radius testWidth : ℕ)
    (word : Position → Row → Fin codeWidth → F)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Submodule.span F (Set.range (stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)))
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧
      hammingDist word source ≤ radius) :
    Pr{let matrix ← $ᵗ (Fin testWidth → Row → F)}[∀ lane,
      Code.distFromCode (StructuredOpening.combine (matrix lane) word)
        (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) ≤ radius] ≤
      ((Code.minDist (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) : ENNReal) /
        Fintype.card F)^testWidth := by
  have bound := ModuleCodeProximity.rectangular_bound (BlockCode.code domain m codeWidth)
    (stack word) radius testWidth large small (far_lift domain m radius word far)
  simpa only [combination] using bound

/-- Explicit RS distance, still with independent test and code-symbol widths. -/
theorem matrix_bound_distance [Nonempty Position] [NeZero codeWidth]
    (domain : Position ↪ F) (m radius testWidth : ℕ) (positive : 0 < m)
    (word : Position → Row → Fin codeWidth → F)
    [SampleableType (Row → F)] [SampleableType (Fin testWidth → Row → F)]
    [SampleableType (Submodule.span F (Set.range (stack word)))]
    [SampleableType (ModuleCodeProximity.toSpan (F := F) (stack word)).toAddMonoidHom.ker]
    (large : radius < Fintype.card F)
    (small : 3*radius < Fintype.card Position - m + 1)
    (far : ¬ ∃ source, CommonSource.RowsIn (BlockCode.code domain m codeWidth) source ∧
      hammingDist word source ≤ radius) :
    Pr{let matrix ← $ᵗ (Fin testWidth → Row → F)}[∀ lane,
      Code.distFromCode (StructuredOpening.combine (matrix lane) word)
        (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) ≤ radius] ≤
      (((Fintype.card Position - m + 1 : ℕ) : ENNReal) / Fintype.card F)^testWidth := by
  have smallCode : 3*radius < Code.minDist
      (BlockCode.code domain m codeWidth : Set (Position → Fin codeWidth → F)) := by
    rwa [BlockCode.minDist domain m codeWidth positive]
  simpa only [BlockCode.minDist domain m codeWidth positive] using
    matrix_bound domain m radius testWidth word large smallCode far

end
end FormalProof4FHE.HasteBoots.RectangularBaseProximity
