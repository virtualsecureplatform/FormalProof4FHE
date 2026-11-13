module
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout
public import FormalProof4FHE.HasteBoots.PaddedSourceAddress
public import FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
@[expose] public section

/-! Query-independent packed sources decoded from independent code-symbol
widths. Only physical encoding and capacity use codeWidth; query lanes retain
the packing width, including the native three-lane helper case. -/
namespace FormalProof4FHE.HasteBoots.RectangularSubclaimSourceLayout
noncomputable section
variable {F Position : Type} [Field F] [DecidableEq F] [Fintype Position]
  {front suffix packingWidth codeWidth degree n : ℕ}

def decodedSource (domain : Position ↪ F) (capacity : 2^suffix ≤ degree*codeWidth) (radius : ℕ)
    (word : Position → (Fin (2^front) × Fin packingWidth) → Fin codeWidth → F) :
    MatrixFold.Cube (front+suffix) → Fin packingWidth → F :=
  SubclaimSourceLayout.source (RectangularMatrixOpeningKernel.extract domain capacity radius word)

/-- The existing native matrix-query split evaluates the exact rectangular
extracted table, without changing the logical packed query. -/
theorem fold_decodedSource (domain : Position ↪ F) (capacity : 2^suffix ≤ degree*codeWidth) (radius : ℕ)
    (word : Position → (Fin (2^front) × Fin packingWidth) → Fin codeWidth → F)
    (query : PackedSumcheckSubclaim.Query F packingWidth (front+suffix)) :
    query.fold (decodedSource domain capacity radius word) =
      matrixEvaluation (SubclaimSourceLayout.leftWeights query) (SubclaimSourceLayout.rightWeights query)
        (RectangularMatrixOpeningKernel.extract domain capacity radius word) :=
  SubclaimSourceLayout.fold_source query _

/-- High-zero padding keeps the original native scalar address of this same
fixed rectangular decoder, just as for square original-source workers. -/
theorem padded_decoded_source (padding : ℕ) (dimensions : padding+n = front+suffix)
    (domain : Position ↪ F) (capacity : 2^suffix ≤ degree*codeWidth) (radius : ℕ)
    (word : Position → (Fin (2^front) × Fin packingWidth) → Fin codeWidth → F) :
    QueryHighZeroPadding.source padding (QueryReindex.source dimensions (decodedSource domain capacity radius word)) =
      PaddedSourceAddress.logical n (RectangularMatrixOpeningKernel.extract domain capacity radius word) :=
  PaddedSourceAddress.padded_source padding dimensions _

/-- Square source semantics are recovered exactly, without a new decoding law. -/
theorem square (domain : Position ↪ F) (capacity : 2^suffix ≤ degree*packingWidth) (radius : ℕ)
    (word : Position → (Fin (2^front) × Fin packingWidth) → Fin packingWidth → F) :
    decodedSource domain capacity radius word = SubclaimSourceLayout.decodedSource domain capacity radius word := rfl

end
end FormalProof4FHE.HasteBoots.RectangularSubclaimSourceLayout
