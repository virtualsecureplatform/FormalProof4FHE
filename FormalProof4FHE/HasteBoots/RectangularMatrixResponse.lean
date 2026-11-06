module

public import FormalProof4FHE.HasteBoots.ResponseCoefficients
public import FormalProof4FHE.HasteBoots.MatrixOpening

@[expose] public section

/-! Matrix-query finishing and one query-independent coefficient extractor
with independent packing and code-symbol widths. Source padding is truncated
to the original right-message length. This is algebraic transport, not an
efficient decoder, transcript-freshness or application-security theorem. -/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.RectangularMatrixResponse

noncomputable section

variable {F Position Left : Type} [Field F] [Fintype Left] {m packingWidth codeWidth size : ℕ}

/-- The exact native structured weight address, with both row components explicit. -/
def weights (left : Left → Matrix (Fin packingWidth) (Fin packingWidth) F) (lane : Fin packingWidth)
    (row : Left × Fin packingWidth) : F := left row.1 lane row.2

/-- Recover only the original right-message coordinates of each response lane. -/
def recoverResponse (domain : Position → F) (capacity : size ≤ m * codeWidth)
    (encoded : Fin packingWidth → Position → Fin codeWidth → F) : Fin size → Fin packingWidth → F :=
  fun right lane => RowLayout.recover capacity (ResponseCoefficients.decode domain (encoded lane)) right

/-- One common coefficient table, recovered independently of the opening query. -/
def extractTable (domain : Position → F) (capacity : size ≤ m * codeWidth)
    (source : Position → (Left × Fin packingWidth) → Fin codeWidth → F) : Left → Fin size → Fin packingWidth → F :=
  fun left right channel => RowLayout.recover capacity
    (ResponseCoefficients.decode domain (fun pos => source pos (left, channel))) right

/-- Analysis finishing map on encoded responses. -/
def finishEncoded (domain : Position → F) (capacity : size ≤ m * codeWidth)
    (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (encoded : Fin packingWidth → Position → Fin codeWidth → F) : Fin packingWidth → F :=
  ∑ r, right r *ᵥ recoverResponse domain capacity encoded r

/-- Native final fold on the unencoded lane-major response array. -/
def finishMessage (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (messages : Fin packingWidth → Fin size → F) : Fin packingWidth → F :=
  ∑ r, right r *ᵥ (fun lane => messages lane r)

/-- Analysis finishing recovers exactly the native messages, including zero padding. -/
theorem finishEncoded_padded [Fintype Position] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * codeWidth)
    (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F) (messages : Fin packingWidth → Fin size → F) :
    finishEncoded domain capacity right
      (fun lane => BlockEncoder.encode domain (RowLayout.padded (m := m) (messages lane))) =
      finishMessage right messages := by
  classical
  unfold finishEncoded finishMessage
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  funext lane
  change RowLayout.recover capacity
    (ResponseCoefficients.decode domain (BlockEncoder.encode domain
      (RowLayout.padded (m := m) (messages lane)))) r = messages lane r
  rw [ResponseCoefficients.decode_encode domain enough, RowLayout.recover_padded]

/-- Structured response recovery agrees with the ordered left matrix aggregation. -/
theorem recover_structured [Fintype Position] [NeZero m] [NeZero codeWidth]
    (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * codeWidth)
    (left : Left → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (source : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (coded : CommonSource.RowsIn (BlockCode.code domain m codeWidth) source) :
    recoverResponse domain capacity (fun lane => StructuredOpening.combine (weights left lane) source) =
      leftResponse left (extractTable domain capacity source) := by
  classical
  funext right lane
  unfold recoverResponse
  rw [ResponseCoefficients.decode_combine domain enough _ source coded,
    ResponseCoefficients.recover_aggregate]
  simp only [weights, Fintype.sum_prod_type, leftResponse, Matrix.mulVec, dotProduct,
    Finset.sum_apply, extractTable]

/-- The native ordered matrix evaluation is precisely the analysis finishing of
the common source's structured coded responses. -/
theorem finish_structured_eq_evaluation [Fintype Position] [NeZero m] [NeZero codeWidth]
    (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * codeWidth)
    (left : Left → Matrix (Fin packingWidth) (Fin packingWidth) F) (right : Fin size → Matrix (Fin packingWidth) (Fin packingWidth) F)
    (source : Position → (Left × Fin packingWidth) → Fin codeWidth → F)
    (coded : CommonSource.RowsIn (BlockCode.code domain m codeWidth) source) :
    finishEncoded domain capacity right (fun lane => StructuredOpening.combine (weights left lane) source) =
      matrixEvaluation left right (extractTable domain capacity source) := by
  unfold finishEncoded
  rw [recover_structured domain enough capacity left source coded]
  exact foldedOpening_eq_matrixEvaluation left right (extractTable domain capacity source)

omit [Fintype Left] in
/-- An honest padded row encoding extracts the original table, without padding entries. -/
theorem extractTable_encoded [Fintype Position] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * codeWidth)
    (table : Left → Fin size → Fin packingWidth → F) :
    extractTable domain capacity (fun pos row => BlockEncoder.encode domain
      (RowLayout.padded (m := m) (fun right => table row.1 right row.2)) pos) = table := by
  funext left right channel
  simp only [extractTable, ResponseCoefficients.decode_encode domain enough, RowLayout.recover_padded]

end

end FormalProof4FHE.HasteBoots.RectangularMatrixResponse
