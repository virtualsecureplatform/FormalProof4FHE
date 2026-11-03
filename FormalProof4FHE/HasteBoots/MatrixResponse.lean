module

public import FormalProof4FHE.HasteBoots.ResponseCoefficients
public import FormalProof4FHE.HasteBoots.MatrixOpening

@[expose] public section

/-!
# Matrix-query finishing through encoded structured responses

Native rows are indexed by (left index, input channel), and structured response
lanes are indexed by output channel. The original right-message length may be
strictly less than the padded block capacity. Extraction truncates coefficient
rows to that original length, so nonzero padding in an abstract decoded source
does not change the claimed table relation.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.MatrixResponse

noncomputable section

variable {F Position Left : Type} [Field F] [Fintype Left] {m b size : ℕ}

/-- The exact native structured weight address, with both row components explicit. -/
def weights (left : Left → Matrix (Fin b) (Fin b) F) (lane : Fin b)
    (row : Left × Fin b) : F := left row.1 lane row.2

/-- Recover only the original right-message coordinates of each response lane. -/
def recoverResponse (domain : Position → F) (capacity : size ≤ m * b)
    (encoded : Fin b → Position → Fin b → F) : Fin size → Fin b → F :=
  fun right lane => RowLayout.recover capacity (ResponseCoefficients.decode domain (encoded lane)) right

/-- One common coefficient table, recovered independently of the opening query. -/
def extractTable (domain : Position → F) (capacity : size ≤ m * b)
    (source : Position → (Left × Fin b) → Fin b → F) : Left → Fin size → Fin b → F :=
  fun left right channel => RowLayout.recover capacity
    (ResponseCoefficients.decode domain (fun pos => source pos (left, channel))) right

/-- Analysis finishing map on encoded responses. -/
def finishEncoded (domain : Position → F) (capacity : size ≤ m * b)
    (right : Fin size → Matrix (Fin b) (Fin b) F)
    (encoded : Fin b → Position → Fin b → F) : Fin b → F :=
  ∑ r, right r *ᵥ recoverResponse domain capacity encoded r

/-- Native final fold on the unencoded lane-major response array. -/
def finishMessage (right : Fin size → Matrix (Fin b) (Fin b) F)
    (messages : Fin b → Fin size → F) : Fin b → F :=
  ∑ r, right r *ᵥ (fun lane => messages lane r)

/-- Analysis finishing recovers exactly the native messages, including zero padding. -/
theorem finishEncoded_padded [Fintype Position] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b)
    (right : Fin size → Matrix (Fin b) (Fin b) F) (messages : Fin b → Fin size → F) :
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
theorem recover_structured [Fintype Position] [NeZero m] [NeZero b]
    (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b)
    (left : Left → Matrix (Fin b) (Fin b) F)
    (source : Position → (Left × Fin b) → Fin b → F)
    (coded : CommonSource.RowsIn (BlockCode.code domain m b) source) :
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
theorem finish_structured_eq_evaluation [Fintype Position] [NeZero m] [NeZero b]
    (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b)
    (left : Left → Matrix (Fin b) (Fin b) F) (right : Fin size → Matrix (Fin b) (Fin b) F)
    (source : Position → (Left × Fin b) → Fin b → F)
    (coded : CommonSource.RowsIn (BlockCode.code domain m b) source) :
    finishEncoded domain capacity right (fun lane => StructuredOpening.combine (weights left lane) source) =
      matrixEvaluation left right (extractTable domain capacity source) := by
  unfold finishEncoded
  rw [recover_structured domain enough capacity left source coded]
  exact foldedOpening_eq_matrixEvaluation left right (extractTable domain capacity source)

omit [Fintype Left] in
/-- An honest padded row encoding extracts the original table, without padding entries. -/
theorem extractTable_encoded [Fintype Position] (domain : Position ↪ F)
    (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b)
    (table : Left → Fin size → Fin b → F) :
    extractTable domain capacity (fun pos row => BlockEncoder.encode domain
      (RowLayout.padded (m := m) (fun right => table row.1 right row.2)) pos) = table := by
  funext left right channel
  simp only [extractTable, ResponseCoefficients.decode_encode domain enough, RowLayout.recover_padded]

end

end FormalProof4FHE.HasteBoots.MatrixResponse
