module

public import FormalProof4FHE.HasteBoots.MatrixOpeningSecurity

@[expose] public section

/-!
# Semantic completeness of native matrix openings

Honest aggregation, zero padding and encoding satisfy every coordinate check,
for every draw vector. Native matrix-query finishing returns the intended
ordered evaluation. When the decoder is within its unique radius, the same
query-independent extractor returns the original table.
Merkle authentication and production byte/NTT refinements are not included.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness

noncomputable section

variable {F Position Left : Type} [Field F] [Fintype Left] {m b size : ℕ}

/-- Row/column layout of the honest packed table, encoded with native zero padding. -/
def encodedTable (domain : Position → F) (table : Left → Fin size → Fin b → F) :
    Position → (Left × Fin b) → Fin b → F :=
  fun pos row => BlockEncoder.encode domain
    (RowLayout.padded (m := m) (fun right => table row.1 right row.2)) pos

/-- Native lane-major aggregation over the unencoded table. -/
def response (weights : Fin b → (Left × Fin b) → F) (table : Left → Fin size → Fin b → F) :
    Fin b → Fin size → F :=
  fun lane right => ∑ row, weights lane row * table row.1 right row.2

/-- Encoded honest responses agree with the committed row combinations everywhere. -/
theorem encoded_response (domain : Position → F)
    (weights : Fin b → (Left × Fin b) → F) (table : Left → Fin size → Fin b → F) (lane : Fin b) :
    MatrixOpeningSecurity.encodeMessages (m := m) domain (response weights table) lane =
      StructuredOpening.combine (weights lane) (encodedTable (m := m) domain table) := by
  unfold MatrixOpeningSecurity.encodeMessages response
  rw [ResponseCoefficients.padded_aggregate, ResponseCoefficients.encode_aggregate]
  rfl

/-- Every sampled native coordinate check passes for honest responses. -/
theorem checks (domain : Position → F) (weights : Fin b → (Left × Fin b) → F)
    (table : Left → Fin size → Fin b → F) {queries : ℕ} (draw : Fin queries → Position) :
    MatrixOpeningSecurity.Checks (m := m) domain (encodedTable (m := m) domain table)
      weights (response weights table) draw := by
  intro lane i
  rw [encoded_response]

/-- The structured message family is exactly the left matrix aggregation. -/
theorem structured_response (left : Left → Matrix (Fin b) (Fin b) F)
    (table : Left → Fin size → Fin b → F) :
    (fun right lane => response (MatrixResponse.weights left) table lane right) =
      leftResponse left table := by
  classical
  funext right lane
  simp only [response, MatrixResponse.weights, Fintype.sum_prod_type,
    leftResponse, Matrix.mulVec, dotProduct, Finset.sum_apply]

/-- Honest native finishing gives the claimed ordered matrix evaluation. -/
theorem finish (left : Left → Matrix (Fin b) (Fin b) F)
    (right : Fin size → Matrix (Fin b) (Fin b) F) (table : Left → Fin size → Fin b → F) :
    MatrixResponse.finishMessage right (response (MatrixResponse.weights left) table) =
      matrixEvaluation left right table := by
  have equal : MatrixResponse.finishMessage right (response (MatrixResponse.weights left) table) =
      foldedOpening left right table := by
    classical
    unfold MatrixResponse.finishMessage foldedOpening
    apply Finset.sum_congr rfl
    intro r _
    rw [congrFun (structured_response left table) r]
  exact equal.trans (foldedOpening_eq_matrixEvaluation left right table)

/-- The common-source extractor returns the honest table under the same
strict unique-decoding margin used by the opening argument. -/
theorem extract [Fintype Position] [DecidableEq F] [NeZero b]
    (domain : Position ↪ F) (enough : m ≤ Fintype.card Position) (capacity : size ≤ m * b)
    (radius : ℕ) (margin : 2 * radius <
      Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)))
    (table : Left → Fin size → Fin b → F) :
    MatrixOpeningSecurity.extract domain capacity radius (encodedTable (m := m) domain table) = table := by
  classical
  unfold MatrixOpeningSecurity.extract
  have coded : CommonSource.RowsIn (BlockCode.code domain m b) (encodedTable (m := m) domain table) :=
    fun row => BlockEncoder.encode_mem_code domain
      (RowLayout.padded (m := m) (fun right => table row.1 right row.2))
  have decoded : CommonSource.decode (BlockCode.code domain m b) radius
      (encodedTable (m := m) domain table) = encodedTable (m := m) domain table :=
    CommonSource.decode_eq_of_nearby (BlockCode.code domain m b) radius margin
      (encodedTable (m := m) domain table) (encodedTable (m := m) domain table) coded
      (by simp only [hammingDist_self, Nat.zero_le])
  rw [decoded]
  exact MatrixResponse.extractTable_encoded domain enough capacity table

end

end FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness
