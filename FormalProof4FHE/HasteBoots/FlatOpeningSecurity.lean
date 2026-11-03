module

public import FormalProof4FHE.HasteBoots.MatrixOpeningSecurity
public import FormalProof4FHE.HasteBoots.MatrixQuerySplit

@[expose] public section

/-!
# Opening security for the complete native flat matrix query

Both the supplied structured response and the extracted full table are now
evaluated by adjacent-cell folds in variable order. Prefix/suffix splitting
uses the native low-prefix address, so no abstract matrix-evaluation premise
is supplied by the prover. Authentication and transcript/implementation
refinement remain separate.
-/

open ProbabilityTheory Matrix

namespace FormalProof4FHE.HasteBoots.FlatOpeningSecurity

noncomputable section

variable {F K Position : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq F] [DecidableEq K]
  [Fintype Position] [DecidableEq Position] {m b : ℕ}

/-- The same query-independent common table, indexed in native flat cell order.
It depends on the split lengths, not on any challenge matrix values. -/
def extract (domain : Position ↪ F)
    (front suffix : List (MatrixFold.Pair (F := F) (Lane := Fin b)))
    (capacity : 2 ^ suffix.length ≤ m * b) (radius : ℕ)
    (word : Position → (Fin (2 ^ front.length) × Fin b) → Fin b → F)
    (cell : Fin (2 ^ (front ++ suffix).length)) : Fin b → F :=
  let pair := (MatrixQuerySplit.join front suffix).symm cell
  MatrixOpeningSecurity.extract domain capacity radius word pair.1 pair.2

omit [Fintype F] [DecidableEq Position] in
/-- Complete-query evaluation of the flat extraction matches the already
proved two-half evaluation, using the exact native address bijection. -/
theorem evaluation_extract (domain : Position ↪ F)
    (front suffix : List (MatrixFold.Pair (F := F) (Lane := Fin b)))
    (capacity : 2 ^ suffix.length ≤ m * b) (radius : ℕ)
    (word : Position → (Fin (2 ^ front.length) × Fin b) → Fin b → F) :
    FlatMatrixFold.foldAll (front ++ suffix) (extract domain front suffix capacity radius word) =
      matrixEvaluation (FlatMatrixFold.weights front) (FlatMatrixFold.weights suffix)
        (MatrixOpeningSecurity.extract domain capacity radius word) := by
  rw [MatrixQuerySplit.foldAll_eq_split]
  congr 1
  funext left right
  simp only [extract, Equiv.symm_apply_apply]

/-- Native-flat fixed-word soundness. The verifier folds supplied lane-major
structured messages through the suffix query; the false claim is measured
against the complete query folded over one common extracted flat table. -/
theorem fixedWord_bound [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K) (domain : Position ↪ F)
    (front suffix : List (MatrixFold.Pair (F := F) (Lane := Fin b)))
    (enough : m ≤ Fintype.card Position) (capacity : 2 ^ suffix.length ≤ m * b)
    (radius queries : ℕ)
    (word : Position → (Fin (2 ^ front.length) × Fin b) → Fin b → F)
    (testResponse structuredResponse :
      (Fin b → (Fin (2 ^ front.length) × Fin b) → F) → Fin b → Fin (2 ^ suffix.length) → F)
    [SampleableType (Fin b → (Fin (2 ^ front.length) × Fin b) → F)]
    [SampleableType ((Fin (2 ^ front.length) × Fin b) → K)]
    [SampleableType (Fin queries → Position)]
    [SampleableType (Matrix.rowSpan (BaseMatrixProximity.stack basis word))]
    [SampleableType (RowSpanSampling.toSpan (BaseMatrixProximity.stack basis word)).toAddMonoidHom.ker]
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ℚ≥0) / 3) :
    Pr{let pair ← CommonSourceOpening.experiment (F := F)
        (Row := Fin (2 ^ front.length) × Fin b) (Position := Position) b queries}[
      FlatMatrixFold.foldAll suffix (fun cell lane => structuredResponse pair.1 lane cell) ≠
        FlatMatrixFold.foldAll (front ++ suffix) (extract domain front suffix capacity radius word) ∧
      MatrixOpeningSecurity.Checks (m := m) domain word pair.1 (testResponse pair.1) pair.2 ∧
      MatrixOpeningSecurity.Checks (m := m) domain word (MatrixResponse.weights (FlatMatrixFold.weights front))
        (structuredResponse pair.1) pair.2] ≤
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m :
        Set (Position → K)) : ENNReal) / (Fintype.card F ^ b) +
      max (ColumnOpening.missBound Position queries
        (Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)) - radius))
        (ColumnOpening.missBound Position queries (radius + 1)) := by
  have bound := MatrixOpeningSecurity.fixedWord_bound basis domain enough capacity radius queries word
    (FlatMatrixFold.weights front) (FlatMatrixFold.weights suffix) testResponse structuredResponse small
  rw [← evaluation_extract domain front suffix capacity radius word] at bound
  simpa only [FlatMatrixFold.finishMessage_eq_fold] using bound

end

end FormalProof4FHE.HasteBoots.FlatOpeningSecurity
