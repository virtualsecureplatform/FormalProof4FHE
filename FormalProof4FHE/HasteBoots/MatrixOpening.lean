module

public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Ordered matrix-weighted openings

The deterministic aggregation identity in HasteBoots `pcs/src/matrix_weighted.rs`
and 2025/719, Appendix B.2. The right-half matrix acts AFTER the left-half
matrix. This file proves algebra only: it makes no commitment-security claim.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots

variable {F L R Lane : Type*} [Semiring F]
  [Fintype L] [Fintype R] [Fintype Lane]

/-- Prover response for one right-half index, before the verifier's final fold. -/
def leftResponse (left : L → Matrix Lane Lane F) (table : L → R → Lane → F)
    (r : R) : Lane → F :=
  ∑ l, left l *ᵥ table l r

/-- The verifier folds the supplied left aggregation using the right weights. -/
def foldedOpening (left : L → Matrix Lane Lane F)
    (right : R → Matrix Lane Lane F) (table : L → R → Lane → F) : Lane → F :=
  ∑ r, right r *ᵥ leftResponse left table r

/-- The direct matrix-weighted table evaluation. Multiplication order is significant. -/
def matrixEvaluation (left : L → Matrix Lane Lane F)
    (right : R → Matrix Lane Lane F) (table : L → R → Lane → F) : Lane → F :=
  ∑ r, ∑ l, (right r * left l) *ᵥ table l r

/-- Ordered structured openings compute precisely the direct table evaluation. -/
theorem foldedOpening_eq_matrixEvaluation (left : L → Matrix Lane Lane F)
    (right : R → Matrix Lane Lane F) (table : L → R → Lane → F) :
    foldedOpening left right table = matrixEvaluation left right table := by
  classical
  unfold foldedOpening leftResponse matrixEvaluation
  congr 1
  funext r
  simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec]

/-- A terminal claim is about the fixed table only after its response is authenticated. -/
theorem authenticatedResponse_eq_evaluation (left : L → Matrix Lane Lane F)
    (right : R → Matrix Lane Lane F) (table : L → R → Lane → F)
    (response : R → Lane → F) (authenticated : response = leftResponse left table) :
    (∑ r, right r *ᵥ response r) = matrixEvaluation left right table := by
  subst response
  exact foldedOpening_eq_matrixEvaluation left right table

end FormalProof4FHE.HasteBoots
