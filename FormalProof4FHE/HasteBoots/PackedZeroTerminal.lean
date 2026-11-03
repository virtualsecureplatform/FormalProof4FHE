module

public import FormalProof4FHE.HasteBoots.PackedZeroCube

@[expose] public section

/-!
# Typed ZeroCheck terminal checking with a public equality value

Only the original factor vectors require commitment authentication. The
additional EQ factor is computed by the verifier's ordered matrix recurrence.
The native Boolean terminal identity is exactly the reduced sum-of-products
identity against the same augmented source tables, once the original factor
vectors are their authenticated folds. Cryptographic authentication and the
full shared-oracle run remain composition obligations.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.PackedZeroTerminal

noncomputable section

variable {F Factor Term : Type} [Field F] [DecidableEq F] [Fintype Term] {k : ℕ}

def check (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (factors : Factor → Fin k → F) (equality expected : Fin k → F) : Bool :=
  (List.ofFn fun lane : Fin k => decide
    (PackedSumcheckRound.expression arity coefficient indices (fun factor => factors factor lane) *
      equality lane = expected lane)).all id

theorem check_iff (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (factors : Factor → Fin k → F) (equality expected : Fin k → F) :
    check arity coefficient indices factors equality expected = true ↔
      ∀ lane, PackedSumcheckRound.expression arity coefficient indices (fun factor => factors factor lane) *
        equality lane = expected lane := by
  simp [check, List.mem_ofFn, List.all_eq_true]

def augmentedSource (query : List (MatrixFold.Pair (F := F) (Lane := Fin k)))
    (tables : Factor → MatrixFold.Cube query.length → Fin k → F)
    (points : Fin k → Fin query.length → F) (mixing : Fin k → Fin k → F) :
    (Factor ⊕ Unit) → MatrixFold.Cube query.length → Fin k → F :=
  Sum.elim tables (fun _ => PackedPublicEquality.mixedTable points mixing)

omit [DecidableEq F] in
/-- Computing the EQ terminal agrees with folding the appended source, while
each original factor keeps precisely its own source fold. -/
theorem augmented_folds (query : List (MatrixFold.Pair (F := F) (Lane := Fin k)))
    (tables : Factor → MatrixFold.Cube query.length → Fin k → F)
    (points : Fin k → Fin query.length → F) (mixing : Fin k → Fin k → F) :
    (fun factor => MatrixFold.foldAll query (augmentedSource query tables points mixing factor)) =
      Sum.elim (fun factor => MatrixFold.foldAll query (tables factor))
        (fun _ => PackedPublicEquality.evaluatePublic query points mixing) := by
  funext factor
  cases factor with
  | inl factor => rfl
  | inr tag => exact PackedPublicEquality.fold_eq_evaluatePublic query points mixing

/-- Native terminal acceptance is the reduced relation on these exact folded
sources; the public EQ value does not need a separate commitment opening. -/
theorem check_folds_iff (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (query : List (MatrixFold.Pair (F := F) (Lane := Fin k)))
    (tables : Factor → MatrixFold.Cube query.length → Fin k → F)
    (points : Fin k → Fin query.length → F) (mixing : Fin k → Fin k → F) (expected : Fin k → F) :
    check arity coefficient indices (fun factor => MatrixFold.foldAll query (tables factor))
      (PackedPublicEquality.evaluatePublic query points mixing) expected = true ↔
      (fun lane => PackedSumcheckRound.expression (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices)
          (fun factor => MatrixFold.foldAll query (augmentedSource query tables points mixing factor) lane)) = expected := by
  rw [check_iff]
  have expressions (lane : Fin k) :
      PackedSumcheckRound.expression (fun term => arity term + 1) coefficient
        (PackedZeroFirst.reducedIndices arity indices)
          (fun factor => MatrixFold.foldAll query (augmentedSource query tables points mixing factor) lane) =
        PackedSumcheckRound.expression arity coefficient indices
          (fun factor => MatrixFold.foldAll query (tables factor) lane) *
            PackedPublicEquality.evaluatePublic query points mixing lane := by
    have valuesEq : (fun factor => MatrixFold.foldAll query (augmentedSource query tables points mixing factor) lane) =
        Sum.elim (fun factor => MatrixFold.foldAll query (tables factor) lane)
          (fun _ => PackedPublicEquality.evaluatePublic query points mixing lane) := by
      funext factor
      have folded := congrFun (augmented_folds query tables points mixing) factor
      cases factor <;> exact congrFun folded lane
    rw [valuesEq, PackedZeroFirst.reduced_expression, mul_comm]
  simp only [funext_iff, expressions]

end

end FormalProof4FHE.HasteBoots.PackedZeroTerminal
