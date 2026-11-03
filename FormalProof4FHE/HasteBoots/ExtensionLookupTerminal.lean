module

public import FormalProof4FHE.HasteBoots.ExtensionLookupIdentity
public import FormalProof4FHE.HasteBoots.ExtensionSourceOpening

@[expose] public section

/-!
# Native lookup terminal checking and original base-field obligations

The full point has low lane coordinates followed by row coordinates. Source
claims use the scalar query on their original roots; helper claims use the
coefficient query on the helper root. Successful local decoding and the literal
terminal equality force either the truthful factor expression or a false
original base-field opening. Tuple width, packing width, lookup basis degree
and row count remain distinct. This is the deterministic acceptance adapter;
complete shared sumcheck/batch-opening and transcript composition remains open.
-/

open scoped BigOperators Classical

namespace FormalProof4FHE.HasteBoots.ExtensionLookupTerminal

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d padding c row sourceCount : ℕ}

def sourceQuery (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (point : Fin (c + row) → K) : ExtensionQuery.Broadcast F (d + padding) row :=
  ExtensionQuery.scalarQuery basis
    (ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes shape) (fun i => point (i.castAdd row))) row
    (fun i => point (Fin.natAdd c i))

def sourceTruth (shape : d + padding = 2 ^ c) (point : Fin (c + row) → K)
    (table : MatrixFold.Cube row → Fin (d + padding) → F) : K :=
  ExtensionQuery.evaluate row (fun i => point (Fin.natAdd c i))
    (fun cell => ExtensionQuery.laneValue
      (ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes shape) (fun i => point (i.castAdd row))) (table cell))

theorem source_evaluate (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (point : Fin (c + row) → K) (table : MatrixFold.Cube row → Fin (d + padding) → F) :
    (sourceQuery basis shape point).evaluate table = PaddedExtension.encode basis (sourceTruth shape point table) :=
  ExtensionQuery.scalar_evaluate _ _ _ _

/-- This identity fixes native low-lane/high-row point order explicitly. -/
theorem source_tensor (shape : d + padding = 2 ^ c) (point : Fin (c + row) → K)
    (table : MatrixFold.Cube row → Fin (d + padding) → F) :
    sourceTruth shape point table = ∑ cell, PackedEqualityCube.weight (fun i => point (Fin.natAdd c i)) cell *
      ∑ lane, PackedEqualityCube.weight (fun i => point (i.castAdd row)) (ExtensionQuery.nativeLanes shape lane) *
        algebraMap F K (table cell lane) := by
  rw [sourceTruth, ExtensionQuery.evaluate_eq_sum]
  simp only [ExtensionQuery.laneValue_algebraMap, ExtensionQuery.laneWeights]

private theorem decoded_truth {n : ℕ} (basis : Module.Basis (Fin d) F K)
    (query : ExtensionQuery.Broadcast F (d + padding) n) (table : MatrixFold.Cube n → Fin (d + padding) → F)
    (truth value : K) (claim : Fin (d + padding) → F)
    (semantics : query.evaluate table = PaddedExtension.encode basis truth)
    (decoded : PaddedExtension.element basis (query.finish claim) = some value)
    (correct : claim = query.query.fold table) : value = truth := by
  rw [correct, ← ExtensionQuery.Broadcast.evaluate, semantics, PaddedExtension.element_encode] at decoded
  exact Option.some.inj decoded.symm

/-- The local check reads supplied vectors and computed public factors only.
If it accepts, an incorrect factor expression exposes a wrong original root
opening; no new projected source or extension PCS assumption is introduced. -/
theorem checked_truthful_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint point : Fin (c + row) → K) (r y : K) (count : ℕ) (enough : count ≤ 2 ^ (c + row))
    (sources : Fin sourceCount → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (sourceClaims : Fin sourceCount → Fin (d + padding) → F) (helperClaim : Fin (d + padding) → F)
    (sourceValues : Fin sourceCount → K) (helperValue expected : K)
    (sourceDecoded : ∀ i, PaddedExtension.element basis ((sourceQuery basis shape point).finish (sourceClaims i)) =
      some (sourceValues i))
    (helperDecoded : PaddedExtension.element basis ((ExtensionQuery.coefficientsQuery basis point).finish helperClaim) =
      some helperValue)
    (checked : ExtensionLookupIdentity.terminal eqPoint point r (∑ i, y ^ i.val * sourceValues i)
      helperValue count enough = expected) :
    expected = ExtensionLookupIdentity.terminal eqPoint point r
      (∑ i, y ^ i.val * sourceTruth shape point (sources i))
      (ExtensionQuery.evaluate (c + row) point (fun cell => PaddedExtension.decode basis (helpers cell))) count enough ∨
      (∃ i, sourceClaims i ≠ (sourceQuery basis shape point).query.fold (sources i)) ∨
      helperClaim ≠ (ExtensionQuery.coefficientsQuery basis point).query.fold helpers := by
  by_cases wrongSource : ∃ i, sourceClaims i ≠ (sourceQuery basis shape point).query.fold (sources i)
  · exact Or.inr (Or.inl wrongSource)
  by_cases wrongHelper : helperClaim ≠ (ExtensionQuery.coefficientsQuery basis point).query.fold helpers
  · exact Or.inr (Or.inr wrongHelper)
  left
  have sourceCorrect (i : Fin sourceCount) : sourceClaims i = (sourceQuery basis shape point).query.fold (sources i) := by
    by_contra bad
    exact wrongSource ⟨i, bad⟩
  have sourceEqual (i : Fin sourceCount) : sourceValues i = sourceTruth shape point (sources i) :=
    decoded_truth basis _ _ _ _ _ (source_evaluate basis shape point (sources i)) (sourceDecoded i) (sourceCorrect i)
  have helperEqual : helperValue =
      ExtensionQuery.evaluate (c + row) point (fun cell => PaddedExtension.decode basis (helpers cell)) :=
    decoded_truth basis _ _ _ _ _ (ExtensionQuery.coefficients_evaluate basis point helpers) helperDecoded (not_not.mp wrongHelper)
  rw [← checked, helperEqual]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun value => y ^ i.val * value) (sourceEqual i))

end

end FormalProof4FHE.HasteBoots.ExtensionLookupTerminal
