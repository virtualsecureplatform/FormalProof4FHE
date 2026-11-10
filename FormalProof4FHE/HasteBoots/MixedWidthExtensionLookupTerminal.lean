module
public import FormalProof4FHE.HasteBoots.ExtensionLookupTerminal
@[expose] public section

/-! Original source decoding and original helper decoding have independent
physical widths. No helper commitment or padded helper payload is introduced. -/
namespace FormalProof4FHE.HasteBoots.MixedWidthExtensionLookupTerminal
open scoped BigOperators Classical
open ExtensionLookupTerminal (sourceQuery sourceTruth source_evaluate)
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row sourceCount : ℕ}

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
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (sourceClaims : Fin sourceCount → Fin (d + padding) → F) (helperClaim : Fin (d + helperPadding) → F)
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
end FormalProof4FHE.HasteBoots.MixedWidthExtensionLookupTerminal
