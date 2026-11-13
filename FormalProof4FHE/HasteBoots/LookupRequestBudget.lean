module
public import FormalProof4FHE.HasteBoots.RequestLookupPairMiddle
@[expose] public section

/-! Public row-count bounds give a uniform request-pair error budget, including
partially active requests. There is no union factor over request indices. -/
namespace FormalProof4FHE.HasteBoots.LookupRequestBudget
noncomputable section

theorem tuple_error_mono (q width left right size : ℕ) (bound : left ≤ right) :
    TupleLookupPair.error q width left size ≤ TupleLookupPair.error q width right size := by
  unfold TupleLookupPair.error
  gcongr

theorem error_budget_mono {requests : ℕ} (q : ℕ)
    (widths sizes left right repetitions : Fin requests → ℕ) (bound : ∀ index, left index ≤ right index) :
    RequestLookupPairMiddle.errorBudget q widths sizes left repetitions ≤
      RequestLookupPairMiddle.errorBudget q widths sizes right repetitions := by
  unfold RequestLookupPairMiddle.errorBudget
  apply Finset.sup_le
  intro index member
  refine le_trans ?_ (Finset.le_sup (f := fun index => TupleLookupPair.error q (widths index) (right index) (sizes index)^repetitions index) member)
  have single := tuple_error_mono q (widths index) (left index) (right index) (sizes index) (bound index)
  gcongr

theorem logical_shape_bound {requests : ℕ} (q logical : ℕ)
    (widths sizes active inactive repetitions : Fin requests → ℕ)
    (shape : ∀ index, active index + inactive index = 2^logical) :
    RequestLookupPairMiddle.errorBudget q widths sizes active repetitions ≤
      RequestLookupPairMiddle.errorBudget q widths sizes (fun _ => 2^logical) repetitions := by
  apply error_budget_mono
  intro index
  have sized := shape index
  omega

end
end FormalProof4FHE.HasteBoots.LookupRequestBudget
