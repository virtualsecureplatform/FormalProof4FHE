module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.Dedup

@[expose] public section

/-!
# Ordered column draws and transport deduplication

Schedule 5 draws Q columns WITH replacement, then sorts and deduplicates for
authentication. The sample space has Q independent coordinates even if fewer
than Q distinct columns are sent. These counting facts do not assert freshness
of the Fiat--Shamir stream; that remains a separate theorem.
-/

namespace FormalProof4FHE.HasteBoots.ColumnSampling

variable {Position : Type*} [DecidableEq Position]

/-- Deduplication preserves the event of missing every bad column. -/
theorem misses_dedup_iff (samples : List Position) (bad : Set Position) :
    (∀ p ∈ samples.dedup, p ∉ bad) ↔ (∀ p ∈ samples, p ∉ bad) := by
  simp only [List.mem_dedup]

/-- Ordered length-Q outcomes that land entirely in the designated good columns. -/
def goodDrawsEquiv (good : Finset Position) (queries : ℕ) :
    {draw : Fin queries → Position // ∀ i, draw i ∈ good} ≃
      (Fin queries → {p : Position // p ∈ good}) where
  toFun draw i := ⟨draw.1 i, draw.2 i⟩
  invFun draw := ⟨fun i => (draw i).1, fun i => (draw i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exponent is the ordered quota, not the number of distinct transmitted columns. -/
theorem card_goodDraws [Fintype Position] (good : Finset Position) (queries : ℕ) :
    Fintype.card {draw : Fin queries → Position // ∀ i, draw i ∈ good} =
      good.card ^ queries := by
  classical
  rw [Fintype.card_congr (goodDrawsEquiv good queries)]
  simp

end FormalProof4FHE.HasteBoots.ColumnSampling
