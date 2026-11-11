module
import FormalProof4FHE.HasteBoots.LookupConsumedTrace

namespace FormalProof4FHE.HasteBoots.ConsumedReplaySmoke

/-- Rejected candidates remain in the trace while accepted coefficients keep
chronological order. The candidate mask also ignores unused high bits. -/
example : FieldConsumedReplay.values 3 [[3],[2],[255],[1],[0]] = [2,1,0] := by
  decide +kernel

/-- Fixed-width chunking is unique even when candidates are rejected. -/
example : ∀ right : List InputIndexedOracle.Input,
    (∀ chunk ∈ right, chunk.length = 1) →
    right.flatten = [3,2,255,1,0] →
    right = [[3],[2],[255],[1],[0]] := by
  intro right widths same
  exact FieldConsumedReplay.chunks_unique 1 (by decide) right _ widths
    (by simp) same

/-- The positive-width premise matters: empty chunks have the same payload. -/
example : ([] : List InputIndexedOracle.Input).flatten = [[],[]].flatten ∧
    ([] : List InputIndexedOracle.Input) ≠ [[],[]] := by decide

end FormalProof4FHE.HasteBoots.ConsumedReplaySmoke
