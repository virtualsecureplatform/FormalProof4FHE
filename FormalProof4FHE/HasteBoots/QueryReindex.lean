module

public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout

@[expose] public section

/-!
# Dimension transport without changing queries or sources

ZeroCheck has one special variable followed by n ordinary variables. PCS fixes
its independent front/suffix split. Equality of the total dimensions reindexes
both the returned query and the fixed source; it does not select a new source.
-/

namespace FormalProof4FHE.HasteBoots.QueryReindex

variable {F : Type} [Field F] {k n m : ℕ}

def query (equal : n = m) (q : PackedSumcheckSubclaim.Query F k n) : PackedSumcheckSubclaim.Query F k m :=
  equal ▸ q

def source (equal : n = m) (table : MatrixFold.Cube m → Fin k → F) : MatrixFold.Cube n → Fin k → F :=
  fun cell => table (equal ▸ cell)

/-- Simultaneous transport preserves evaluation and the ordered matrix list. -/
theorem fold (equal : n = m) (q : PackedSumcheckSubclaim.Query F k n)
    (table : MatrixFold.Cube m → Fin k → F) :
    q.fold (source equal table) = (query equal q).fold table := by
  cases equal
  rfl

omit [Field F] in
theorem toList (equal : n = m) (q : PackedSumcheckSubclaim.Query F k n) :
    (query equal q).toList = q.toList := by
  cases equal
  rfl

end FormalProof4FHE.HasteBoots.QueryReindex
