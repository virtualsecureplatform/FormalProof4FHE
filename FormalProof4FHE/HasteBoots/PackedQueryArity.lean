module

public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

@[expose] public section

/-!
# Dimension equality without a new query or source view

A trusted tensor split may express the same variable count differently.
Transport preserves the ordered matrices and native Boolean coordinates.
It changes only the dimension proof, not the original root or packed lanes.
-/

namespace FormalProof4FHE.HasteBoots.PackedQueryArity

variable {F : Type} {width n m : ℕ}

def query (same : n = m) (original : PackedSumcheckSubclaim.Query F width n) :
    PackedSumcheckSubclaim.Query F width m := same ▸ original

def table (same : n = m) (original : MatrixFold.Cube m → Fin width → F) :
    MatrixFold.Cube n → Fin width → F := fun cell => original (same ▸ cell)

theorem toList (same : n = m) (original : PackedSumcheckSubclaim.Query F width n) :
    (query same original).toList = original.toList := by cases same; rfl

theorem fold [Field F] (same : n = m) (original : PackedSumcheckSubclaim.Query F width n)
    (source : MatrixFold.Cube m → Fin width → F) :
    (query same original).fold source = original.fold (table same source) := by cases same; rfl

end FormalProof4FHE.HasteBoots.PackedQueryArity
