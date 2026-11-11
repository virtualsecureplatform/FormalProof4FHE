module
public import FormalProof4FHE.HasteBoots.LookupReceiptQueryMeaning
@[expose] public section

/-! Exact native pair readers and complete cube equality transport terminal
folds across original row and packing-width equalities. -/
namespace FormalProof4FHE.HasteBoots.QueryPairFoldTransport
noncomputable section

theorem pairs_heq {lw rw ln rn : ℕ} (width : lw = rw) (rows : ln = rn)
    (raw : List NativeGoldCoefficientsQuery.Pair)
    (left : PackedSumcheckSubclaim.Query NativeFields.Goldilocks lw ln)
    (right : PackedSumcheckSubclaim.Query NativeFields.Goldilocks rw rn)
    (leftRead : NativeGoldCoefficientsQuery.readPairs lw ln raw = some left)
    (rightRead : NativeGoldCoefficientsQuery.readPairs rw rn raw = some right) : HEq left right := by
  subst rw
  subst rn
  exact heq_of_eq (Option.some.inj (leftRead.symm.trans rightRead))

theorem fold_list {lw rw ln rn : ℕ} (width : lw = rw) (rows : ln = rn)
    (left : PackedSumcheckSubclaim.Query NativeFields.Goldilocks lw ln)
    (right : PackedSumcheckSubclaim.Query NativeFields.Goldilocks rw rn)
    (lt : MatrixFold.Cube ln → Fin lw → NativeFields.Goldilocks)
    (rt : MatrixFold.Cube rn → Fin rw → NativeFields.Goldilocks)
    (query : HEq left right) (table : HEq lt rt) : List.ofFn (left.fold lt) = List.ofFn (right.fold rt) := by
  subst rw
  subst rn
  cases query
  cases table
  rfl

end
end FormalProof4FHE.HasteBoots.QueryPairFoldTransport
