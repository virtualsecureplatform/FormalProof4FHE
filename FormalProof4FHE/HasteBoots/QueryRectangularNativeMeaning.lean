module
public import FormalProof4FHE.HasteBoots.SingleOpeningFixedResponseData
public import FormalProof4FHE.HasteBoots.NativeGoldQueryProjection
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout
@[expose] public section

/-! Successful native interpretation uses the exact ordered matrix list and
public front/suffix layout of the rectangular PCS evaluation. Source layout
is independent of the query and does not require honest or padded contents. -/
namespace FormalProof4FHE.HasteBoots.QueryRectangularNativeMeaning
open NativeFields (Goldilocks)
open NativeGoldCoefficientsQuery (readMatrix readPairs interpret)
open NativeGoldPackedMeaning (pairValue)
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativeGoldPcsWire (Query)
open scoped BigOperators Matrix
noncomputable section

theorem matrix_value (width : ℕ) (raw : NativeGoldMatrix.Matrix)
    (value : Matrix (Fin width) (Fin width) Goldilocks) (read : readMatrix width raw = some value) :
    NativeGoldMatrixWeights.value width raw = value := by
  unfold readMatrix at read
  split at read
  next valid =>
    rw [NativeGoldMatrixWeights.value_checked width raw valid]
    exact Option.some.inj read
  next invalid => contradiction

theorem pairs_list (width n : ℕ) (raw : List NativeGoldCoefficientsQuery.Pair)
    (query : PackedSumcheckSubclaim.Query Goldilocks width n) (read : readPairs width n raw = some query) :
    query.toList = raw.map (pairValue width) := by
  induction n generalizing raw with
  | zero =>
    cases raw with
    | nil => cases Option.some.inj read; rfl
    | cons head tail => contradiction
  | succ n ih =>
    cases raw with
    | nil => contradiction
    | cons head tail =>
      simp only [readPairs,Option.bind_eq_some_iff,Option.map_eq_some_iff] at read
      obtain ⟨zero,zeroRead,one,oneRead,rest,restRead,same⟩ := read
      subst query
      simp only [PackedSumcheckSubclaim.Query.toList,List.map_cons]
      refine congrArg₂ List.cons ?_ (ih tail rest restRead)
      funext bit
      cases bit
      · exact (matrix_value width head.zero zero zeroRead).symm
      · exact (matrix_value width head.one one oneRead).symm

theorem interpreted_list (width n : ℕ) (raw : NativeGoldCoefficientsQuery.Query)
    (query : ExtensionQuery.Broadcast Goldilocks width n) (read : interpret width n raw = some query) :
    query.query.toList = raw.pairs.map (pairValue width) := by
  simp only [interpret,Option.bind_eq_some_iff,Option.map_eq_some_iff] at read
  obtain ⟨pairs,pairsRead,post,_,same⟩ := read
  subst query
  exact pairs_list width n raw.pairs pairs pairsRead

variable (parameters : Parameters Stored) (raw : Query) (back : ℕ)
    (query : ExtensionQuery.Broadcast Goldilocks parameters.width.val (parameters.leftVariables.val + back))
    (read : interpret parameters.width.val (parameters.leftVariables.val + back) ⟨raw.models,none⟩ = some query)

include read

theorem left_weights : SingleOpeningFixedResponseData.left parameters raw = SubclaimSourceLayout.leftWeights query.query := by
  have lists := interpreted_list _ _ _ _ read
  change query.query.toList = raw.models.map (pairValue parameters.width.val) at lists
  have halves : query.query.toList.take parameters.leftVariables.val =
      (raw.models.take parameters.leftVariables.val).map (pairValue parameters.width.val) := by
    rw [lists,← List.map_take]
  funext cell
  let weightAt := fun pairs : List (MatrixFold.Pair (F := Goldilocks) (Lane := Fin parameters.width.val)) =>
    FlatMatrixFold.weights pairs ⟨cell.val % 2^pairs.length,Nat.mod_lt _ (by positivity)⟩
  have moved := congrArg weightAt halves.symm
  change weightAt ((raw.models.take parameters.leftVariables.val).map (pairValue parameters.width.val)) = _
  apply moved.trans
  unfold weightAt SubclaimSourceLayout.leftWeights
  apply congrArg (FlatMatrixFold.weights _)
  apply Fin.ext
  simp only [finCongr_symm,finCongr_apply,Fin.val_cast]
  rw [SubclaimSourceLayout.front_length query.query]
  exact Nat.mod_eq_of_lt cell.isLt

theorem right_weights (length : parameters.code.messageLength.val = 2^back) :
    (fun index : Fin (2^back) => SingleOpeningFixedResponseData.right parameters raw (Fin.cast length.symm index)) =
      SubclaimSourceLayout.rightWeights query.query := by
  have lists := interpreted_list _ _ _ _ read
  change query.query.toList = raw.models.map (pairValue parameters.width.val) at lists
  have halves : query.query.toList.drop parameters.leftVariables.val = NativeGoldSuffixFinishing.suffix parameters raw := by
    rw [lists,← List.map_drop]; rfl
  funext index
  let weightAt := fun pairs : List (MatrixFold.Pair (F := Goldilocks) (Lane := Fin parameters.width.val)) =>
    FlatMatrixFold.weights pairs ⟨index.val % 2^pairs.length,Nat.mod_lt _ (by positivity)⟩
  have moved := congrArg weightAt halves.symm
  change weightAt (NativeGoldSuffixFinishing.suffix parameters raw) = _
  apply moved.trans
  unfold weightAt SubclaimSourceLayout.rightWeights
  apply congrArg (FlatMatrixFold.weights _)
  apply Fin.ext
  simp only [finCongr_symm,finCongr_apply,Fin.val_cast]
  rw [SubclaimSourceLayout.suffix_length query.query]
  exact Nat.mod_eq_of_lt index.isLt

omit read in
/-- The cube source is fixed by public dimensions and the same extracted
rectangular table, with no dependence on the opening query. -/
def source (length : parameters.code.messageLength.val = 2^back)
    (table : Fin (2^parameters.leftVariables.val) → Fin parameters.code.messageLength.val → Fin parameters.width.val → Goldilocks) :
    MatrixFold.Cube (parameters.leftVariables.val + back) → Fin parameters.width.val → Goldilocks :=
  SubclaimSourceLayout.source (fun left right => table left (Fin.cast length.symm right))

theorem fold_source (length : parameters.code.messageLength.val = 2^back)
    (table : Fin (2^parameters.leftVariables.val) → Fin parameters.code.messageLength.val → Fin parameters.width.val → Goldilocks) :
    query.query.fold (source parameters back length table) =
      matrixEvaluation (SingleOpeningFixedResponseData.left parameters raw) (SingleOpeningFixedResponseData.right parameters raw) table := by
  have folded := SubclaimSourceLayout.fold_source query.query (fun left right => table left (Fin.cast length.symm right))
  rw [← left_weights parameters raw back query read,← right_weights parameters raw back query read length] at folded
  change query.query.fold (source parameters back length table) = _ at folded
  rw [folded]
  unfold matrixEvaluation
  exact (finCongr length.symm).sum_comp (fun index => ∑ left,
    (SingleOpeningFixedResponseData.right parameters raw index * SingleOpeningFixedResponseData.left parameters raw left) *ᵥ table left index)

end
end FormalProof4FHE.HasteBoots.QueryRectangularNativeMeaning
