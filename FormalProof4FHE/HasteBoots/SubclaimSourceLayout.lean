module

public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
public import FormalProof4FHE.HasteBoots.MatrixQuerySplit
public import FormalProof4FHE.HasteBoots.MatrixOpeningSecurity

@[expose] public section

/-!
# One decoded source for every returned query

Source layout depends only on the trusted front/suffix dimensions. In
particular, converting a returned sumcheck query to PCS weights does not
select a new source. Front coordinates occupy the low native address bits.
This is a deterministic bridge; it makes no new authentication claim.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.SubclaimSourceLayout

variable {F : Type} [Field F] {k front suffix : ℕ}

/-- Total native-address lookup, with zero beyond the trusted table extent. -/
def lookup (table : Fin (2 ^ front) → Fin (2 ^ suffix) → Fin k → F)
    (position : ℕ) : Fin k → F :=
  if bound : position / 2 ^ front < 2 ^ suffix then
    table ⟨position % 2 ^ front, Nat.mod_lt _ (by positivity)⟩
      ⟨position / 2 ^ front, bound⟩
  else 0

theorem lookup_join (table : Fin (2 ^ front) → Fin (2 ^ suffix) → Fin k → F)
    (left : Fin (2 ^ front)) (right : Fin (2 ^ suffix)) :
    lookup table (left.val + 2 ^ front * right.val) = table left right := by
  have quotient : (left.val + 2 ^ front * right.val) / 2 ^ front = right.val := by
    rw [Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt left.isLt, Nat.zero_add]
  have remainder : (left.val + 2 ^ front * right.val) % 2 ^ front = left.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt left.isLt]
  simp only [lookup, quotient, right.isLt, dite_eq_left, remainder]

/-- The source is fixed without receiving any matrix query. -/
def source (table : Fin (2 ^ front) → Fin (2 ^ suffix) → Fin k → F) :
    MatrixFold.Cube (front + suffix) → Fin k → F :=
  fun cell => lookup table (FlatMatrixFold.index (front + suffix) cell).val

/-- Indexed subclaims preserve every native address when projected to lists. -/
theorem fold_lookup {n : ℕ} (query : PackedSumcheckSubclaim.Query F k n)
    (word : ℕ → Fin k → F) :
    query.fold (fun cell => word (FlatMatrixFold.index n cell).val) =
      FlatMatrixFold.foldAll query.toList (fun position => word position.val) := by
  rw [query.fold_eq_list, FlatMatrixFold.foldAll_eq_cube]
  congr 1
  funext cell
  have address := query.index_cubeEquiv (query.cubeEquiv.symm cell)
  simpa only [Equiv.apply_symm_apply] using congrArg word address.symm

omit [Field F] in
/-- Both half lengths are fixed by the trusted PCS dimensions. -/
theorem front_length (query : PackedSumcheckSubclaim.Query F k (front + suffix)) :
    (query.toList.take front).length = front := by
  simp only [List.length_take, query.length_toList]
  omega

omit [Field F] in
theorem suffix_length (query : PackedSumcheckSubclaim.Query F k (front + suffix)) :
    (query.toList.drop front).length = suffix := by
  simp only [List.length_drop, query.length_toList]
  omega

/-- Front weights reindexed onto the fixed low-address coordinate type. -/
def leftWeights (query : PackedSumcheckSubclaim.Query F k (front + suffix))
    (left : Fin (2 ^ front)) : Matrix (Fin k) (Fin k) F :=
  FlatMatrixFold.weights (query.toList.take front)
    ((finCongr (congrArg (2 ^ ·) (front_length query))).symm left)

/-- Suffix weights act after the front weights, by left multiplication. -/
def rightWeights (query : PackedSumcheckSubclaim.Query F k (front + suffix))
    (right : Fin (2 ^ suffix)) : Matrix (Fin k) (Fin k) F :=
  FlatMatrixFold.weights (query.toList.drop front)
    ((finCongr (congrArg (2 ^ ·) (suffix_length query))).symm right)

/-- Every returned query evaluates the same fixed table in native split order. -/
theorem fold_source (query : PackedSumcheckSubclaim.Query F k (front + suffix))
    (table : Fin (2 ^ front) → Fin (2 ^ suffix) → Fin k → F) :
    query.fold (source table) =
      matrixEvaluation (leftWeights query) (rightWeights query) table := by
  unfold source
  rw [fold_lookup]
  let first := query.toList.take front
  let last := query.toList.drop front
  have appended : first ++ last = query.toList := List.take_append_drop _ _
  have split := MatrixQuerySplit.foldAll_eq_split first last
    (fun position => lookup table position.val)
  have joinedFold := congrArg
    (fun pairs => FlatMatrixFold.foldAll pairs (fun position => lookup table position.val)) appended.symm
  rw [joinedFold, split]
  unfold matrixEvaluation
  let leftEquiv := finCongr (congrArg (2 ^ ·) (front_length query))
  let rightEquiv := finCongr (congrArg (2 ^ ·) (suffix_length query))
  rw [← rightEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro right _
  rw [← leftEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro left _
  have address : lookup table (MatrixQuerySplit.join first last (left, right)).val =
      table (leftEquiv left) (rightEquiv right) := by
    rw [MatrixQuerySplit.join_val]
    change lookup table (left.val + 2 ^ first.length * right.val) = _
    have lengthFirst : first.length = front := front_length query
    calc
      _ = lookup table ((leftEquiv left).val + 2 ^ front * (rightEquiv right).val) := by
        apply congrArg (lookup table)
        exact congrArg (fun power : ℕ => left.val + power * right.val) (congrArg (2 ^ ·) lengthFirst)
      _ = _ := lookup_join table (leftEquiv left) (rightEquiv right)
  dsimp only
  rw [address]
  simp only [leftWeights, rightWeights, leftEquiv, rightEquiv, Equiv.symm_apply_apply]
  rfl

section Decoding

noncomputable section

variable {Position : Type} [Fintype Position] [DecidableEq F]
  {m : ℕ}

/-- Decode once using only the frozen word, code and trusted layout dimensions. -/
def decodedSource (domain : Position ↪ F) (capacity : 2 ^ suffix ≤ m * k) (radius : ℕ)
    (word : Position → (Fin (2 ^ front) × Fin k) → Fin k → F) :
    MatrixFold.Cube (front + suffix) → Fin k → F :=
  source (MatrixOpeningSecurity.extract domain capacity radius word)

/-- The exact common-source decoder used by PCS discharges the source-fold
geometry for any query returned later by sumcheck. -/
theorem fold_decodedSource (domain : Position ↪ F) (capacity : 2 ^ suffix ≤ m * k) (radius : ℕ)
    (word : Position → (Fin (2 ^ front) × Fin k) → Fin k → F)
    (query : PackedSumcheckSubclaim.Query F k (front + suffix)) :
    query.fold (decodedSource domain capacity radius word) =
      matrixEvaluation (leftWeights query) (rightWeights query)
        (MatrixOpeningSecurity.extract domain capacity radius word) :=
  fold_source query _

/-- A wrong terminal factor finished from native messages is exactly the
incorrect-evaluation event in PCS, for the same fixed decoded source. -/
theorem wrong_finish_iff (domain : Position ↪ F) (capacity : 2 ^ suffix ≤ m * k) (radius : ℕ)
    (word : Position → (Fin (2 ^ front) × Fin k) → Fin k → F)
    (query : PackedSumcheckSubclaim.Query F k (front + suffix))
    (messages : Fin k → Fin (2 ^ suffix) → F) :
    MatrixResponse.finishMessage (rightWeights query) messages ≠
        query.fold (decodedSource domain capacity radius word) ↔
      MatrixResponse.finishMessage (rightWeights query) messages ≠
        matrixEvaluation (leftWeights query) (rightWeights query)
          (MatrixOpeningSecurity.extract domain capacity radius word) := by
  rw [fold_decodedSource]

end

end Decoding

end FormalProof4FHE.HasteBoots.SubclaimSourceLayout
