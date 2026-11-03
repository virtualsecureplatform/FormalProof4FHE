module

public import FormalProof4FHE.HasteBoots.BatchGrouping
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout

@[expose] public section

/-!
# Computed native response groups for indexed matrix queries

Groups compare the actual ordered matrix prefix, not merely its semantic
aggregate. Representatives are the first original queries with those keys.
Each query reuses a response only from the same trusted left prefix; suffix
matrices and terminal values remain query-specific. Rust vector storage and
field equality refinement remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.BatchQueryLayout

noncomputable section

variable {F : Type} [Field F] [DecidableEq F] {b front suffix claims : ℕ}

def keys (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix)) :=
  List.ofFn (fun claim => (query claim).toList.take front)

def position (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (claim : Fin claims) : Fin (keys (front := front) (suffix := suffix) query).length := Fin.cast (by simp [keys]) claim

def groupCount (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix)) : ℕ :=
  (BatchGrouping.compute (keys (front := front) (suffix := suffix) query)).1.length

def groupOf (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (claim : Fin claims) : Fin (groupCount (front := front) (suffix := suffix) query) := BatchGrouping.groupOf (keys (front := front) (suffix := suffix) query) (position (front := front) (suffix := suffix) query claim)

def representative (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (group : Fin (groupCount (front := front) (suffix := suffix) query)) : Fin claims :=
  Fin.cast (by simp [keys]) (BatchGrouping.representative (keys (front := front) (suffix := suffix) query) group)

omit [Field F] [DecidableEq F] in
theorem key_position (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (claim : Fin claims) : (keys (front := front) (suffix := suffix) query).get (position (front := front) (suffix := suffix) query claim) = (query claim).toList.take front := by
  exact (List.get_ofFn (fun index : Fin claims => (query index).toList.take front)
    (position (front := front) (suffix := suffix) query claim)).trans
      (congrArg (fun index : Fin claims => (query index).toList.take front) (Fin.ext rfl))

omit [Field F] in
theorem key_representative (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (group : Fin (groupCount (front := front) (suffix := suffix) query)) :
    (keys (front := front) (suffix := suffix) query).get (BatchGrouping.representative (keys (front := front) (suffix := suffix) query) group) =
      (query (representative (front := front) (suffix := suffix) query group)).toList.take front := by
  exact List.get_ofFn (fun index : Fin claims => (query index).toList.take front)
    (BatchGrouping.representative (keys (front := front) (suffix := suffix) query) group)

omit [Field F] in
theorem groupOf_eq_iff (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (first second : Fin claims) :
    groupOf (front := front) (suffix := suffix) query first = groupOf (front := front) (suffix := suffix) query second ↔ (query first).toList.take front = (query second).toList.take front := by
  change BatchGrouping.groupOf _ _ = BatchGrouping.groupOf _ _ ↔ _
  simpa only [key_position] using
    BatchGrouping.groupOf_eq_iff (keys (front := front) (suffix := suffix) query) (position (front := front) (suffix := suffix) query first) (position (front := front) (suffix := suffix) query second)

omit [Field F] in
theorem representative_prefix (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (claim : Fin claims) :
    (query (representative (front := front) (suffix := suffix) query (groupOf (front := front) (suffix := suffix) query claim))).toList.take front = (query claim).toList.take front := by
  have same := BatchGrouping.representative_group_key
    (keys (front := front) (suffix := suffix) query) (position (front := front) (suffix := suffix) query claim)
  exact (key_representative (front := front) (suffix := suffix) query
    (groupOf (front := front) (suffix := suffix) query claim)).symm.trans
      (same.trans (key_position (front := front) (suffix := suffix) query claim))

omit [DecidableEq F] in
/-- Equal serialized matrix prefixes induce identical trusted left weights. -/
theorem left_eq_of_prefix (first second : PackedSumcheckSubclaim.Query F b (front + suffix))
    (same : first.toList.take front = second.toList.take front) :
    SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) first = SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) second := by
  let weights := fun key : {list : List (Bool → Matrix (Fin b) (Fin b) F) // list.length = front} =>
    fun position : Fin (2 ^ front) => FlatMatrixFold.weights key.val
      ((finCongr (congrArg (2 ^ ·) key.property)).symm position)
  have sameKeys :
      (⟨first.toList.take front, SubclaimSourceLayout.front_length (front := front) (suffix := suffix) first⟩ :
        {list : List (Bool → Matrix (Fin b) (Fin b) F) // list.length = front}) =
      ⟨second.toList.take front, SubclaimSourceLayout.front_length (front := front) (suffix := suffix) second⟩ :=
    Subtype.ext same
  exact congrArg weights sameKeys

theorem representative_left (query : Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix))
    (claim : Fin claims) :
    SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) (query (representative (front := front) (suffix := suffix) query (groupOf (front := front) (suffix := suffix) query claim))) =
      SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) (query claim) :=
  left_eq_of_prefix _ _ (representative_prefix query claim)

end

end FormalProof4FHE.HasteBoots.BatchQueryLayout
