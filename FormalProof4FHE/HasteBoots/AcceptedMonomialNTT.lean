module
public import FormalProof4FHE.HasteBoots.AmbientMonomialNTT
public import FormalProof4FHE.HasteBoots.AmbientNTTSequenceAccepted
public import FormalProof4FHE.HasteBoots.PackedMonomialRotation
@[expose] public section

/-! Decode the two actually reached monomial NTT calls. Selection uses the
retained accepted loop, and each source retains its actual private memory,
original checkpoint owner and caller root. -/
namespace FormalProof4FHE.HasteBoots.AcceptedMonomialNTT
open OracleSpec OracleComp BinaryTree
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows k front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin (rows+1) → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
variable (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
  (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(cells+lanes+1)))
  (coefficients evaluations : Bool → Digest)
  (base : Bool → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2^lanes) cells (rows+1) k front suffix m queries height)
  (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))


variable (outcome : (AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (b := 2^lanes) (c := cells) (r := rows+1) (k := k) (front := front) (queries := queries) (height := height)) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (AmbientMonomialNTT.witness enc (Nat.pow_add 2 cells lanes).symm psi primitive
    coefficients evaluations base heights dummy memory initial))
  (passed : outcome.1.accepted = true)

include enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed in
/-- Both trusted indices occur in the actual accepted execution. -/
theorem accepted_child (side : Bool) :
    ∃ child : Memory × (AmbientMonomialNTT.Child heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (b := 2^lanes) (c := cells) (r := rows+1) (k := k) (front := front) (queries := queries) (height := height)), (side,child) ∈ outcome.1.results := by
  have order := AmbientNTTSequenceSoundness.accepted_indices (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) heights enc dummy [false,true]
    memory initial outcome supported passed
  have member : side ∈ outcome.1.results.map Prod.fst := by
    rw [order]
    cases side <;> simp
  obtain ⟨entry,retained,equal⟩ := List.mem_map.mp member
  cases entry with
  | mk selected child =>
    change selected = side at equal
    subst selected
    exact ⟨child,retained⟩

/-- Select a retained child rather than executing a fresh NTT experiment. -/
def selected (side : Bool) : Memory × (AmbientMonomialNTT.Child heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (b := 2^lanes) (c := cells) (r := rows+1) (k := k) (front := front) (queries := queries) (height := height)) :=
  Classical.choose (accepted_child enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side)

include enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed in
theorem selected_member (side : Bool) :
    (side,selected enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side) ∈ outcome.1.results :=
  Classical.choose_spec (accepted_child enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side)

/-- Fresh snapshots belong to the actual selected call and its factory memory. -/
def owners (side : Bool) :=
  let child := selected enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
  AmbientCommittedBatchSafeBound.snapshots heights (base side child.1).tag child.2.1

include enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed in
/-- The same owners have the caller's roots and are recorded at the child end. -/
theorem owners_recorded (side source : Bool) :
    let child := selected enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
    (owners enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side source).root =
      (if source then evaluations side else coefficients side) ∧
    ⟨(base side child.1).tag source,
      owners enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side source⟩ ∈
      child.2.2.2.checkpoints.checkpoints := by
  let child := selected enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
  have member := selected_member enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
  obtain ⟨before,present⟩ := AmbientNTTSequenceSoundness.retained_child_support (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) heights enc dummy [false,true]
    memory initial outcome supported (side,child) member
  have recorded := AmbientNTT.fresh_recorded heights ((AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) side child.1) dummy before child.2 present source
  have roots := AmbientMonomialNTT.child_roots enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base
    heights dummy side child.1 before child.2 present
  exact ⟨congrFun roots source,recorded⟩

/-- Complete decoded coefficient/evaluation sources from the actual owners. -/
def sources (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Bool → ℕ) (side source : Bool) :=
  let child := selected enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
  AmbientNTT.originalSources heights ((AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) side child.1) dummy capacity (radius side)
    (owners enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side) source

include enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed in
/-- Clearing the existing original-risk union enforces the actual native
transform on every row of both selected coefficient sources. -/
theorem transforms (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Bool → ℕ)
    (clear : ¬AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) heights dummy capacity radius outcome.1)
    (side : Bool) :
    PackedNTT.Relation (Nat.pow_add 2 cells lanes).symm psi
      (NTTCompression.sourceRows cells (rows+1)
        (sources enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed capacity radius side false))
      (NTTCompression.sourceRows cells (rows+1)
        (sources enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed capacity radius side true)) := by
  let child := selected enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
  have member := selected_member enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side
  have accepted := AmbientNTTSequenceAccepted.accepted_children (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) heights enc dummy [false,true]
    memory initial outcome supported passed (side,child) member
  obtain ⟨before,present⟩ := AmbientNTTSequenceSoundness.retained_child_support (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) heights enc dummy [false,true]
    memory initial outcome supported (side,child) member
  have recorded := fun source => AmbientNTT.fresh_recorded heights ((AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations base) side child.1) dummy before child.2 present source
  by_contra wrong
  exact clear ⟨(side,child),member,
    owners enc psi primitive coefficients evaluations base heights dummy memory initial outcome supported passed side,
    (fun source => ⟨rfl,recorded source⟩),wrong,accepted⟩

end
end FormalProof4FHE.HasteBoots.AcceptedMonomialNTT
