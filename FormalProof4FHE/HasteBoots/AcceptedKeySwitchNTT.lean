module
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedNTT
public import FormalProof4FHE.HasteBoots.DecodedFamilyNTT
@[expose] public section

/-! Select the actual child for every scheduled native key-switch NTT in an
accepted run. Fresh original owners are obtained from execution and retained
at the loop end; no owner authenticity or child-from-empty premise is supplied. -/
namespace FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q c lanes d : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (base : Fin (d+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2^lanes) c 1 (2^lanes))
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
  (nodesEnough : 2*(2^lanes) ≤ q) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))

variable [SampleableType (Fin (2^lanes) → Fin 1 → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((base index memory).code side).front) (2^lanes))]
  [∀ index memory side, SampleableType (Fin ((base index memory).code side).queries → Fin (2^heights ((base index memory).tag side)))]

variable (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (KeySwitchPaddedNTT.witness base enc family nodesEnough
    (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial))

include supported in
/-- Every scheduled index has an actual retained child with that same sigma
index; neither the memory nor the child support is independently supplied. -/
theorem accepted_child (passes : outcome.1.accepted = true) (index : Fin (d+1)) :
    ∃ child : PaddedNTTSequence.Child (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive),
      (index,child) ∈ outcome.1.results ∧ child.1.1 = index := by
  have order := KeySwitchPaddedNTT.accepted_indices base enc family nodesEnough
    (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial outcome supported passes
  have member : index ∈ outcome.1.results.map Prod.fst := by
    rw [order]
    exact List.mem_finRange index
  obtain ⟨entry,retained,equal⟩ := List.mem_map.mp member
  have selected := PaddedNTTSequence.retained_index (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy (List.finRange (d+1)) memory initial outcome supported entry retained
  cases entry with
  | mk scheduled child =>
    change scheduled = index at equal
    subst scheduled
    exact ⟨child,retained,selected⟩

/-- The fresh original owners of a retained native NTT. -/
def owners (entry : Fin (d+1) × PaddedNTTSequence.Child (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)) :=
  HeterogeneousBatchOpening.snapshots heights (base entry.2.1.1 entry.2.1.2).tag entry.2.2.1

include supported in
/-- Fresh owner roots equal the scheduled caller roots, and these same owners
are recorded at both the child end and the loop end. -/
theorem owners_recorded
    (entry : Fin (d+1) × PaddedNTTSequence.Child (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)) (member : entry ∈ outcome.1.results) (side : Bool) :
    (owners base enc family nodesEnough psi primitive entry side).root = KeySwitchPaddedNTT.roots family entry.1 side ∧
    ⟨(base entry.2.1.1 entry.2.1.2).tag side,owners base enc family nodesEnough psi primitive entry side⟩ ∈
      entry.2.2.2.2.checkpoints.checkpoints ∧
    ⟨(base entry.2.1.1 entry.2.1.2).tag side,owners base enc family nodesEnough psi primitive entry side⟩ ∈
      outcome.2.checkpoints.checkpoints := by
  obtain ⟨before,present⟩ := PaddedNTTSequence.retained_child_support (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy (List.finRange (d+1))
    memory initial outcome supported entry member
  have recorded := PaddedNTT.fresh_recorded (PaddedNTTSequence.shared (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc entry.2.1.1 entry.2.1.2)
    dummy before entry.2.2 present side
  have roots := KeySwitchPaddedNTT.retained_roots base enc family nodesEnough (Nat.pow_add 2 c lanes).symm
    psi primitive dummy memory initial outcome supported entry member
  refine ⟨congrFun roots side,recorded,?_⟩
  exact PaddedNTTSequence.child_retains (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy (List.finRange (d+1)) memory initial outcome supported
    entry member _ _ recorded

include supported in
/-- Every retained accepted native child has its actual decoded transform
outside the existing union of original-owner risks. -/
theorem retained_transform
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ)
    (passes : outcome.1.accepted = true)
    (clear : ¬PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1)
    (entry : Fin (d+1) × PaddedNTTSequence.Child (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)) (member : entry ∈ outcome.1.results) (half : Bool) :
    BlindRotationNTT.transform (c+lanes) psi
      (DecodedPaddedNTT.cipher ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) entry.2.1.1 entry.2.1.2) dummy
        (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2)
        (owners base enc family nodesEnough psi primitive entry) false half) =
      DecodedPaddedNTT.cipher ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) entry.2.1.1 entry.2.1.2) dummy
        (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2)
        (owners base enc family nodesEnough psi primitive entry) true half := by
  have recorded : ∀ side, (owners base enc family nodesEnough psi primitive entry side).root = entry.2.2.1.1.1 side ∧
      ⟨(base entry.2.1.1 entry.2.1.2).tag side,owners base enc family nodesEnough psi primitive entry side⟩ ∈
        entry.2.2.2.2.checkpoints.checkpoints := by
    intro side
    exact ⟨rfl,(owners_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported entry member side).2.1⟩
  have accepted := PaddedNTTSequence.accepted_children (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy (List.finRange (d+1)) memory initial outcome supported passes entry member
  have safe : ¬PaddedNTT.OriginalRisk ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) entry.2.1.1 entry.2.1.2) dummy
      (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2) entry.2.2 := by
    intro risk
    exact clear ⟨entry,member,risk⟩
  exact DecodedPaddedNTT.native_transform_of_not_risk (base entry.2.1.1 entry.2.1.2) enc
    (KeySwitchPaddedNTT.roots family entry.2.1.1) nodesEnough psi primitive dummy
    (capacity entry.2.1.1 entry.2.1.2) (radius entry.2.1.1 entry.2.1.2) entry.2.2
    (owners base enc family nodesEnough psi primitive entry) recorded accepted safe half

/-- Choose one child that the accepted execution actually reached for this index. -/
def selected (passes : outcome.1.accepted = true) (index : Fin (d+1)) :
    PaddedNTTSequence.Child (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) :=
  Classical.choose (accepted_child base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index)

include supported in
theorem selected_member (passes : outcome.1.accepted = true) (index : Fin (d+1)) :
    (index,selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index) ∈ outcome.1.results :=
  (Classical.choose_spec (accepted_child base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index)).1

/-- Construct a recorded source family directly from the accepted loop's
coefficient/evaluation owners and their actual per-child decoder descriptors. -/
def sourceFamily
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true) :
    RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (Fin (d+1) × Bool) heights (2^lanes) :=
  let child := selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes
  { parameters := fun pair => PaddedStageSourceInterpretation.nttParameters
      ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) (child pair.1).1.1 (child pair.1).1.2)
      (capacity (child pair.1).1.1 (child pair.1).1.2) (radius (child pair.1).1.1 (child pair.1).1.2) pair.2
    roots := fun pair => KeySwitchPaddedNTT.roots family pair.1 pair.2
    owners := fun pair => owners base enc family nodesEnough psi primitive (pair.1,child pair.1) pair.2
    ownerRoots := fun pair => (owners_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported
      (pair.1,child pair.1)
      (selected_member base enc family nodesEnough psi primitive dummy memory initial outcome supported passes pair.1) pair.2).1 }

include supported in
/-- Every anchor in the constructed family is recorded in the actual loop end. -/
theorem sourceFamily_recorded
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true) :
    RecordedPaddedSourceFamily.Recorded
      (sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 := by
  intro pair
  exact (owners_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported
    (pair.1,selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes pair.1)
    (selected_member base enc family nodesEnough psi primitive dummy memory initial outcome supported passes pair.1) pair.2).2.2

include supported in
/-- Acceptance and exclusion of the existing loop risks give all d+1 native
transforms on the family constructed from that same actual execution. -/
theorem sourceFamily_transform
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ)
    (passes : outcome.1.accepted = true)
    (clear : ¬PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1)
    (incomingAudit : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial)
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2)
    (index : Fin (d+1)) (half : Bool) :
    BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c)
        (sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
        enc dummy (index,false) half) =
      PackedCipherSource.familyCipher (c := c)
        (sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
        enc dummy (index,true) half := by
  let child := selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index
  have member : (index,child) ∈ outcome.1.results :=
    selected_member base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index
  let world := sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes
  have audited := PaddedNTTSequence.audited_witness (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy (List.finRange (d+1))
    memory initial outcome supported incomingAudit
  have worldRecorded := sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes
  have same : DecodedPaddedNTT.cipher ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) child.1.1 child.1.2) dummy
      (capacity child.1.1 child.1.2) (radius child.1.1 child.1.2)
      (owners base enc family nodesEnough psi primitive (index,child)) =
      fun side => PackedCipherSource.familyCipher (c := c) world enc dummy (index,side) := by
    funext side
    exact (DecodedPaddedNTT.cipher_family_eq_or_bad ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) child.1.1 child.1.2)
      world (index,side) side dummy (capacity child.1.1 child.1.2) (radius child.1.1 child.1.2) rfl
      outcome.2 audited worldRecorded (owners base enc family nodesEnough psi primitive (index,child))
      (owners_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported (index,child) member side).2.2
      (owners_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported (index,child) member side).1).resolve_right noBad
  have transformed := retained_transform base enc family nodesEnough psi primitive dummy memory initial outcome supported
    capacity radius passes clear (index,child) member half
  rw [same] at transformed
  exact transformed

/-- The constructed family retains exactly the caller-owned coefficient and
evaluation roots, independently of the selected private memory. -/
theorem sourceFamily_roots
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (index : Fin (d+1)) (side : Bool) :
    (sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes).roots (index,side) =
      KeySwitchPaddedNTT.roots family index side := rfl

/-- A false transform of a family built from the actual accepted execution.
Support and acceptance here are factual properties of that same outcome;
no independent owner family or source interpretation is quantified. -/
def FalseFamilyTransform
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) : Prop :=
  ∃ present : outcome ∈ support (KeySwitchPaddedNTT.witness base enc family nodesEnough
      (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial),
    ∃ passes : outcome.1.accepted = true, ∃ index half,
      BlindRotationNTT.transform (c+lanes) psi
        (PackedCipherSource.familyCipher (c := c)
          (sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome present capacity radius passes)
          enc dummy (index,false) half) ≠
        PackedCipherSource.familyCipher (c := c)
          (sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome present capacity radius passes)
          enc dummy (index,true) half

/-- False decoded transforms on the executed accepted family are covered by
the existing original-owner risk union under the same single final exclusion. -/
theorem false_family_transform_safe_le_original
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ)
    (incomingAudit : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let actual ← (KeySwitchPaddedNTT.witness base enc family nodesEnough
      (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial)}[
      FalseFamilyTransform base enc family nodesEnough psi primitive dummy memory initial actual capacity radius ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2] ≤
    Pr{let actual ← (KeySwitchPaddedNTT.witness base enc family nodesEnough
      (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial)}[
      PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius actual.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2] := by
  apply prEvent_mono
  intro actual event
  obtain ⟨⟨present,passes,index,half,wrong⟩,noBad⟩ := event
  refine ⟨?_,noBad⟩
  by_contra clear
  exact wrong (sourceFamily_transform base enc family nodesEnough psi primitive dummy memory initial actual present
    capacity radius passes clear incomingAudit noBad index half)

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin 1 → ZMod q)]
  [∀ index memory side, SampleableType ((Fin (2^((base index memory).code side).front) × Fin (2^lanes)) → K)]

/-- The actual accepted family's false native transform has the derived d+1
NTT rate, including each original physical PCS error outside one final Bad. -/
theorem false_family_transform_safe_bound
    [∀ index memory side, NeZero ((base index memory).code side).m]
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (enough : ∀ index memory side, ((base index memory).code side).m ≤
      Fintype.card (Fin (2^heights ((base index memory).tag side))))
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (epsilon : Fin (d+1) → ENNReal)
    (small : ∀ index memory side, (radius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ((base index memory).domain side))
        ((base index memory).code side).m : Set (Fin (2^heights ((base index memory).tag side)) → K)) : ℚ≥0)/3)
    (calibrated : ∀ index memory,
      ((((1 : ENNReal)/Fintype.card (ZMod q))^(2^lanes)) + (c : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := ((base index memory).code false).m) (b := (2^lanes))
          (queries := ((base index memory).code false).queries) ((base index memory).domain false) (radius index memory false) +
        JointMatrixOpening.error (K := K) (m := ((base index memory).code true).m) (b := (2^lanes))
          (queries := ((base index memory).code true).queries) ((base index memory).domain true) (radius index memory true)) ≤ epsilon index)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let actual ← (KeySwitchPaddedNTT.witness base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial)}[
      FalseFamilyTransform base enc family nodesEnough psi primitive dummy memory initial actual capacity radius ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2] ≤ ((List.finRange (d+1)).map epsilon).sum :=
  (false_family_transform_safe_le_original base enc family nodesEnough psi primitive dummy memory initial
    capacity radius audited).trans
    (KeySwitchPaddedNTT.original_safe_bound base enc family nodesEnough (Nat.pow_add 2 c lanes).symm
      psi primitive dummy memory initial basis enough capacity radius epsilon small calibrated audited)

end
end FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
