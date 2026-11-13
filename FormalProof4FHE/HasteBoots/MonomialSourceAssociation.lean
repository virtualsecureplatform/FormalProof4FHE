module
public import FormalProof4FHE.HasteBoots.AcceptedMonomialProductRotation
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
@[expose] public section

/-! Discharge the monomial evaluation-source mismatch using actual retained
owners and complete public decoder association under one shared final history. -/
namespace FormalProof4FHE.HasteBoots.MonomialSourceAssociation
open OracleSpec OracleComp
open InteractiveAuthenticatedOpening AcceptedMonomialProductRotation
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q lanes cells rows rounds : ℕ} [Fact q.Prime]
variable {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Input] [DecidableEq Digest]
  {front suffix m queries height : ℕ}

variable [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))] [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (TestMatrix (ZMod q) (2^front) (2^lanes))] [SampleableType (Fin queries → Fin (2^height))]


variable {NTTResponse NTTCommitMemory : Type} {nttK nttFront nttSuffix nttM nttQueries nttHeight : ℕ}
  [SampleableType (Fin nttK → Fin (rows+1) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^nttFront) (2^lanes))]
  [SampleableType (Fin nttQueries → Fin (2^nttHeight))]

variable (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
  (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
  (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(cells+lanes+1)))
  (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (coefficients evaluations : Bool → Digest)
  (nttBase : Bool → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg NTTResponse Memory NTTCommitMemory
    (2^lanes) cells (rows+1) nttK nttFront nttSuffix nttM nttQueries nttHeight)
  (zeroBase : Memory → AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
    (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
    Input Digest Cfg Response Memory CommitMemory (2^lanes) (cells+rows) front suffix m queries height)

variable (heights : Cfg → ℕ) (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (before : (Before (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
  (NTTResponse := NTTResponse) (Memory := Memory) (NTTCommitMemory := NTTCommitMemory)
  (lanes := lanes) (cells := cells) (rows := rows) (nttK := nttK) (nttFront := nttFront)
  (nttQueries := nttQueries) (nttHeight := nttHeight)) heights) (product : (Child (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
  (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (lanes := lanes)
  (cells := cells) (rows := rows) (front := front) (queries := queries) (height := height)) heights)
  (supported : (before,some product) ∈ support (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc
    (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial))


/-- The actual chosen NTT call, with its returned factory memory. -/
def selected (side : Bool) :=
  let reached := AmbientMonomialProduct.reached_product firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  AcceptedMonomialNTT.selected enc psi primitive coefficients evaluations nttBase heights dummy memory initial
    before reached.2.1 reached.1 side

/-- Its actual fresh checkpoint owners, without replacing their saved logs. -/
def nttOwners (side : Bool) :=
  let reached := AmbientMonomialProduct.reached_product firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  AcceptedMonomialNTT.owners enc psi primitive coefficients evaluations nttBase heights dummy memory initial
    before reached.2.1 reached.1 side

/-- Complete metadata for the selected NTT's original evaluation decoder. -/
def nttParameters (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (nttGeometry : ∀ side incoming, heights ((nttBase side incoming).tag true) = nttHeight) (side : Bool) :=
  let child := selected firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported side
  AmbientSourceDescriptor.parameters (front := nttFront) heights ((nttBase side child.1).tag true)
    (nttGeometry side child.1) (nttBase side child.1).domain nttCapacity (nttRadius side)

/-- The product's original private decoder metadata at its actual memory. -/
def productParameters (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (zeroGeometry : ∀ incoming factor, heights ((zeroBase incoming).tag factor) = height) (side : Bool) :=
  AmbientSourceDescriptor.parameters (front := front) heights ((zeroBase before.1.memory).tag side)
    (zeroGeometry before.1.memory side) (zeroBase before.1.memory).domain capacity radius

omit [DecidableEq Input] [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)] in
/-- The regrouped logical view preserves each flat native address. -/
theorem regroup_logical (parameters : RecordedPaddedSource.Parameters (ZMod q) Cfg heights (2^lanes))
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) parameters) :
    RecordedPaddedSource.logical parameters enc dummy ((rows+1)+cells) owner =
      PackedMonomialRotation.reindex (RecordedPaddedSource.logical parameters enc dummy ((cells+rows)+1) owner) := by
  funext cell lane
  apply congrFun (RecordedPaddedSource.logical_same_address parameters enc dummy owner cell _ ?_) lane
  simp only [Equiv.apply_symm_apply,finCongr_apply,Fin.val_cast]

include firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported in
/-- The actual NTT and product sources agree for both original evaluations
under their complete public descriptor association and the one final history.
No source-value premise, independent owner receipt or alias union is supplied. -/
theorem sources_eq_or_bad (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (nttGeometry : ∀ side incoming, heights ((nttBase side incoming).tag true) = nttHeight)
    (zeroGeometry : ∀ incoming factor, heights ((zeroBase incoming).tag factor) = height)
    (associated : ∀ side, nttParameters firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius nttGeometry side = productParameters (zeroBase := zeroBase) (heights := heights) (before := before) capacity radius zeroGeometry side)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    (∀ side, AcceptedMonomialProductRotation.nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius side true = PackedMonomialRotation.reindex (AcceptedMonomialProductRotation.productSources firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before product capacity radius side)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) product.2.2 := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) product.2.2
  · exact Or.inr bad
  · left
    intro side
    have reached := AmbientMonomialProduct.reached_product firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
    let child := selected firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported side
    have member := AcceptedMonomialNTT.selected_member enc psi primitive coefficients evaluations nttBase heights dummy memory initial
      before reached.2.1 reached.1 side
    have nttRecorded := AmbientMonomialProduct.retained_source_recorded firstSmall roundSmall nodesEnough enc
      (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
      (side,child) member true
    have zeroRecorded := AmbientPublicZeroCheck.fresh_recorded heights
      (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase before.1.memory))
      dummy before.2 product reached.2.2
      (by intro factor; cases factor <;> simp [MonomialPublicZeroCheck.stage, AuthenticatedPublicZeroCheck.nativeScheme, MonomialPublicZeroCheck.configure]) side
    have rootNtt := AcceptedMonomialNTT.owners_recorded enc psi primitive coefficients evaluations nttBase heights dummy memory initial
      before reached.2.1 reached.1 side true
    have rootProduct := AmbientMonomialProduct.product_roots firstSmall roundSmall nodesEnough enc
      (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
    have finalAudited := AmbientMonomialProduct.audited_witness firstSmall roundSmall nodesEnough enc
      (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial
      audited (before,some product) supported
    change CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) product.2.2 at finalAudited
    have comparison := AmbientSourceDescriptor.associated_logical_eq_or_bad
      (nttParameters firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius nttGeometry side) (productParameters (zeroBase := zeroBase) (heights := heights) (before := before) capacity radius zeroGeometry side) (associated side) enc dummy ((rows+1)+cells) product.2.2 finalAudited
      (nttOwners firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported side true) (AcceptedMonomialProductRotation.productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product side) nttRecorded zeroRecorded
      (rootNtt.1.trans (congrFun rootProduct side).symm)
    have equal := comparison.resolve_right bad
    have normalizedNtt := AmbientSourceDescriptor.original enc dummy heights ((nttBase side child.1).tag true)
      (nttGeometry side child.1) (nttBase side child.1).domain nttCapacity (nttRadius side)
      (nttBase side child.1).dimensions (nttOwners firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported side true)
    have normalizedProduct := AmbientSourceDescriptor.original enc dummy heights ((zeroBase before.1.memory).tag side)
      (zeroGeometry before.1.memory side) (zeroBase before.1.memory).domain capacity radius
      (zeroBase before.1.memory).dimensions (AcceptedMonomialProductRotation.productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product side)
    change QueryReindex.source (nttBase side child.1).dimensions
      (AmbientMatrixSource.source (front := nttFront) enc dummy heights (nttBase side child.1).domain nttCapacity (nttRadius side)
        ((nttBase side child.1).tag true) (nttOwners firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported side true)) =
      PackedMonomialRotation.reindex (QueryReindex.source (zeroBase before.1.memory).dimensions
        (AmbientMatrixSource.source (front := front) enc dummy heights (zeroBase before.1.memory).domain capacity radius
          ((zeroBase before.1.memory).tag side) (AcceptedMonomialProductRotation.productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product side)))
    rw [normalizedNtt,normalizedProduct]
    exact equal.trans (regroup_logical (enc := enc) (dummy := dummy) (heights := heights) (cells := cells) (rows := rows) (productParameters (zeroBase := zeroBase) (heights := heights) (before := before) capacity radius zeroGeometry side) (AcceptedMonomialProductRotation.productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product side))

include firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported in
/-- All actual coefficient-domain rotations hold simultaneously outside the
existing original-risk families and one final exception. Public descriptors
replace the previously exposed source-value mismatch. -/
theorem all_rotations_or_risks (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (nttGeometry : ∀ side incoming, heights ((nttBase side incoming).tag true) = nttHeight)
    (zeroGeometry : ∀ incoming factor, heights ((zeroBase incoming).tag factor) = height)
    (associated : ∀ side, nttParameters firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius nttGeometry side = productParameters (zeroBase := zeroBase) (heights := heights) (before := before) capacity radius zeroGeometry side)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial)
    (passed : AmbientPublicZeroCheck.accepted product.2.1 = true) :
    (∀ (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool),
      PackedMonomialRotation.polynomial
      (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius true false) position half =
      NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
        (PackedMonomialRotation.polynomial
          (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius false false) position half)) ∨
    AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius before.1 ∨
    AmbientPublicZeroCheck.OriginalRisk heights (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase before.1.memory)) dummy capacity radius product ∨
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) product.2.2 := by
  rcases sources_eq_or_bad firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius capacity radius nttGeometry zeroGeometry associated audited with agree | bad
  · rcases AcceptedMonomialProductRotation.all_rotations_or_risks firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
      nttCapacity nttRadius capacity radius passed with rotated | mismatch | nttRisk | productRisk
    · exact Or.inl rotated
    · obtain ⟨side,different⟩ := mismatch
      exact False.elim (different (agree side))
    · exact Or.inr (Or.inl nttRisk)
    · exact Or.inr (Or.inr (Or.inl productRisk))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.MonomialSourceAssociation
