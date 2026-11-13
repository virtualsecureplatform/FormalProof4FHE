module
public import FormalProof4FHE.HasteBoots.AmbientMonomialProduct
public import FormalProof4FHE.HasteBoots.AcceptedMonomialNTT
@[expose] public section

/-! An accepted wrong monomial rotation in the actual NTT/public-product
execution exposes an existing original-owner risk or a concrete association
failure between those two stages' full original evaluation sources. -/
namespace FormalProof4FHE.HasteBoots.AcceptedMonomialProductRotation
open OracleSpec OracleComp
open InteractiveAuthenticatedOpening
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

abbrev Before (heights : Cfg → ℕ) := AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest)
  (Cfg := Cfg) (Response := NTTResponse) (Memory := Memory) (CommitMemory := NTTCommitMemory)
  (b := (2^lanes)) (c := cells) (r := (rows+1)) (k := nttK) (front := nttFront) (queries := nttQueries) (height := nttHeight) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

abbrev Child (heights : Cfg → ℕ) :=
  AmbientPublicZeroCheck.Prefix heights (Private := Bool) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
  AmbientPublicZeroCheck.RunResult heights (F := ZMod q) (Private := Bool) (Input := Input) (Digest := Digest)
    (Response := Response) (Memory := Memory) (b := 2^lanes) (n := cells+rows) (front := front) (queries := queries) (height := height)

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

/-- Decode the actually accepted NTT prefix retained by this product run. -/
def nttSources (capacity : 2^nttSuffix ≤ nttM*(2^lanes)) (radius : Bool → ℕ) (side source : Bool) :=
  let reached := AmbientMonomialProduct.reached_product firstSmall roundSmall nodesEnough enc
    (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  AcceptedMonomialNTT.sources enc psi primitive coefficients evaluations nttBase heights dummy memory initial
    before reached.2.1 reached.1 capacity radius side source

/-- Fresh original evaluation owners of the actual public-product check. -/
def productOwners :=
  AmbientCommittedBatchSafeBound.snapshots heights ((fun selectedMemory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase selectedMemory)) before.1.memory).tag product.1

/-- Full original private sources rather than the prover's terminal values. -/
def productSources (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ) :=
  AmbientPublicZeroCheck.originalPrivateSources heights ((fun selectedMemory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase selectedMemory)) before.1.memory) dummy capacity radius
    (productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product)

include firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported in
/-- The clear original-product risk gives its fixed native public equation on
all source coordinates; acceptance by itself is not used as a truth premise. -/
theorem product_relation (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (passed : AmbientPublicZeroCheck.accepted product.2.1 = true)
    (clear : ¬AmbientPublicZeroCheck.OriginalRisk heights ((fun selectedMemory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase selectedMemory)) before.1.memory) dummy capacity radius product) :
    ∀ cell lane, productSources firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before product capacity radius true cell lane =
      productSources firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before product capacity radius false cell lane *
        MonomialPublicZeroCheck.table psi rotations cell lane := by
  have reached := AmbientMonomialProduct.reached_product firstSmall roundSmall nodesEnough enc
    (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  have recorded := fun factor => AmbientPublicZeroCheck.fresh_recorded heights ((fun selectedMemory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase selectedMemory)) before.1.memory) dummy before.2 product reached.2.2 (by intro side; cases side <;> simp [MonomialPublicZeroCheck.stage, AuthenticatedPublicZeroCheck.nativeScheme, MonomialPublicZeroCheck.configure]) factor
  apply (MonomialPublicZeroCheck.original_vanishes_iff firstSmall roundSmall nodesEnough enc psi rotations evaluations
    (zeroBase before.1.memory) heights dummy capacity radius
    (productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product) product.1.1).mp
  by_contra wrong
  exact clear ⟨productOwners firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights before product,
    (fun factor => ⟨rfl,recorded factor⟩),wrong,passed⟩

include firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported in
/-- A wrong active rotation is covered by actual original-source mismatch or
one of the two already bounded native risk families. No source equality or
per-stage success-probability certificate is assumed. -/
theorem rotation_coverage (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (passed : AmbientPublicZeroCheck.accepted product.2.1 = true)
    (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool)
    (wrong : PackedMonomialRotation.polynomial
      (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius true false) position half ≠
      NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
        (PackedMonomialRotation.polynomial
          (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius false false) position half)) :
    (∃ side, nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius side true ≠
      PackedMonomialRotation.reindex (productSources firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before product capacity radius side)) ∨
    AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc (Eq.symm (Nat.pow_add 2 cells lanes)) psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius before.1 ∨
    AmbientPublicZeroCheck.OriginalRisk heights ((fun selectedMemory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase selectedMemory)) before.1.memory) dummy capacity radius product := by
  classical
  by_contra absent
  push Not at absent
  have reached := AmbientMonomialProduct.reached_product firstSmall roundSmall nodesEnough enc
    (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported
  apply wrong
  apply PackedMonomialRotation.rotate_of_relations psi primitive rotations
    (fun side => nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius side false)
    (productSources firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before product capacity radius)
  · intro side
    have transformed := AcceptedMonomialNTT.transforms enc psi primitive coefficients evaluations nttBase heights dummy memory initial before
      reached.2.1 reached.1 nttCapacity nttRadius absent.2.1 side
    change PackedNTT.Relation _ psi
      (NTTCompression.sourceRows cells (rows+1)
        (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius side false))
      (NTTCompression.sourceRows cells (rows+1)
        (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius side true)) at transformed
    rw [absent.1 side] at transformed
    exact transformed
  · exact product_relation firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported capacity radius passed absent.2.2

include firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported in
/-- All active rounds and both halves satisfy their rotations simultaneously
outside the same source/risk alternatives; no per-round exception is added. -/
theorem all_rotations_or_risks (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (passed : AmbientPublicZeroCheck.accepted product.2.1 = true) :
    (∀ (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool),
      PackedMonomialRotation.polynomial
      (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius true false) position half =
      NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
        (PackedMonomialRotation.polynomial
          (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius false false) position half)) ∨
    (∃ side, nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius side true ≠
      PackedMonomialRotation.reindex (productSources firstSmall roundSmall nodesEnough enc psi rotations evaluations zeroBase heights dummy before product capacity radius side)) ∨
    AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory enc (Eq.symm (Nat.pow_add 2 cells lanes)) psi primitive coefficients evaluations nttBase) heights dummy nttCapacity nttRadius before.1 ∨
    AmbientPublicZeroCheck.OriginalRisk heights ((fun selectedMemory => MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase selectedMemory)) before.1.memory) dummy capacity radius product := by
  classical
  by_cases good : ∀ (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool),
      PackedMonomialRotation.polynomial
      (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius true false) position half =
      NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
        (PackedMonomialRotation.polynomial
          (nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product supported nttCapacity nttRadius false false) position half)
  · exact Or.inl good
  · right
    push Not at good
    obtain ⟨position,active,half,wrong⟩ := good
    exact rotation_coverage firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase
      heights dummy memory initial before product supported nttCapacity nttRadius capacity radius passed position active half wrong

end
end FormalProof4FHE.HasteBoots.AcceptedMonomialProductRotation
