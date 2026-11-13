module
public import FormalProof4FHE.HasteBoots.MonomialSourceAssociation
@[expose] public section

/-! Semantic accepted-wrong rotations inherit the actual native component
rates under one final exclusion, from the actual inherited audited state. -/
namespace FormalProof4FHE.HasteBoots.MonomialRotationProbability
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

abbrev Result := Before (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
  (NTTResponse := NTTResponse) (Memory := Memory) (NTTCommitMemory := NTTCommitMemory)
  (lanes := lanes) (cells := cells) (rows := rows) (nttK := nttK) (nttFront := nttFront)
  (nttQueries := nttQueries) (nttHeight := nttHeight) heights ×
  Option (Child (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
    (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (lanes := lanes)
    (cells := cells) (rows := rows) (front := front) (queries := queries) (height := height) heights)

/-- Raw event on the actual retained run. The support receipt selects its
existing NTT children; it neither conditions nor normalizes the experiment. -/
def AcceptedWrong (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (outcome : (Result (q := q) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (NTTResponse := NTTResponse) (NTTCommitMemory := NTTCommitMemory) (lanes := lanes) (cells := cells) (rows := rows) (nttK := nttK) (nttFront := nttFront) (nttQueries := nttQueries) (nttHeight := nttHeight) (front := front) (queries := queries) (height := height) heights)) : Prop :=
  ∃ product, outcome.2 = some product ∧
    ∃ present : (outcome.1,some product) ∈ support (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial),
      AmbientPublicZeroCheck.accepted product.2.1 = true ∧
      ∃ (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool),
        PackedMonomialRotation.polynomial (AcceptedMonomialProductRotation.nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial outcome.1 product present nttCapacity nttRadius true false) position half ≠
        NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
          (PackedMonomialRotation.polynomial (AcceptedMonomialProductRotation.nttSources firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial outcome.1 product present nttCapacity nttRadius false false) position half)

/-- Semantic failure transfers to the existing native original-risk union
on the same actual run, outside its one final Bad event. -/
theorem accepted_wrong_safe_le_risks (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes)) (nttRadius : Bool → ℕ)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (nttGeometry : ∀ side incoming, heights ((nttBase side incoming).tag true) = nttHeight)
    (zeroGeometry : ∀ incoming factor, heights ((zeroBase incoming).tag factor) = height)
    (associated : ∀ before product (present : (before,some product) ∈ support (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial)),
      ∀ side, MonomialSourceAssociation.nttParameters firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product present nttCapacity nttRadius nttGeometry side = MonomialSourceAssociation.productParameters (zeroBase := zeroBase) (heights := heights) (before := before) capacity radius zeroGeometry side)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial)}[
      AcceptedWrong firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial nttCapacity nttRadius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (AmbientMonomialProduct.finalState heights outcome)] ≤
    Pr{let outcome ← (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial)}[
      (AmbientNTTSequenceSoundness.AnyOriginalRisk
        (AmbientMonomialNTT.factory enc (Nat.pow_add 2 cells lanes).symm psi primitive coefficients evaluations nttBase)
        heights dummy nttCapacity nttRadius outcome.1.1 ∨
      (∃ product, outcome.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights
        (MonomialPublicZeroCheck.stage firstSmall roundSmall nodesEnough enc psi rotations evaluations (zeroBase outcome.1.1.memory))
        dummy capacity radius product)) ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (AmbientMonomialProduct.finalState heights outcome)] := by
  apply prEvent_mono
  intro outcome event
  rcases outcome with ⟨before,rest⟩
  obtain ⟨product,same,present,passed,position,active,half,wrong⟩ := event.1
  change rest = some product at same
  subst rest
  have coverage := MonomialSourceAssociation.all_rotations_or_risks firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product present
    nttCapacity nttRadius capacity radius nttGeometry zeroGeometry (associated before product present) audited passed
  rcases coverage with rotated | nttRisk | productRisk | failed
  · exact False.elim (wrong (rotated position active half))
  · exact ⟨Or.inl nttRisk,event.2⟩
  · exact ⟨Or.inr ⟨product,rfl,productRisk⟩,event.2⟩
  · exact False.elim (event.2 failed)

variable {K P : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType ((Fin (2^front) × Fin (2^lanes)) → K)]
  [SampleableType (Fin (rows+1) → ZMod q)] [SampleableType ((Fin (2^nttFront) × Fin (2^lanes)) → P)]

variable [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]

/-- The actual accepted-wrong rotation event has the already derived native
NTT-plus-product rate on the inherited state. Only public descriptor/numeric
admission is assumed; no child security probability is supplied. -/
theorem native_safe_bound [NeZero m] [NeZero nttM]
    (nttBasis : Module.Basis (Fin (2^lanes)) (ZMod q) P)
    (nttEnough : nttM ≤ Fintype.card (Fin (2^nttHeight))) (nttCapacity : 2^nttSuffix ≤ nttM*(2^lanes))
    (nttRadius : Bool → ℕ) (nttEpsilon : Bool → ENNReal)
    (nttGeometry : ∀ side memory source, heights ((nttBase side memory).tag source) = nttHeight)
    (nttSmall : ∀ side memory, (nttRadius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (nttBase side memory).domain) nttM :
        Set (Fin (2^nttHeight) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ side memory,
      (((((rows+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^nttK) +
        (cells : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side) +
        JointMatrixOpening.error (K := P) (m := nttM) (b := 2^lanes) (queries := nttQueries) (nttBase side memory).domain (nttRadius side)) ≤ nttEpsilon side)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*(2^lanes))
    (radius : ℕ) (epsilon : ENNReal)
    (geometry : ∀ memory factor, heights ((zeroBase memory).tag factor) = height)
    (small : ∀ memory, (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (zeroBase memory).domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (calibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius +
        JointMatrixOpening.error (K := K) (m := m) (b := 2^lanes) (queries := queries) (zeroBase memory).domain radius) ≤ epsilon)
    (associated : ∀ before product (present : (before,some product) ∈ support (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial)),
      ∀ side, MonomialSourceAssociation.nttParameters firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial before product present nttCapacity nttRadius (fun side incoming => nttGeometry side incoming true) side = MonomialSourceAssociation.productParameters (zeroBase := zeroBase) (heights := heights) (before := before) capacity radius geometry side)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (AmbientMonomialProduct.witness firstSmall roundSmall nodesEnough enc (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial)}[
      AcceptedWrong firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial nttCapacity nttRadius outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (AmbientMonomialProduct.finalState heights outcome)] ≤
        (nttEpsilon false + nttEpsilon true) + epsilon := by
  have transfer := accepted_wrong_safe_le_risks firstSmall roundSmall nodesEnough enc psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial nttCapacity nttRadius capacity radius
    (fun side incoming => nttGeometry side incoming true) geometry associated audited
  have native := AmbientMonomialProduct.native_safe_joint_bound firstSmall roundSmall nodesEnough enc
    (Nat.pow_add 2 cells lanes).symm psi primitive rotations coefficients evaluations nttBase zeroBase heights dummy memory initial
    nttBasis nttEnough nttCapacity nttRadius nttEpsilon nttGeometry nttSmall nttCalibrated
    basis enough capacity radius epsilon geometry small calibrated audited
  exact transfer.trans native

end
end FormalProof4FHE.HasteBoots.MonomialRotationProbability
