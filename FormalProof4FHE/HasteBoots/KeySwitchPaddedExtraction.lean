module
public import FormalProof4FHE.HasteBoots.PaddedPublicZeroCheck
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
public import FormalProof4FHE.HasteBoots.AuthenticatedExtraction
public import FormalProof4FHE.HasteBoots.NativePBS
@[expose] public section

/-! Final extraction on the retained coefficient root. The increment is the
only private factor; mask and target are verifier-computed public tables. The
raw accumulator receives the native q/8 body bias exactly once. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchPaddedExtraction
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes dimension : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

abbrev Scheme := PaddedPublicZeroCheck.Scheme (ZMod q) Unit Bool (PBSHadamard.Term 1)
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg Response Memory CommitMemory heights (2^lanes) c

/-- Only the final coefficient object is opened by extraction. -/
def roots (family : PackedPBSOriginalReferences.Family d) (_ : Unit) : Digest :=
  family.coefficients (Fin.last d)

omit [DecidableEq Input] [DecidableEq Digest] in
/-- At an admitted ring size the native stride-one LUT contributes q/8. -/
theorem native_lut_bias (ringSize : 2 ≤ 2^(c+lanes)) :
    NativePublic.nandLut (q := q) 1 (NativeKeySwitch.zeroIndex : Fin (2^(c+lanes))) = (q/8 : ℕ) := by
  have mid : 0 < 2^(c+lanes)/2 + 2^(c+lanes)/4 := by omega
  simp [NativePublic.nandLut,NativeKeySwitch.zeroIndex,mid]

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The native target subtracts the raw endpoint and exactly one body bias. -/
theorem target_body (positive : 0 < dimension)
    (acc : NativeBlindRotation.Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension) :
    KeySwitchExtraction.target positive (NativePBS.bias acc) output true NativeKeySwitch.zeroIndex =
      output.body - acc true NativeKeySwitch.zeroIndex - (q/8 : ℕ) := by
  simp [KeySwitchExtraction.target,NativePBS.bias,NativeKeySwitch.zeroIndex,sub_add_eq_sub_sub]

omit [DecidableEq Input] [DecidableEq Digest] in
/-- Under the public ring-size check the target is the Rust LUT-biased target. -/
theorem target_body_native (ringSize : 2 ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc : NativeBlindRotation.Cipher q (2^(c+lanes))) (output : NativePublic.Ciphertext q dimension) :
    KeySwitchExtraction.target positive (NativePBS.bias acc) output true NativeKeySwitch.zeroIndex =
      output.body - acc true NativeKeySwitch.zeroIndex -
        NativePublic.nandLut 1 (NativeKeySwitch.zeroIndex : Fin (2^(c+lanes))) := by
  rw [native_lut_bias ringSize,target_body]

variable (s : Scheme (q := q) (c := c) (lanes := lanes) (Input := Input) (Cfg := Cfg)
  (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := heights))

/-- Fix the native extraction shape, original roots and typed interpolation rules,
retaining the factory's commitment work and returned private memory. -/
abbrev stage (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1) :=
  {s with
    encoding := enc
    factors := [()]
    nodes := NativePackedInterpolation.nodes q (nodesEnough.trans firstSmall)
    arity := PBSHadamard.arity
    coefficient := PBSHadamard.coefficient
    indices := AuthenticatedExtraction.indices
    publicTables := fun emission => AuthenticatedExtraction.publicTables positive (NativePBS.bias (acc emission)) (output emission)
    interpretFirst := fun (message : Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) point => NativePackedInterpolation.messagePolynomial
      (NativePackedInterpolation.consecutive q firstSmall) (message point)
    interpret := NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive q roundSmall)
    commit := do
      let original ← s.commit
      pure (roots family,original.2)}

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The extraction equation uses the fixed public mask and biased target. -/
theorem relation (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (emission : (Unit → Digest) × CommitMemory)
    (privateTables : Unit → MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q) :
    PackedZeroCube.Vanishes (stage s enc family positive acc output firstSmall roundSmall nodesEnough).arity
      (stage s enc family positive acc output firstSmall roundSmall nodesEnough).coefficient
      (stage s enc family positive acc output firstSmall roundSmall nodesEnough).indices
      (Sum.elim privateTables ((stage s enc family positive acc output firstSmall roundSmall nodesEnough).publicTables emission)) ↔
      AuthenticatedExtraction.Relation positive (NativePBS.bias (acc emission)) (output emission) (privateTables ()) :=
  AuthenticatedExtraction.vanishes_iff positive _ _ privateTables

omit [DecidableEq Input] [DecidableEq Digest] in
/-- With the retained private table interpreted as the increment, a true
checked relation enforces canonical extraction of the biased raw endpoint. -/
theorem extraction_of_relation (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (family : PackedPBSOriginalReferences.Family d) (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (emission : (Unit → Digest) × CommitMemory)
    (increment : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (checked : PackedZeroCube.Vanishes (stage s enc family positive acc output firstSmall roundSmall nodesEnough).arity
      (stage s enc family positive acc output firstSmall roundSmall nodesEnough).coefficient
      (stage s enc family positive acc output firstSmall roundSmall nodesEnough).indices
      (Sum.elim (fun _ : Unit => KeySwitchExtraction.pack (c := c) (lanes := lanes) increment)
        ((stage s enc family positive acc output firstSmall roundSmall nodesEnough).publicTables emission))) :
    CanonicalKeySwitch.Extraction shape (NativePBS.bias (acc emission)) increment (output emission) :=
  AuthenticatedExtraction.extraction_of_relation shape positive _ _ _
    ((relation s enc family positive acc output firstSmall roundSmall nodesEnough emission _).mp checked)

omit [DecidableEq Input] in
/-- Accepted incorrect extraction is the original-owner risk already bounded
below, once the retained physical source is interpreted as the increment. -/
theorem wrong_extraction_implies_originalRisk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (family : PackedPBSOriginalReferences.Family d) (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (outcome : PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedPublicZeroCheck.RunResult (stage s enc family positive acc output firstSmall roundSmall nodesEnough))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (increment : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (decoded : PaddedPublicZeroCheck.originalSources (stage s enc family positive acc output firstSmall roundSmall nodesEnough)
      dummy capacity radius owner = fun _ : Unit => KeySwitchExtraction.pack (c := c) (lanes := lanes) increment)
    (wrong : ¬CanonicalKeySwitch.Extraction shape (NativePBS.bias (acc outcome.1.1)) increment (output outcome.1.1))
    (passes : PaddedPublicZeroCheck.accepted (stage s enc family positive acc output firstSmall roundSmall nodesEnough) outcome.2.1 = true) :
    PaddedPublicZeroCheck.OriginalRisk (stage s enc family positive acc output firstSmall roundSmall nodesEnough)
      dummy capacity radius outcome := by
  refine ⟨owner,recorded,?_,passes⟩
  intro checked
  rw [decoded] at checked
  exact wrong (extraction_of_relation s enc family shape positive acc output firstSmall roundSmall nodesEnough outcome.1.1 increment checked)

variable [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)] [SampleableType Digest]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) (2^lanes))]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

/-- Every reached extraction retains the caller's retained coefficient root, including
later rejection. Commitment work and returned commitment memory are preserved. -/
theorem witness_roots (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q) (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedPublicZeroCheck.RunResult (stage s enc family positive acc output firstSmall roundSmall nodesEnough))
    (supported : outcome ∈ support (PaddedPublicZeroCheck.witness (stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy initial)) :
    outcome.1.1.1 = roots family := by
  simp only [PaddedPublicZeroCheck.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨original,_,same⟩ := firstSupported
  subst first
  rfl

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin c → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [∀ factor, SampleableType ((Fin (2^(s.code factor).front) × Fin (2^lanes)) → K)]

/-- The extraction's native original-owner rate is derived from typed
messages and actual source-specific single workers, with no degree, replay or
child-security certificate and no local collision charge. -/
theorem original_safe_bound [NeZero (2^lanes)] [∀ factor, NeZero (s.code factor).m]
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q) (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K) (dummy : Digest)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (PaddedPublicZeroCheck.witness (stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy initial)}[
      PaddedPublicZeroCheck.OriginalRisk (stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((c : ENNReal)/Fintype.card (ZMod q))^(2^lanes) + ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        (c : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (([()]).map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := 2^lanes)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum :=
  PaddedPublicZeroCheck.original_safe_bound (stage s enc family positive acc output firstSmall roundSmall nodesEnough) basis dummy (fun _ => by simp)
    enough capacity radius 2 (PBSHadamard.degree_bound (count := 1))
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small initial audited

end
end FormalProof4FHE.HasteBoots.KeySwitchPaddedExtraction
