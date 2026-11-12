module
public import FormalProof4FHE.HasteBoots.PaddedZeroCheck
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
@[expose] public section

/-! Final key-switch product on the original evaluation/key roots, followed
by the result root. The native degree-two shape and interpolation messages are
fixed by the verifier; physical single-opening parameters remain source-specific. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchPaddedProduct
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q d b n : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

abbrev Scheme := PaddedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor d) (PBSHadamard.Term d)
  (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q)
  Input Digest Cfg Response Memory CommitMemory heights b n

/-- The final product borrows the same evaluation/key objects used by the
caller family, in digit/key pairs and then the original evaluation result. -/
def roots (family : PackedPBSOriginalReferences.Family d) (factor : PBSHadamard.Factor d) : Digest :=
  (PackedPBSOriginalReferences.roleReference family factor).root

variable (s : Scheme (q := q) (d := d) (b := b) (n := n) (Input := Input) (Cfg := Cfg)
  (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := heights))

/-- Fix the native product shape, original roots and typed interpolation rules,
retaining the factory's commitment work and returned private memory. -/
abbrev stage (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
    (nodesEnough : 2*b ≤ (2*b-1)*2+1) :=
  {s with
    encoding := enc
    factors := PBSHadamard.factors d
    nodes := NativePackedInterpolation.nodes q (nodesEnough.trans firstSmall)
    arity := PBSHadamard.arity
    coefficient := PBSHadamard.coefficient
    indices := PBSHadamard.indices
    interpretFirst := fun (message : Fin b → Fin ((2*b-1)*2+1) → ZMod q) point => NativePackedInterpolation.messagePolynomial
      (NativePackedInterpolation.consecutive q firstSmall) (message point)
    interpret := NativePackedInterpolation.messagePolynomial (NativePackedInterpolation.consecutive q roundSmall)
    commit := do
      let original ← s.commit
      pure (roots family,original.2)}

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The checked native polynomial is exactly the pointwise digit/key product
sum minus the original result, on the logical source tables. -/
theorem relation (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
    (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor d) (n+1) b) :
    PackedZeroCube.Vanishes (stage s enc family firstSmall roundSmall nodesEnough).arity
      (stage s enc family firstSmall roundSmall nodesEnough).coefficient (stage s enc family firstSmall roundSmall nodesEnough).indices tables ↔
      PBSHadamard.Relation tables := PBSHadamard.vanishes_iff tables

variable [SampleableType (Fin b → ZMod q)] [SampleableType (PackedZeroReduction.Points (ZMod q) n b)]
  [SampleableType (Fin b → Fin b → ZMod q)] [SampleableType Digest]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

/-- Every reached product retains the caller's original root family, including
later rejection. Commitment work and returned commitment memory are preserved. -/
theorem witness_roots (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q) (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedZeroCheck.RunResult (stage s enc family firstSmall roundSmall nodesEnough))
    (supported : outcome ∈ support (PaddedZeroCheck.witness (stage s enc family firstSmall roundSmall nodesEnough) dummy initial)) :
    outcome.1.1.1 = roots family := by
  simp only [PaddedZeroCheck.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨original,_,same⟩ := firstSupported
  subst first
  rfl

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin n → ZMod q)]
  [SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]
  [∀ factor, SampleableType ((Fin (2^(s.code factor).front) × Fin b) → K)]

/-- The final product's native original-owner rate is derived from typed
messages and actual source-specific single workers, with no degree, replay or
child-security certificate and no local collision charge. -/
theorem original_safe_bound [NeZero b] [∀ factor, NeZero (s.code factor).m]
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q) (nodesEnough : 2*b ≤ (2*b-1)*2+1)
    (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : PBSHadamard.Factor d → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (PaddedZeroCheck.witness (stage s enc family firstSmall roundSmall nodesEnough) dummy initial)}[
      PaddedZeroCheck.OriginalRisk (stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((n : ENNReal)/Fintype.card (ZMod q))^b + ((((((2*b-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b)) +
        (n : ENNReal)*((((((2*b-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((PBSHadamard.factors d).map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := b)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum :=
  PaddedZeroCheck.original_safe_bound (stage s enc family firstSmall roundSmall nodesEnough) basis dummy PBSHadamard.factors_complete
    enough capacity radius 2 PBSHadamard.degree_bound
    (fun _ _ => NativePackedInterpolation.messagePolynomial_degree _ _)
    (fun _ => NativePackedInterpolation.messagePolynomial_degree _ _) small initial audited

end
end FormalProof4FHE.HasteBoots.KeySwitchPaddedProduct
