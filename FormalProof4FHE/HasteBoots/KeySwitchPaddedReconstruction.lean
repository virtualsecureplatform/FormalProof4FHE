module
public import FormalProof4FHE.HasteBoots.PaddedLinear
public import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
@[expose] public section

/-! Canonical final key-switch reconstruction on the known negative-mask input,
original digit coefficient roots and newly committed borrows. Trusted native
relations check reconstruction and both borrow endpoints, with each source's
own physical PCS parameters and logical high-zero view. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchPaddedReconstruction
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q d b n : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (s : PaddedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2*d+2) b n)

/-- Only borrow roots are supplied by the original commit callback. The caller
fixes the input, original digit roots, relation list and native nodes while
retaining all commitment work and the emitted private memory. -/
abbrev stage (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*b ≤ q) (radix : ZMod q) :=
  {s with
    encoding := enc
    nodes := NativePackedInterpolation.nodes q nodesEnough
    relations := DecompositionLinear.relations radix
    commit := do
      let emission ← s.commit
      pure (OwnedDecompositionSoundness.roots input.root (fun i => family.coefficients (Fin.castSucc i)) emission.1,emission.2)}

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The native linear list means radix reconstruction and zero first/last
borrows on every logical cell and packed lane. -/
theorem relation (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*b ≤ q) (radix : ZMod q)
    (tables : Fin (2*d+2) → MatrixFold.Cube n → Fin b → ZMod q) :
    PackedLinear.Holds (stage s enc input family nodesEnough radix).relations tables ↔
      DecompositionLinear.Relation radix tables := DecompositionLinear.holds_iff radix tables

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The fixed relation list satisfies native preflight at an admitted width;
raw dimensions and role indices are already fixed by the types. -/
theorem preflight (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*b ≤ q) (radix : ZMod q) (positive : 0 < b) (large : 2*b < q) :
    PaddedLinear.preflight (stage s enc input family nodesEnough radix) = true := by
  simp [PaddedLinear.preflight,DecompositionLinear.relations,DecompositionLinear.reconstruction,positive,large,ZMod.card]

variable [SampleableType (Fin b → ZMod q)] [SampleableType Digest]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

/-- Input and digit roots are the caller's originals on every supported path,
including a later rejection; no independent source-identity certificate is used. -/
theorem witness_expected_roots (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*b ≤ q) (radix : ZMod q) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedLinear.RunResult (stage s enc input family nodesEnough radix))
    (supported : outcome ∈ support (PaddedLinear.witness (stage s enc input family nodesEnough radix) dummy initial)) :
    outcome.1.1.1 DecompositionLinear.input = input.root ∧
      ∀ i : Fin d, outcome.1.1.1 (DecompositionLinear.digit i) = family.coefficients (Fin.castSucc i) := by
  simp only [PaddedLinear.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨emission,_,same⟩ := firstSupported
  subst first
  exact ⟨OwnedDecompositionSoundness.roots_input input.root (fun i => family.coefficients (Fin.castSucc i)) emission.1.1,
    fun i => OwnedDecompositionSoundness.roots_digit input.root (fun j => family.coefficients (Fin.castSucc j)) emission.1.1 i⟩

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [∀ factor, SampleableType ((Fin (2^(s.code factor).front) × Fin b) → K)]

/-- Native reconstruction uses the derived logical compression rate plus one
PCS error per original physical source, under the inherited final exclusion.
Only code facts remain explicit; there is no child-security or replay premise. -/
theorem original_safe_bound [NeZero b] [∀ factor, NeZero (s.code factor).m]
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*b ≤ q) (radix : ZMod q) (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin (2*d+2) → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (PaddedLinear.witness (stage s enc input family nodesEnough radix) dummy initial)}[
      PaddedLinear.OriginalRisk (stage s enc input family nodesEnough radix) dummy capacity radius outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (n : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b)) +
      ((AuthenticatedLinear.factors (2*d+2)).map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := b)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum :=
  PaddedLinear.original_safe_bound (stage s enc input family nodesEnough radix) basis dummy enough capacity radius small initial audited

end
end FormalProof4FHE.HasteBoots.KeySwitchPaddedReconstruction
