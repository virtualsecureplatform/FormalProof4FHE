module
public import FormalProof4FHE.HasteBoots.AmbientKnownInput
public import FormalProof4FHE.HasteBoots.PackedNTTBinding
@[expose] public section

/-! The canonical final key-switch public input is TWO copies of the negated
accumulator mask, in the same original coefficient/half order as its NTTs.
The root and verifier table are caller-bound; no input-authenticity certificate
is assumed. Byte/field/physical and production transcript refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchKnownInput
open OracleSpec OracleComp
open InteractiveAuthenticatedOpening
noncomputable section
variable {q log c b front suffix m queries height : ℕ} [Fact q.Prime]

/-- Matches `input_dimensions`: negate the mask and repeat it in both halves. -/
def table (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log)) :
    PackedNTTBinding.Table q (1+c) b :=
  PackedNTTBinding.pack (r := 1) length (fun _ => -accumulator false)

/-- Every source polynomial row is the canonical negated original mask. -/
theorem table_row (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log))
    (row : MatrixFold.Cube 1) :
    PackedNTTBinding.row length (table length accumulator) row = -accumulator false :=
  PackedNTTBinding.row_pack length _ row

/-- The public table is fixed at the same native addresses later NTTs use. -/
theorem table_address (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log))
    (row : MatrixFold.Cube 1) (index : Fin (2^log)) :
    table length accumulator (PackedNTTBinding.address length row index).1
      (PackedNTTBinding.address length row index).2 = -accumulator false index :=
  congrFun (table_row length accumulator row) index

variable {Input Digest Cfg Response Memory CommitMemory : Type} [DecidableEq Input] [DecidableEq Digest]
local notation "S" => AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory b (1+c) front suffix m queries height

/-- Factory commitment work and private memory are preserved. Trusted caller
inputs fix the encoding, original input root, table and consecutive nodes. -/
def stage (small : 2*b ≤ q) (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log)) (s : S) : S :=
  {s with
    encoding := enc
    nodes := NativePackedInterpolation.nodes q small
    table := table length accumulator
    commit := do
      let original ← s.commit
      pure ((fun _ => root),original.2)}

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The opening's expected value comes from this fixed verifier table. -/
theorem expected_value (small : 2*b ≤ q) (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log)) (s : S)
    (emission : (Unit → Digest) × CommitMemory)
    (packet : PackedSumcheckSubclaim.Query (ZMod q) b (1+c) × Memory) :
    (AmbientKnownInput.build (stage small enc root length accumulator s) emission packet).value () =
      packet.1.fold (table length accumulator) := rfl

variable [SampleableType Digest] [SampleableType (Fin b → ZMod q)]
  [SampleableType (TestMatrix (ZMod q) (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]

/-- Actual native opening executions retain the original caller input root,
including executions whose own workers reject. -/
theorem witness_root (small : 2*b ≤ q) (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log)) (s : S)
    (heights : Cfg → ℕ) (dummy : Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := 1+c) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AmbientKnownInput.witness heights (stage small enc root length accumulator s) dummy initial)) :
    outcome.1.1.1 () = root := by
  simp only [AmbientKnownInput.witness,MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,_,equal⟩ := supported
  subst outcome
  simp only [stage,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at firstSupported
  obtain ⟨original,_,same⟩ := firstSupported
  subst first
  rfl

/-- A wrong original coefficient row of an accepted input produces the
bounded original-owner event. Root identity follows from actual stage support;
only structural owner membership and its caller-root identity are supplied. -/
theorem accepted_wrong_row_implies_original (small : 2*b ≤ q)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log)) (s : S)
    (heights : Cfg → ℕ) (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := b) (n := 1+c) (front := front) (queries := queries) (height := height))
    (supported : outcome ∈ support (AmbientKnownInput.witness heights (stage small enc root length accumulator s) dummy initial))
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag) (sameRoot : owner.root = root)
    (recorded : ⟨s.tag,owner⟩ ∈ outcome.2.2.checkpoints.checkpoints) (row : MatrixFold.Cube 1)
    (wrong : PackedNTTBinding.row length
      (AmbientKnownInput.originalSource heights (stage small enc root length accumulator s) dummy capacity radius owner) row ≠ -accumulator false)
    (accepted : outcome.2.1.2.accepted = true) :
    AmbientKnownInput.OriginalRisk heights (stage small enc root length accumulator s) dummy capacity radius outcome := by
  have boundRoot := witness_root small enc root length accumulator s heights dummy initial outcome supported
  refine ⟨owner,sameRoot.trans boundRoot.symm,recorded,?_,accepted⟩
  intro equal
  apply wrong
  change AmbientKnownInput.originalSource heights (stage small enc root length accumulator s) dummy capacity radius owner = table length accumulator at equal
  rw [equal]
  exact table_row length accumulator row

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2^front) × Fin b) → K)]

/-- The caller-owned negative-mask input has derived native soundness on the
inherited ambient state. Only code/layout facts remain explicit; there is no
input-authenticity or PCS-security hypothesis and no local hash charge. -/
theorem original_safe_bound [NeZero m] [NeZero b] (small : 2*b ≤ q)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (length : 2^c*b = 2^log) (accumulator : NativeBlindRotation.Cipher q (2^log)) (s : S)
    (heights : Cfg → ℕ) (geometry : heights s.tag = height) (basis : Module.Basis (Fin b) (ZMod q) K) (dummy : Digest)
    (enough : m ≤ Fintype.card (Fin (2^height))) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (distance : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) s.domain) m : Set (Fin (2^height) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (AmbientKnownInput.witness heights (stage small enc root length accumulator s) dummy initial)}[
      AmbientKnownInput.OriginalRisk heights (stage small enc root length accumulator s) dummy capacity radius outcome ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((1+c : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) s.domain radius :=
  AmbientKnownInput.original_safe_bound heights (stage small enc root length accumulator s) geometry basis dummy enough capacity radius distance initial audited

end
end FormalProof4FHE.HasteBoots.KeySwitchKnownInput
