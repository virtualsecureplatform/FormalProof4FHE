module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
public import FormalProof4FHE.HasteBoots.KeySwitchKnownInput
public import FormalProof4FHE.HasteBoots.FixedHeightPaddedSource
@[expose] public section

/-! The actual known-input check fixes the decoded final key-switch input to
two copies of the negated retained accumulator mask. Logical high-zero padding
is preserved by the existing adapter; no input source-value witness is used. -/
namespace FormalProof4FHE.HasteBoots.DecodedKnownInput
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c lanes front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest]

variable (s : AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
  (2^lanes) (1+c) front suffix m queries height)

/-- Construct both polynomial halves from the retained logical source. -/
def cipher (heights : Cfg → ℕ) (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag) :=
  PackedCipherSource.ofRows (AmbientKnownInput.originalSource heights s dummy capacity radius owner)

omit [DecidableEq Input] in
/-- Clearing the original-owner event forces equality to the verifier's known
table for an accepted check, without a claimed source interpretation. -/
theorem source_of_not_risk (heights : Cfg → ℕ) (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := 2^lanes) (n := 1+c) (front := front) (queries := queries) (height := height))
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag)
    (ownerRoot : owner.root = outcome.1.1.1 ())
    (ownerRecorded : ⟨s.tag,owner⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : outcome.2.1.2.accepted = true)
    (clear : ¬AmbientKnownInput.OriginalRisk heights s dummy capacity radius outcome) :
    AmbientKnownInput.originalSource heights s dummy capacity radius owner = s.table := by
  by_contra wrong
  exact clear ⟨owner,ownerRoot,ownerRecorded,wrong,passes⟩

omit [DecidableEq Input] in
/-- The caller-bound native input has exactly the two negative-mask polynomial
halves expected by canonical key switching, derived from the actual check. -/
theorem negative_mask_of_not_risk (small : 2*(2^lanes) ≤ q)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (accumulator : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (heights : Cfg → ℕ) (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := 2^lanes) (n := 1+c) (front := front) (queries := queries) (height := height))
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag)
    (ownerRoot : owner.root = outcome.1.1.1 ())
    (ownerRecorded : ⟨s.tag,owner⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : outcome.2.1.2.accepted = true)
    (clear : ¬AmbientKnownInput.OriginalRisk heights
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome)
    (half : Bool) :
    cipher (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
      heights dummy capacity radius owner half = -accumulator false := by
  have same := source_of_not_risk (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
    heights dummy capacity radius outcome owner ownerRoot ownerRecorded passes clear
  have row := congrArg (fun table => PackedNTTBinding.row (r := 1) (Nat.pow_add 2 c lanes).symm table (half,())) same
  change PackedNTTBinding.row (Nat.pow_add 2 c lanes).symm
      (AmbientKnownInput.originalSource heights
        (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius owner) (half,()) =
    PackedNTTBinding.row (Nat.pow_add 2 c lanes).symm (KeySwitchKnownInput.table (Nat.pow_add 2 c lanes).symm accumulator) (half,()) at row
  erw [KeySwitchKnownInput.table_row] at row
  exact (PackedCipherSource.flatten_rows _ half).symm.trans row
/-- Normalize the fixed-height public-input descriptor to the actual ambient
context height; only public geometry is transported. -/
def parameters (heights : Cfg → ℕ) (geometry : heights s.tag = height)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ) :
    RecordedPaddedSource.Parameters (ZMod q) Cfg heights (2^lanes) :=
  FixedHeightPaddedSource.parameters (front := front) s.tag geometry s.domain capacity radius

omit [DecidableEq Input] in
/-- The literal known-input source uses the same canonical decoder/address view. -/
theorem source_eq_logical (heights : Cfg → ℕ) (geometry : heights s.tag = height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag) :
    AmbientKnownInput.originalSource heights s dummy capacity radius owner =
      RecordedPaddedSource.logical (parameters s heights geometry capacity radius) s.encoding dummy (1+c) owner :=
  FixedHeightPaddedSource.padded_eq_logical s.encoding dummy s.tag geometry s.domain capacity radius s.padding s.dimensions owner

variable {Index : Type} {heights : Cfg → ℕ}

/-- The caller's retained input source has the same coefficient-domain family
value as later stages under public descriptor and recorded-root association. -/
theorem cipher_family_eq_or_bad
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (geometry : heights s.tag = height)
    (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (associated : parameters s heights geometry capacity radius = world.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag)
    (ownerRetained : ⟨s.tag,owner⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : owner.root = world.roots index) :
    cipher s heights dummy capacity radius owner = PackedCipherSource.familyCipher (c := c) world s.encoding dummy index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have compared := RecordedPaddedSourceFamily.associated_owner_agrees_or_bad world s.encoding dummy (1+c) index
    (parameters s heights geometry capacity radius) associated state audited worldRecorded owner ownerRetained ownerRoot
  rcases compared with same | bad
  · left
    unfold cipher
    rw [source_eq_logical s heights geometry,same,PackedCipherSource.ofRows_family]
  · exact Or.inr bad
/-- The executed known-input constraint fixes both polynomial halves of the
common family input under the same final exclusion as the later stages. -/
theorem negative_mask_family_of_not_risk (small : 2*(2^lanes) ≤ q)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
    (accumulator : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (heights : Cfg → ℕ) (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
      AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
        (b := 2^lanes) (n := 1+c) (front := front) (queries := queries) (height := height))
    (owner : AmbientMatrixSource.Snapshot Input Digest heights s.tag)
    (ownerRoot : owner.root = outcome.1.1.1 ())
    (ownerRecorded : ⟨s.tag,owner⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : outcome.2.1.2.accepted = true)
    (clear : ¬AmbientKnownInput.OriginalRisk heights
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (geometry : heights s.tag = height)
    (associated : parameters (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
      heights geometry capacity radius = world.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (ownerRetained : ⟨s.tag,owner⟩ ∈ state.checkpoints.checkpoints)
    (worldRoot : owner.root = world.roots index)
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state) :
    ∀ half, PackedCipherSource.familyCipher (c := c) world enc dummy index half = -accumulator false := by
  have same := (cipher_family_eq_or_bad
    (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
    world index geometry dummy capacity radius associated state audited worldRecorded owner ownerRetained worldRoot).resolve_right noBad
  change cipher (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
    heights dummy capacity radius owner = PackedCipherSource.familyCipher (c := c) world enc dummy index at same
  intro half
  rw [←same]
  exact negative_mask_of_not_risk s small enc root accumulator heights dummy capacity radius outcome owner ownerRoot ownerRecorded passes clear half

end
end FormalProof4FHE.HasteBoots.DecodedKnownInput
