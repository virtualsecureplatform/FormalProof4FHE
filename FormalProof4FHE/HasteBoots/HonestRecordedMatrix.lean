module
public import FormalProof4FHE.HasteBoots.HonestMerkleTranscript
public import FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
@[expose] public section

/-! Encode actual setup matrices, commit their whole-column payloads, and recover
their contents through the verifier's existing frozen-source decoder. Decoding
truth follows from construction and the unique-radius condition. -/
namespace FormalProof4FHE.HasteBoots.HonestRecordedMatrix
open BinaryTree OracleSpec OracleComp
noncomputable section
variable {F Cfg Input Digest : Type} [Field F]
  {H : Cfg → ℕ} {b : ℕ}

def encoded (p : RecordedPaddedSource.Parameters F Cfg H b)
    (table : RecordedPaddedSource.PhysicalMatrix p) :=
  MatrixOpeningCompleteness.encodedTable (m := p.degree) p.domain table

/-- Preserve the native row/lane/channel order in every whole-column payload. -/
def column (p : RecordedPaddedSource.Parameters F Cfg H b)
    (table : RecordedPaddedSource.PhysicalMatrix p) (position : Fin (2^H p.tag)) : List F :=
  NativeColumnLayout.packPayload (fun address : Fin (((2^p.front)*b)*b) =>
    let pair : Fin ((2^p.front)*b) × Fin b := finProdFinEquiv.symm address
    let row : Fin (2^p.front) × Fin b := finProdFinEquiv.symm pair.1
    encoded p table position row pair.2)

def leaves (p : RecordedPaddedSource.Parameters F Cfg H b)
    (table : RecordedPaddedSource.PhysicalMatrix p) : LeafData (List F) (.perfect (H p.tag)) :=
  LeafData.ofFun _ (fun index => column p table ((SkeletonLeafIndex.perfectEquiv (H p.tag)).symm index))

/-- The owner's root and cumulative log are computed from the honest builder. -/
def owner (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p) : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) p :=
  let labels := HonestMerkleTranscript.tree enc hash (leaves p table)
  ⟨labels.getRootValue,before ++ HonestMerkleTranscript.queries enc (leaves p table) labels⟩

def family (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p) :
    RecordedPaddedSourceFamily.Family F Cfg Input Digest Unit H b where
  parameters := fun _ => p
  roots := fun _ => (owner p enc hash before table).root
  owners := fun _ => owner p enc hash before table
  ownerRoots := fun _ => rfl

/-- Both fields are exactly those returned by the actual effectful builder
under the deterministic hash interpreter; no independent root/log is supplied. -/
theorem owner_run (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p) :
    let built := (simulateQ (HonestMerkleTranscript.handler hash)
      (HonestMerkleTranscript.program enc (leaves p table))).run before
    owner p enc hash before table = ⟨built.1.getRootValue,built.2⟩ := by
  rw [HonestMerkleTranscript.run]
  rfl

variable [DecidableEq Digest]

theorem word (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn (owner p enc hash before table).cumulativeLog) :
    AmbientMatrixSource.word (front := p.front) (b := b) (height := H p.tag)
      enc dummy H p.tag (owner p enc hash before table) = encoded p table := by
  funext position row channel
  have recovered := HonestMerkleTranscript.word_recovered enc dummy [] (H p.tag) (leaves p table)
    (HonestMerkleTranscript.tree enc hash (leaves p table))
    (owner p enc hash before table).cumulativeLog injective
    (fun entry member => List.mem_append_right before member) position
  have value : MerkleAvailability.word enc dummy [] (H p.tag)
      (owner p enc hash before table).cumulativeLog (owner p enc hash before table).root position =
      column p table position := by
    simpa only [leaves,LeafData.get_ofFun,Equiv.symm_apply_apply,owner] using recovered
  change NativeColumnLayout.unpackPayload (((2^p.front)*b)*b)
    (MerkleAvailability.word enc dummy [] (H p.tag) (owner p enc hash before table).cumulativeLog
      (owner p enc hash before table).root position)
    (NativeColumnLayout.payloadAddress (finProdFinEquiv row) channel) = _
  rw [value]
  simp only [column,NativeColumnLayout.unpack_packPayload,NativeColumnLayout.payloadAddress,
    Equiv.symm_apply_apply]

variable [DecidableEq F] [NeZero b]

/-- The fixed query-independent matrix decoder returns the committed setup
matrix, for any admitted unique radius, not only radius zero. -/
theorem decoded (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn (owner p enc hash before table).cumulativeLog)
    (enough : p.degree ≤ 2^H p.tag)
    (margin : 2*p.radius < Code.minDist (BlockCode.code p.domain p.degree b :
      Set (Fin (2^H p.tag) → Fin b → F))) :
    RecordedPaddedSource.decoded p enc dummy (owner p enc hash before table) = table := by
  unfold RecordedPaddedSource.decoded
  rw [word p enc dummy hash before table injective]
  exact MatrixOpeningCompleteness.extract p.domain (by simpa only [Fintype.card_fin] using enough)
    p.capacity p.radius margin table

theorem logical (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn (owner p enc hash before table).cumulativeLog)
    (enough : p.degree ≤ 2^H p.tag)
    (margin : 2*p.radius < Code.minDist (BlockCode.code p.domain p.degree b :
      Set (Fin (2^H p.tag) → Fin b → F))) (arity : ℕ) :
    RecordedPaddedSource.logical p enc dummy arity (owner p enc hash before table) =
      PaddedSourceAddress.logical arity table := by
  unfold RecordedPaddedSource.logical
  rw [decoded p enc dummy hash before table injective enough margin]

variable [DecidableEq Input]

/-- Actual setup-query cache facts and a recorded owner identify the final
constructed source world. Collision freedom is discharged by the same final
Bad disjunction, rather than supplied as a separate security certificate. -/
theorem world_logical_or_bad (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (hash : Input → Digest)
    (before : MerkleTreeExtractor.QueryLog Input Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (logged : ∀ entry ∈ (owner p enc hash before table).cumulativeLog,
      state.hash.cache entry.1 = some entry.2)
    (recorded : ⟨p.tag,owner p enc hash before table⟩ ∈ state.checkpoints.checkpoints)
    (enough : p.degree ≤ 2^H p.tag)
    (margin : 2*p.radius < Code.minDist (BlockCode.code p.domain p.degree b :
      Set (Fin (2^H p.tag) → Fin b → F))) (arity : ℕ) :
    RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family (F := F) (b := b) state) enc dummy arity
      (RecordedSourceWorld.slot (family p enc hash before table) state (fun _ => recorded) ()) =
      PaddedSourceAddress.logical arity table ∨
        CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr bad
  have injective := MerkleTreeExtractability.responseInjectiveOn_of_cache_noCollision
    (owner p enc hash before table).cumulativeLog state.hash.cache logged
    (fun collision => bad (Or.inr collision))
  have honest := logical p enc dummy hash before table injective enough margin arity
  have same := (RecordedSourceWorld.logical_eq_or_bad (family p enc hash before table)
    enc dummy arity state audited (fun _ => recorded)).resolve_right bad
  exact Or.inl ((congrFun same ()).symm.trans honest)

end
end FormalProof4FHE.HasteBoots.HonestRecordedMatrix
