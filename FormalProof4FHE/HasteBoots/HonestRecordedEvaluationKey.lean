module
public import FormalProof4FHE.HasteBoots.HonestRecordedMatrix
public import FormalProof4FHE.HasteBoots.HonestPaddedSource
public import FormalProof4FHE.HasteBoots.DecodedEvaluationKey
@[expose] public section

/-! Build evaluation-key commitment payloads from actual coefficient keys.
Their canonical retained-world inverse-NTT key equals the original key outside
the same final history exception. Native setup execution/refinement must supply
the factual query-cache and checkpoint-retention receipts. -/
namespace FormalProof4FHE.HasteBoots.HonestRecordedEvaluationKey
noncomputable section
variable {q c levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}

def evaluations (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (level : Fin levels) : NativeBlindRotation.Cipher q (2^(c+2)) :=
  fun half => BlindRotationNTT.transform (c+2) psi (original level half)

def table (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels) (level : Fin levels) :
    RecordedPaddedSource.PhysicalMatrix (parameters level) :=
  HonestPaddedSource.cipher (c := c) (lanes := 2) (parameters level).front (parameters level).suffix
    (evaluations (c := c) psi original level)

def owner (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels) (level : Fin levels) :=
  HonestRecordedMatrix.owner (parameters level) enc hash (before level) (table parameters psi original level)

def family (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels) (level : Fin levels) :=
  HonestRecordedMatrix.family (parameters level) enc hash (before level) (table parameters psi original level)

def slots (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (recorded : ∀ level, ⟨(parameters level).tag,owner parameters enc hash before psi original level⟩ ∈
      state.checkpoints.checkpoints) (level : Fin levels) :=
  RecordedSourceWorld.slot (family parameters enc hash before psi original level) state
    (fun _ => recorded level) ()

def decoded (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (recorded : ∀ level, ⟨(parameters level).tag,owner parameters enc hash before psi original level⟩ ∈
      state.checkpoints.checkpoints) :=
  DecodedEvaluationKey.key (c+2) psi primitive
    (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family state)
      enc dummy (slots parameters enc hash before psi original state recorded level))

/-- Honest encoding and commitment determine the setup transform identity;
no decoded-table equality or transform certificate is a premise. The remaining
receipts concern actual hash observations and retained checkpoints. -/
theorem decoded_eq_or_bad
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (logged : ∀ level, ∀ entry ∈ (owner parameters enc hash before psi original level).cumulativeLog,
      state.hash.cache entry.1 = some entry.2)
    (recorded : ∀ level, ⟨(parameters level).tag,owner parameters enc hash before psi original level⟩ ∈
      state.checkpoints.checkpoints)
    (enough : ∀ level, (parameters level).degree ≤ 2^H (parameters level).tag)
    (margin : ∀ level, 2*(parameters level).radius <
      Code.minDist (BlockCode.code (parameters level).domain (parameters level).degree 4 :
        Set (Fin (2^H (parameters level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters level).front+(parameters level).suffix) :
    decoded parameters enc dummy hash before psi primitive original state recorded = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr bad
  have values : ∀ level,
      PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family state) enc dummy
        (slots parameters enc hash before psi original state recorded level) = evaluations psi original level := by
    intro level
    have source := (HonestRecordedMatrix.world_logical_or_bad (parameters level) enc dummy hash (before level)
      (table parameters psi original level) state audited (logged level) (recorded level)
      (enough level) (margin level) (c+1)).resolve_right bad
    have sourceAt : RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) enc dummy (c+1)
        (slots parameters enc hash before psi original state recorded level) =
          PaddedSourceAddress.logical (c+1) (table parameters psi original level) := source
    unfold PackedCipherSource.familyCipher
    rw [sourceAt]
    unfold table
    rw [HonestPaddedSource.logical_cipher _ _ _ (fits level)]
    exact PackedCipherSource.unpack_pack _
  unfold decoded
  exact Or.inl (DecodedEvaluationKey.key_eq_of_setup (c+2) psi primitive _ original
    (fun level half => (congrFun (values level) half).symm))

/-- A verifier-selected family uses the honest key whenever its actual public
descriptor/root pairs select these constructed setup commitments. No equality
of decoded sources or transform values is supplied. Aliases are permitted. -/
theorem associated_key_eq_or_bad {Source : Type}
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (logged : ∀ level, ∀ entry ∈ (owner parameters enc hash before psi original level).cumulativeLog,
      state.hash.cache entry.1 = some entry.2)
    (recorded : ∀ level, ⟨(parameters level).tag,owner parameters enc hash before psi original level⟩ ∈
      state.checkpoints.checkpoints)
    (enough : ∀ level, (parameters level).degree ≤ 2^H (parameters level).tag)
    (margin : ∀ level, 2*(parameters level).radius <
      Code.minDist (BlockCode.code (parameters level).domain (parameters level).degree 4 :
        Set (Fin (2^H (parameters level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters level).front+(parameters level).suffix)
    (actual : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H 4)
    (actualRecorded : RecordedPaddedSourceFamily.Recorded actual state) (keySources : Fin levels → Source)
    (sameParameters : ∀ level, actual.parameters (keySources level) = parameters level)
    (sameRoots : ∀ level, actual.roots (keySources level) =
      (owner parameters enc hash before psi original level).root) :
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family state)
        enc dummy (RecordedSourceWorld.slot actual state actualRecorded (keySources level))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  have sameSlots : ∀ level,
      RecordedSourceWorld.slot actual state actualRecorded (keySources level) =
        slots parameters enc hash before psi original state recorded level := by
    intro level
    exact RecordedSourceWorld.slot_eq actual (family parameters enc hash before psi original level)
      state actualRecorded (fun _ => recorded level) (keySources level) ()
      (sameParameters level) (sameRoots level)
  rcases decoded_eq_or_bad parameters enc dummy hash before psi primitive original state audited
    logged recorded enough margin fits with equal | bad
  · left
    have values : (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2)
        (RecordedSourceWorld.family state) enc dummy
        (RecordedSourceWorld.slot actual state actualRecorded (keySources level))) =
        (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2)
          (RecordedSourceWorld.family state) enc dummy
          (slots parameters enc hash before psi original state recorded level)) := by
      funext level
      rw [sameSlots level]
    rw [values]
    exact equal
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.HonestRecordedEvaluationKey
