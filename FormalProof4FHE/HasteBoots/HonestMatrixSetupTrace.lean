module
public import FormalProof4FHE.HasteBoots.SharedHashLog
public import FormalProof4FHE.HasteBoots.HonestRecordedMatrix
@[expose] public section

/-! Honest setup performs real shared hash calls and returns every label tree.
Root recording is left to the native source stage, at its actual geometry. -/
namespace FormalProof4FHE.HasteBoots.HonestMatrixSetupTrace
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Cfg Input Digest : Type} {H : Cfg → ℕ} {b : ℕ}
  {ι : Type} {base : OracleSpec ι}

section Construction
variable [Field F]

/-- Build all honest matrices without introducing setup checkpoint annotations. -/
def program (enc : MerkleOracle.Encoding Input Digest (List F)) :
    {n : ℕ} → (parameters : Fin n → RecordedPaddedSource.Parameters F Cfg H b) →
    ((i : Fin n) → RecordedPaddedSource.PhysicalMatrix (parameters i)) →
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      ((i : Fin n) → FullData Digest (Skeleton.perfect (H (parameters i).tag)))
  | 0, _, _ => pure (fun i => i.elim0)
  | n+1, parameters, tables => do
      let first ← ExecutedHonestCommitment.program enc (HonestRecordedMatrix.leaves (parameters 0) (tables 0))
      let rest ← program enc (fun i : Fin n => parameters i.succ) (fun i => tables i.succ)
      pure (Fin.cases first rest)

end Construction

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Hash-only Merkle construction does not record or remove checkpoints. -/
theorem builder_checkpoints (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    {s : Skeleton} (payloads : LeafData (List F) s)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : FullData Digest s × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (ExecutedHonestCommitment.program enc payloads)).run state)) :
    result.2.checkpoints = state.checkpoints := by
  induction payloads generalizing state with
  | leaf payload =>
      simp only [ExecutedHonestCommitment.program, AddressedMerkleTree.buildMerkleTreeAddressedM, simulateQ_map,
        StateT.run_map, simulateQ_spec_query, support_map, Set.mem_image] at supported
      obtain ⟨answer, answerSupported, equal⟩ := supported
      subst result
      change answer ∈ support ((fun next => (next.1, CheckpointExecution.afterHash enc dummy shape state next.2)) <$>
        (CachedHashHandler.handler (enc.leaf () payload)).run state.hash) at answerSupported
      rw [support_map, Set.mem_image] at answerSupported
      obtain ⟨next, nextSupported, equal⟩ := answerSupported
      subst answer
      rfl
  | internal left right ihLeft ihRight =>
      simp only [ExecutedHonestCommitment.program, AddressedMerkleTree.buildMerkleTreeAddressedM, simulateQ_bind,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind,
        support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
      obtain ⟨l, lSupported, r, rSupported, root, rootSupported, equal⟩ := supported
      subst result
      have leftLog := ihLeft state l lSupported
      have rightLog := ihRight l.2 r rSupported
      simp only [simulateQ_spec_query] at rootSupported
      change root ∈ support ((fun next => (next.1, CheckpointExecution.afterHash enc dummy shape r.2 next.2)) <$>
        (CachedHashHandler.handler (enc.node () (l.1.getRootValue,r.1.getRootValue))).run r.2.hash) at rootSupported
      rw [support_map, Set.mem_image] at rootSupported
      obtain ⟨next, nextSupported, equal⟩ := rootSupported
      subst root
      exact rightLog.trans leftLog

variable [Field F]

/-- All per-level setup queries are in the actual shared log, even when the
execution history's extraction geometry differs from the key geometry. -/
theorem queries_logged (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    {n : ℕ} (parameters : Fin n → RecordedPaddedSource.Parameters F Cfg H b)
    (tables : (i : Fin n) → RecordedPaddedSource.PhysicalMatrix (parameters i))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : ((i : Fin n) → FullData Digest (Skeleton.perfect (H (parameters i).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program enc parameters tables)).run state)) :
    ∀ i, ∀ entry ∈ HonestMerkleTranscript.queries enc (HonestRecordedMatrix.leaves (parameters i) (tables i)) (result.1 i),
      entry ∈ result.2.hash.log := by
  induction n generalizing state with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      simp only [program, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
      obtain ⟨first, firstSupported, rest, restSupported, equal⟩ := supported
      subst result
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro entry member
        have trace := ExecutedHonestCommitment.transcript impl enc dummy shape
          (HonestRecordedMatrix.leaves (parameters 0) (tables 0)) state first firstSupported
        have logged : entry ∈ first.2.hash.log := by
          rw [trace]
          exact List.mem_append_right _ member
        exact (SharedHashLog.run impl enc dummy shape
          (program enc (fun i : Fin n => parameters i.succ) (fun i => tables i.succ))
          first.2 rest restSupported).sublist.subset logged
      · exact ih (fun i : Fin n => parameters i.succ) (fun i => tables i.succ) first.2 rest restSupported j

/-- Native stages remain the only source checkpoint annotations. -/
theorem checkpoints (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    {n : ℕ} (parameters : Fin n → RecordedPaddedSource.Parameters F Cfg H b)
    (tables : (i : Fin n) → RecordedPaddedSource.PhysicalMatrix (parameters i))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : ((i : Fin n) → FullData Digest (Skeleton.perfect (H (parameters i).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program enc parameters tables)).run state)) :
    result.2.checkpoints = state.checkpoints := by
  induction n generalizing state with
  | zero =>
      change result ∈ support (pure ((fun i => i.elim0),state) : ProbComp _) at supported
      have equal := eq_of_mem_support_pure _ supported
      subst result
      rfl
  | succ n ih =>
      simp only [program, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
      obtain ⟨first, firstSupported, rest, restSupported, equal⟩ := supported
      subst result
      have firstHistory := builder_checkpoints impl enc dummy shape
        (HonestRecordedMatrix.leaves (parameters 0) (tables 0)) state first firstSupported
      have restHistory := ih (fun i : Fin n => parameters i.succ) (fun i => tables i.succ)
        first.2 rest restSupported
      exact restHistory.trans firstHistory

end
end FormalProof4FHE.HasteBoots.HonestMatrixSetupTrace
