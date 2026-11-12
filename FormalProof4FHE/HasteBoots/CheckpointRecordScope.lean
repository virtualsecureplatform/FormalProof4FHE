module
public import FormalProof4FHE.HasteBoots.CheckpointShapeTransport
public import FormalProof4FHE.HasteBoots.RecordRoots
public import VCVio.OracleComp.Traversal
@[expose] public section

/-! Structural checkpoint scope covers every adaptive query branch, including
queries with no returning continuation. Private and hash queries are unrestricted. -/
namespace FormalProof4FHE.HasteBoots.CheckpointRecordScope
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {Cfg Input Digest Payload A B : Type} {ι : Type} {base : OracleSpec ι}

def Allowed (scope : Cfg → Prop) : (CheckpointExecution.Spec base Cfg Input Digest).Domain → Prop
  | .inl _ => True
  | .inr (.inl _) => True
  | .inr (.inr request) => scope request.1

def Scoped (scope : Cfg → Prop) (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) A) : Prop :=
  allPathsSatisfy (Allowed scope) (fun _ => True) (fun _ => Set.univ) program

theorem pure_scoped (scope : Cfg → Prop) (value : A) :
    Scoped (Input := Input) (Digest := Digest) (base := base) scope (pure value) := by
  simp [Scoped]

theorem query_bind_scoped (scope : Cfg → Prop)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (next : (CheckpointExecution.Spec base Cfg Input Digest).Range query →
      OracleComp (CheckpointExecution.Spec base Cfg Input Digest) A) :
    Scoped scope (liftM ((CheckpointExecution.Spec base Cfg Input Digest).query query) >>= next) ↔
      Allowed scope query ∧ ∀ answer, Scoped scope (next answer) := by
  simp only [Scoped,allPathsSatisfy_query_bind,Set.mem_univ,forall_const]

theorem bind_scoped (scope : Cfg → Prop)
    (first : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) A)
    (next : A → OracleComp (CheckpointExecution.Spec base Cfg Input Digest) B)
    (restricted : Scoped scope first) (following : ∀ value, Scoped scope (next value)) :
    Scoped scope (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using following value
  | query_bind query tail ih =>
    obtain ⟨allowed,children⟩ := (query_bind_scoped scope query tail).mp restricted
    rw [bind_assoc,query_bind_scoped]
    exact ⟨allowed,fun answer => ih answer (children answer)⟩

theorem map_scoped (scope : Cfg → Prop)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) A)
    (restricted : Scoped scope program) (f : A → B) : Scoped scope (f <$> program) := by
  rw [←bind_pure_comp]
  exact bind_scoped scope program _ restricted (fun _ => pure_scoped scope _)

theorem query_scoped (scope : Cfg → Prop)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (allowed : Allowed scope query) :
    Scoped scope (liftM ((CheckpointExecution.Spec base Cfg Input Digest).query query) : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) _) := by
  simpa only [bind_pure] using (query_bind_scoped scope query (fun answer => pure answer)).mpr
    ⟨allowed,fun answer => pure_scoped scope answer⟩

/-- Trusted annotations record exactly the tags listed by the caller. -/
theorem recordRoots_scoped (scope : Cfg → Prop) (roots : List (Cfg × Digest))
    (allowed : ∀ request ∈ roots, scope request.1) :
    Scoped (Input := Input) scope (RecordRoots.program roots) := by
  induction roots with
  | nil => exact pure_scoped scope ()
  | cons request rest ih =>
    apply bind_scoped scope _ _
      (query_scoped scope (.inr (.inr request)) (allowed request (List.mem_cons_self)))
    intro _
    exact ih (fun entry member => allowed entry (List.mem_cons_of_mem request member))

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- One allowed recording preserves geometry agreement on the entire history. -/
theorem compatible_step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (oldShape newShape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (allowed : Allowed (fun tag => oldShape tag = newShape tag) query)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : CheckpointShapeTransport.Compatible oldShape newShape before.checkpoints)
    (result : (CheckpointExecution.Spec base Cfg Input Digest).Range query × CheckpointExecution.State oldShape)
    (supported : result ∈ support ((CheckpointExecution.handler implBase enc dummy oldShape query).run before)) :
    CheckpointShapeTransport.Compatible oldShape newShape result.2.checkpoints := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer,before)) <$> implBase privateQuery) at supported
    rw [support_map,Set.mem_image] at supported
    obtain ⟨_,_,rfl⟩ := supported
    exact compatible
  · change result ∈ support ((fun result => (result.1,CheckpointExecution.afterHash enc dummy oldShape before result.2)) <$>
      (CachedHashHandler.handler hashQuery).run before.hash) at supported
    rw [support_map,Set.mem_image] at supported
    obtain ⟨_,_,rfl⟩ := supported
    exact compatible
  · have same := eq_of_mem_support_pure _ supported
    subst result
    exact (CheckpointShapeTransport.compatible_record oldShape newShape before.checkpoints request.1 request.2 before.hash.log).mpr
      ⟨compatible,allowed⟩

/-- Actual supported returns of a restricted prefix have compatible histories. -/
theorem compatible_run (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (oldShape newShape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) A)
    (restricted : Scoped (fun tag => oldShape tag = newShape tag) program)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : CheckpointShapeTransport.Compatible oldShape newShape before.checkpoints)
    (result : A × CheckpointExecution.State oldShape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy oldShape) program).run before)) :
    CheckpointShapeTransport.Compatible oldShape newShape result.2.checkpoints := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
    have same := eq_of_mem_support_pure _ supported
    subst result
    exact compatible
  | query_bind query next ih =>
    obtain ⟨allowed,children⟩ := (query_bind_scoped _ query next).mp restricted
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,support_bind,Set.mem_iUnion] at supported
    obtain ⟨middle,present,tail⟩ := supported
    exact ih middle.1 (children middle.1) middle.2
      (compatible_step implBase enc dummy oldShape newShape query allowed before compatible middle present) result tail

end
end FormalProof4FHE.HasteBoots.CheckpointRecordScope
