module
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonReferences
public import FormalProof4FHE.HasteBoots.StagedPrefixSafeBound
public import FormalProof4FHE.HasteBoots.CheckpointShapeTransport
@[expose] public section

/-! Comparisons reuse the successful reconstruction registry and opening memory.
Only helpers are newly committed. The scheme can be instantiated with the
private-pair middle and shared lookup continuation; heights remain per context. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSComparisonStage
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section

structure Scheme (Cfg Input Memory Helper Result : Type) (d : ℕ) where
  heights : Cfg → ℕ
  sourceTag : Fin (2*d+1) → Cfg
  helperRequests : ((Fin (2*d+1) → Digest) × Memory) → Helper → List (Cfg × Digest)
  helperCommit : ((Fin (2*d+1) → Digest) × Memory) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Helper
  next : ((Fin (2*d+1) → Digest) × Memory) → Helper →
    OracleComp (SharedSequence.Shared Cfg Input Digest) Result

variable {F Cfg Input Memory Helper Result : Type} {d : ℕ}

abbrev State (s : Scheme Cfg Input Memory Helper Result d) :=
  CheckpointExecution.State (Input := Input) (Digest := Digest)
    (fun cfg => Skeleton.perfect (s.heights cfg))

abbrev Outcome (s : Scheme Cfg Input Memory Helper Result d) :=
  (((Fin (2*d+1) → Digest) × Memory) × State s) × (Helper × State s) × (Result × State s)

def erase (s : Scheme Cfg Input Memory Helper Result d) (outcome : Outcome s) :=
  (outcome.1.1,outcome.2.1.1,outcome.2.2.1)

def sources (roots : Fin (2*d+2) → Digest) (memory : Memory) :
    (Fin (2*d+1) → Digest) × Memory :=
  (fun source => roots (PackedPBSComparisonReferences.linearSlot source),memory)

def requests (s : Scheme Cfg Input Memory Helper Result d)
    (first : (Fin (2*d+1) → Digest) × Memory) : List (Cfg × Digest) :=
  (List.finRange (2*d+1)).map (fun source => (s.sourceTag source,first.1 source))

def program (s : Scheme Cfg Input Memory Helper Result d)
    (roots : Fin (2*d+2) → Digest) (memory : Memory) :=
  StagedCommitmentPrefix.program (requests s) s.helperRequests (pure (sources roots memory))
    s.helperCommit s.next

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

def witness (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun cfg => Skeleton.perfect (s.heights cfg))) :=
  StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (s.heights cfg))
    (requests s) s.helperRequests (pure (sources roots memory)) s.helperCommit s.next initial

theorem project_witness (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun cfg => Skeleton.perfect (s.heights cfg))) :
    (fun outcome => ((outcome.1.1,outcome.2.1.1,outcome.2.2.1),outcome.2.2.2)) <$>
      witness enc dummy s roots memory initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun cfg => Skeleton.perfect (s.heights cfg))) (program s roots memory)).run initial :=
  StagedCommitmentPrefix.project_witness enc dummy _ _ _ _ _ _ initial

/-- Erasing ghost snapshots recovers the canonical shared-cache experiment. -/
theorem project_canonical (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : State s) :
    (fun outcome => (erase s outcome,outcome.2.2.2.hash.cache)) <$>
      witness enc dummy s roots memory initial =
    (simulateQ (CheckpointExecution.canonical (Cfg := Cfg) (QueryImpl.ofLift unifSpec ProbComp))
      (program s roots memory)).run initial.hash.cache := by
  have projected := congrArg (fun experiment =>
    Prod.map id (fun current : State s => current.hash.cache) <$> experiment)
    (project_witness enc dummy s roots memory initial)
  rw [Functor.map_map,CheckpointExecution.project_run] at projected
  exact projected

/-- The source registry is fixed by the reached reconstruction, before helper work. -/
theorem source_eq (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun cfg => Skeleton.perfect (s.heights cfg)))
    (outcome : _) (supported : outcome ∈ support (witness enc dummy s roots memory initial)) :
    outcome.1.1 = sources roots memory ∧ outcome.1.2 = initial := by
  simp only [witness,StagedCommitmentPrefix.witness,simulateQ_pure,StateT.run_pure,pure_bind,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨second,_,last,_,equal⟩ := supported
  subst outcome
  exact ⟨rfl,rfl⟩

/-- All actual staged returns retain the incoming audit, including rejection. -/
theorem audited (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun cfg => Skeleton.perfect (s.heights cfg)))
    (valid : CheckpointExecution.Audited enc dummy _ initial)
    (outcome : _) (supported : outcome ∈ support (witness enc dummy s roots memory initial)) :
    CheckpointExecution.Audited enc dummy _ outcome.2.2.2 :=
  StagedPrefixSafeBound.audited_witness enc dummy _ _ _ _ _ _ initial valid outcome supported


/-- An earlier collision or monitor failure survives all comparison branches. -/
theorem bad_persistent (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : State s) (bad : CheckpointCollision.Bad _ initial)
    (outcome : Outcome s) (supported : outcome ∈ support (witness enc dummy s roots memory initial)) :
    CheckpointCollision.Bad _ outcome.2.2.2 := by
  have actual : (erase s outcome,outcome.2.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (fun cfg => Skeleton.perfect (s.heights cfg))) (program s roots memory)).run initial) := by
    rw [←project_witness enc dummy s roots memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointCollision.bad_persistent_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy _
    (program s roots memory) initial bad _ actual

/-- No comparison action can remove an original recorded owner. -/
theorem retains (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : State s) (tag : Cfg)
    (entry : MerkleTreeMultiExtractability.Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (s.heights cfg))) tag)
    (recorded : ⟨tag,entry⟩ ∈ initial.checkpoints.checkpoints)
    (outcome : Outcome s) (supported : outcome ∈ support (witness enc dummy s roots memory initial)) :
    ⟨tag,entry⟩ ∈ outcome.2.2.2.checkpoints.checkpoints := by
  have actual : (erase s outcome,outcome.2.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (fun cfg => Skeleton.perfect (s.heights cfg))) (program s roots memory)).run initial) := by
    rw [←project_witness enc dummy s roots memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy _ tag entry
    (program s roots memory) initial recorded _ actual

end
end FormalProof4FHE.HasteBoots.PackedPBSComparisonStage
