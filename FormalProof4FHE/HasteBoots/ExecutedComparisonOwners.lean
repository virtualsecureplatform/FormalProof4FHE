module
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonStage
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! Literal original-source owners in an actually executed comparison, recorded
before any adaptive helper work and retained through every returned path. -/
namespace FormalProof4FHE.HasteBoots.ExecutedComparisonOwners
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
open PackedPBSComparisonStage
noncomputable section
variable {F Cfg Input Memory Helper Result : Type} {d : ℕ}

/-- The original source uses the incoming log frozen before helper work. -/
def owners (s : Scheme Cfg Input Memory Helper Result d) (outcome : Outcome s)
    (source : Fin (2*d+1)) : AmbientMatrixSource.Snapshot Input Digest s.heights (s.sourceTag source) :=
  ⟨outcome.1.1.1 source,outcome.1.2.hash.log⟩

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

theorem recorded (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (s : Scheme Cfg Input Memory Helper Result d) (roots : Fin (2*d+2) → Digest) (memory : Memory)
    (initial : State s) (outcome : Outcome s)
    (supported : outcome ∈ support (witness enc dummy s roots memory initial)) (source : Fin (2*d+1)) :
    ⟨s.sourceTag source,owners s outcome source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints := by
  simp only [witness,StagedCommitmentPrefix.witness,simulateQ_pure,StateT.run_pure,pure_bind,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨second,secondSupported,last,lastSupported,equal⟩ := supported
  subst outcome
  have earlier := RecordRoots.recorded (fun cfg => Skeleton.perfect (s.heights cfg))
    (requests s (sources roots memory)) initial (s.sourceTag source,(sources roots memory).1 source)
    (List.mem_map_of_mem (List.mem_finRange source))
  have middle := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (fun cfg => Skeleton.perfect (s.heights cfg)) (s.sourceTag source)
    (owners s ((sources roots memory,initial),second,last) source)
    (s.helperCommit (sources roots memory)) (RecordRoots.state _ (requests s (sources roots memory)) initial)
    earlier second secondSupported
  have later := RecordRoots.retains _ (s.helperRequests (sources roots memory) second.1) second.2 _ _ middle
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy _
    (s.sourceTag source) (owners s ((sources roots memory,initial),second,last) source)
    (s.next (sources roots memory) second.1) (RecordRoots.state _ (s.helperRequests (sources roots memory) second.1) second.2)
    later last lastSupported

end
end FormalProof4FHE.HasteBoots.ExecutedComparisonOwners
