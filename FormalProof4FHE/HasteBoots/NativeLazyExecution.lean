module

public import FormalProof4FHE.HasteBoots.NativeLazyIndexExecution
public import FormalProof4FHE.HasteBoots.NativeShakeProjection
public import FormalProof4FHE.HasteBoots.JointHashKernel

@[expose] public section

/-! Literal decomposition of the existing shared lazy interpreter.
This projects its value and complete native log, while all byte/hash state is
threaded through the actual compiled execution. These are code equalities,
not assumptions about independent future oracle answers. -/
namespace FormalProof4FHE.HasteBoots.NativeLazyExecution
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeShakeCache (Cache)
open OracleSpec OracleComp

noncomputable section
variable {Cfg Payload A : Type}

def execute (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ProbComp (A × List Observation) :=
  (fun result => result.1.1) <$> (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    ((NativeLazyProgram.compile program).run cache)).run state

theorem execute_read (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.read input offset count next) cache state = (do
      let first ← NativeShakeReadLaw.sample input offset count cache
      let rest ← execute enc dummy shape (next first.1) first.2 state
      pure (NativeCheckpointProgram.prepend (.output input offset first.1) rest)) := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_bind,simulateQ_bind,StateT.run_bind,
    NativeShakeReadLaw.shared_read,StateT.run_map,simulateQ_map,Functor.map_map,bind_map_left,
    map_bind,bind_pure_comp]

theorem hash_step (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ((CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (.inr (.inl input))).run state =
      (fun digest => (digest,CheckpointExecution.afterHash enc dummy shape state
        (JointHashCache.record state.hash (.hash input (List.ofFn digest))))) <$>
          JointHashKernel.answer state.hash input := by
  change (fun result => (result.1,CheckpointExecution.afterHash enc dummy shape state result.2)) <$>
    (CachedHashHandler.handler input).run state.hash = _
  rw [← JointHashKernel.handler_normalize state.hash input]
  simp only [JointHashKernel.answer,JointHashKernel.normalize,Functor.map_map]

theorem execute_hash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input) (next : Digest → OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.hash input next) cache state = (do
      let digest ← JointHashKernel.answer state.hash input
      let rest ← execute enc dummy shape (next digest) cache
        (CheckpointExecution.afterHash enc dummy shape state
          (JointHashCache.record state.hash (.hash input (List.ofFn digest))))
      pure (NativeCheckpointProgram.prepend (.hash input (List.ofFn digest)) rest)) := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_bind,StateT.run_liftM,simulateQ_bind,simulateQ_map,simulateQ_spec_query,
    StateT.run_bind,StateT.run_map,Functor.map_map,map_bind,bind_map_left,bind_pure_comp]
  rw [hash_step enc dummy shape input state]
  simp only [bind_map_left]


theorem execute_pure (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (value : A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.pure value) cache state = pure (value,[]) := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_pure,simulateQ_pure,map_pure]

theorem execute_start (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input) (next : OracleProgram.Program A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.start input next) cache state =
      NativeCheckpointProgram.prepend (.start input) <$> execute enc dummy shape next cache state := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_map,simulateQ_map,Functor.map_map]


/-- Project the actual retained byte cache as well as the value/log. -/
def executeWithCache (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ProbComp ((A × List Observation) × Cache) :=
  Prod.fst <$> (simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    ((NativeLazyProgram.compile program).run cache)).run state

/-- The owned final byte cache is reconstructed from the literal executed log,
including repeats and overlaps. This equality uses supported executions of the
actual shared handler, without replacing its state or future oracle. -/
theorem executeWithCache_records (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    executeWithCache enc dummy shape program cache state =
      (fun packet => (packet,packet.2.foldl NativeShakeHistory.record cache)) <$>
        execute enc dummy shape program cache state := by
  unfold executeWithCache execute
  rw [Functor.map_map,← bind_pure_comp,← bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result possible
  congr 1
  exact Prod.ext rfl (NativeShakeHistory.simulated_records _ program cache state result possible)

end
end FormalProof4FHE.HasteBoots.NativeLazyExecution
