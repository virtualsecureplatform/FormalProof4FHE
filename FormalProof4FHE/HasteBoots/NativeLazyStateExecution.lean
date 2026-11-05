module

public import FormalProof4FHE.HasteBoots.NativeLazyExecutionLaw
@[expose] public section

/-! Exact full-state execution of causal mixed-oracle programs. The owned byte
cache, canonical hash cache and passive monitor are reconstructed from the
complete executed log. This syntax issues no checkpoint-registration query,
so the initial checkpoint registry is preserved. Infinite execution and
native scheduler/registration refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeLazyStateExecution
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeShakeCache (Cache)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section
variable {Cfg Payload A : Type}

/-- Replay the actual shared-handler state update of one native observation. -/
def record (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Observation → CheckpointExecution.State (Input := Input) (Digest := Digest) shape
  | .hash input digest => CheckpointExecution.afterHash enc dummy shape state
      (JointHashCache.record state.hash (.hash input digest))
  | _ => state

/-- The actual compiled execution, retaining both caches and the full shared state. -/
def execute (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :=
  (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
    ((NativeLazyProgram.compile program).run cache)).run state

/-- Prefix a native observation without changing either retained state. -/
def prepend {shape : Cfg → BinaryTree.Skeleton} (entry : Observation)
    (result : ((A × List Observation) × Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ((A × List Observation) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape :=
  ((NativeCheckpointProgram.prepend entry result.1.1,result.1.2),result.2)

theorem execute_pure (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (value : A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.pure value) cache state = pure (((value,[]),cache),state) := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_pure,simulateQ_pure]

theorem execute_start (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input) (next : OracleProgram.Program A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.start input next) cache state =
      prepend (.start input) <$> execute enc dummy shape next cache state := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_map,simulateQ_map]
  rfl

theorem execute_read (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.read input offset count next) cache state = (do
      let first ← NativeShakeReadLaw.sample input offset count cache
      let rest ← execute enc dummy shape (next first.1) first.2 state
      pure (prepend (.output input offset first.1) rest)) := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_bind,simulateQ_bind,
    NativeShakeReadLaw.shared_read,StateT.run_map,simulateQ_map,bind_map_left]
  simp only [bind_pure_comp,prepend]

theorem execute_hash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input) (next : Digest → OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape (.hash input next) cache state = (do
      let digest ← JointHashKernel.answer state.hash input
      let rest ← execute enc dummy shape (next digest) cache
        (record enc dummy shape state (.hash input (List.ofFn digest)))
      pure (prepend (.hash input (List.ofFn digest)) rest)) := by
  simp only [execute,NativeLazyProgram.compile,StateT.run_bind,StateT.run_liftM,
    simulateQ_bind,simulateQ_map,simulateQ_spec_query,StateT.run_map]
  rw [NativeLazyExecution.hash_step enc dummy shape input state]
  simp only [bind_map_left,simulateQ_pure,StateT.run_pure,bind_pure_comp,prepend,record]

/-- Every supported actual execution has exactly the state obtained by folding its full log. -/
theorem shared_records (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : ((A × List Observation) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape program cache state)) :
    result.2 = result.1.1.2.foldl (record enc dummy shape) state := by
  induction program generalizing cache state result with
  | pure value =>
    rw [execute_pure] at possible
    have same := eq_of_mem_support_pure _ possible
    subst result
    rfl
  | start input next ih =>
    rw [execute_start,support_map,Set.mem_image] at possible
    obtain ⟨rest,possible,rfl⟩ := possible
    simpa only [prepend,NativeCheckpointProgram.prepend,List.foldl_cons,record] using ih cache state rest possible
  | read input offset count next ih =>
    rw [execute_read,mem_support_bind_iff] at possible
    obtain ⟨first,_,possible⟩ := possible
    rw [bind_pure_comp,support_map,Set.mem_image] at possible
    obtain ⟨rest,possible,rfl⟩ := possible
    simpa only [prepend,NativeCheckpointProgram.prepend,List.foldl_cons,record] using ih first.1 first.2 state rest possible
  | hash input next ih =>
    rw [execute_hash,mem_support_bind_iff] at possible
    obtain ⟨digest,_,possible⟩ := possible
    rw [bind_pure_comp,support_map,Set.mem_image] at possible
    obtain ⟨rest,possible,rfl⟩ := possible
    simpa only [prepend,NativeCheckpointProgram.prepend,List.foldl_cons] using
      ih digest cache (record enc dummy shape state (.hash input (List.ofFn digest))) rest possible


/-- The reconstructed shared hash state is the canonical native hash-log fold. -/
theorem fold_hash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (log : List Observation)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (log.foldl (record enc dummy shape) state).hash = log.foldl JointHashCache.record state.hash := by
  induction log generalizing state with
  | nil => rfl
  | cons entry log ih =>
    rw [List.foldl_cons,List.foldl_cons,ih]
    cases entry <;> rfl

/-- Mixed read/hash programs do not issue checkpoint-registration queries. -/
theorem fold_checkpoints (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (log : List Observation)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (log.foldl (record enc dummy shape) state).checkpoints = state.checkpoints := by
  induction log generalizing state with
  | nil => rfl
  | cons entry log ih =>
    rw [List.foldl_cons,ih]
    cases entry <;> rfl

/-- The passive failure flag remains set even if later hashes repair source stability. -/
theorem fold_failed (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (log : List Observation)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (failed : state.failed = true) :
    (log.foldl (record enc dummy shape) state).failed = true := by
  induction log generalizing state with
  | nil => exact failed
  | cons entry log ih =>
    rw [List.foldl_cons]
    apply ih
    cases entry <;> simp [record,CheckpointExecution.afterHash,failed]

/-- An initial history supplies the final canonical hash cache of the whole extended history. -/
theorem fold_project (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (before log : List Observation)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project before) :
    (log.foldl (record enc dummy shape) state).hash = JointHashCache.project (before++log) := by
  simp only [fold_hash,hashStart,JointHashCache.project,List.foldl_append]

/-- The actual full-state computation equals deterministic reconstruction from its value and complete log. -/
theorem execute_records (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape program cache state =
      (fun packet => ((packet,packet.2.foldl NativeShakeHistory.record cache),
        packet.2.foldl (record enc dummy shape) state)) <$>
          NativeLazyExecution.execute enc dummy shape program cache state := by
  calc _ = (fun result => result) <$> execute enc dummy shape program cache state := by simp
       _ = _ := by
        unfold NativeLazyExecution.execute
        rw [Functor.map_map,← bind_pure_comp,← bind_pure_comp]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro result possible
        congr 1
        exact Prod.ext (Prod.ext rfl (NativeShakeHistory.simulated_records _ program cache state result possible))
          (shared_records enc dummy shape program cache state result possible)


/-- The full shared state is recovered from the actual value/log/owned-cache execution. -/
theorem execute_with_cache (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape program cache state =
      (fun result => (result,result.1.2.foldl (record enc dummy shape) state)) <$>
        NativeLazyExecution.executeWithCache enc dummy shape program cache state := by
  rw [execute_records,NativeLazyExecution.executeWithCache_records,Functor.map_map]

/-- Exact conditional event probability including both final caches, checkpoints and the passive monitor. -/
theorem state_law {P : Type} (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : ((A × List Observation) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | event (((OracleProgram.run program other).run,
        NativeShakeKernel.observed ((past other).run.2 ++ (OracleProgram.run program other).run.2) other),
        (OracleProgram.run program other).run.2.foldl (record enc dummy shape) state)} =
      Pr{let result ← (execute enc dummy shape program
        (NativeShakeKernel.observed (past world).run.2 world) state)}[event result] := by
  rw [execute_with_cache,prEvent_map]
  exact NativeLazyExecutionLaw.cache_law program replay world enc dummy shape state hashStart
    (fun packet => event (packet,packet.1.2.foldl (record enc dummy shape) state))


/-- Every finite analysis prefix retains its actual residual program and full interpreter state. -/
theorem prefix_law {P : Type} (fuel : ℕ) (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P}
    (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : (((OracleProgram.Program A ⊕ A) × List Observation) × Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (InputIndexedOracle.law[|{other | (past other).run = (past world).run}])
      {other | event (((OracleProgram.runPrefix fuel program other).run,
        NativeShakeKernel.observed ((past other).run.2 ++ (OracleProgram.runPrefix fuel program other).run.2) other),
        (OracleProgram.runPrefix fuel program other).run.2.foldl (record enc dummy shape) state)} =
      Pr{let result ← (execute enc dummy shape (NativeProgramPrefix.take fuel program)
        (NativeShakeKernel.observed (past world).run.2 world) state)}[event result] := by
  simpa only [NativeProgramPrefix.take_run] using
    state_law (NativeProgramPrefix.take fuel program) replay world enc dummy shape state hashStart event

/-- Empty caches and the initial shared state discharge all history premises. -/
theorem from_empty (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton)
    (event : ((A × List Observation) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    InputIndexedOracle.law
      {other | event (((OracleProgram.run program other).run,
        NativeShakeKernel.observed (OracleProgram.run program other).run.2 other),
        (OracleProgram.run program other).run.2.foldl (record enc dummy shape) (CheckpointExecution.empty shape))} =
      Pr{let result ← (execute enc dummy shape program NativeShakeCache.empty
        (CheckpointExecution.empty shape))}[event result] := by
  have proved := state_law program (past := fun _ => WriterT.mk ((),[]))
    (ObservationReplay.pure_replay ()) (fun _ => 0) enc dummy shape (CheckpointExecution.empty shape) rfl event
  simp only [WriterT.run_mk] at proved
  have emptyCache : NativeShakeKernel.observed [] (fun _ => 0) = NativeShakeCache.empty := by
    funext key
    simp [NativeShakeKernel.observed,ObservationReplay.footprint,NativeShakeCache.empty]
  rw [emptyCache] at proved
  simpa using proved

end
end FormalProof4FHE.HasteBoots.NativeLazyStateExecution
