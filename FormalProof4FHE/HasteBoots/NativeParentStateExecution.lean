module

public import FormalProof4FHE.HasteBoots.NativeParentHistory
@[expose] public section

/-! Exact reconstruction and posterior laws for the actual parent-instrumented
interpreter, including ledger, caches, checkpoints and the passive monitor.
Replayed preludes initialize these fields together. Snapshot coverage means
registration, not Merkle availability, authenticated lineage or physical work. -/
namespace FormalProof4FHE.HasteBoots.NativeParentStateExecution
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeShakeCache (Cache)
open NativeParentRootFreeze (Ledger Spec execute prependExecution)
open OracleSpec OracleComp MeasureTheory ProbabilityTheory
noncomputable section
variable {Payload A : Type}

abbrev State (shape : Digest → BinaryTree.Skeleton) :=
  (Ledger × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape

def record (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (state : State shape) (entry : Observation) : State shape :=
  (NativeParentHistory.record state.1 entry,match entry with
    | .output input _ values => if values = [] then state.2
        else RecordRoots.state shape (NativeParentLedger.prepare state.1.1 state.1.2 input).requests state.2
    | _ => NativeLazyStateExecution.record enc dummy shape state.2 entry)

theorem execute_start (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (next : OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape ledger (.start input next) cache state =
      prependExecution (.start input) <$>
        execute enc dummy shape (NativeParentLedger.discover ledger cache input) next cache state := by
  simp only [execute,NativeParentRootFreeze.compile,StateT.run_bind,StateT.run_get,pure_bind,StateT.run_map,simulateQ_map]
  rfl

theorem execute_hash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (next : Digest → OracleProgram.Program A)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape ledger (.hash input next) cache state = (do
      let digest ← JointHashKernel.answer state.hash input
      let rest ← execute enc dummy shape (NativeParentLedger.discover ledger cache input) (next digest) cache
        (NativeLazyStateExecution.record enc dummy shape state (.hash input (List.ofFn digest)))
      pure (prependExecution (.hash input (List.ofFn digest)) rest)) := by
  simp only [execute,NativeParentRootFreeze.compile,StateT.run_bind,StateT.run_get,pure_bind,
    StateT.run_liftM,simulateQ_bind,simulateQ_map,simulateQ_spec_query,StateT.run_map]
  rw [NativeLazyExecution.hash_step enc dummy shape input state]
  simp only [bind_map_left,simulateQ_pure,StateT.run_pure,bind_pure_comp,prependExecution,NativeLazyStateExecution.record]

theorem sample_records (input : Input) (offset count : ℕ) (cache : Cache) (result : Input × Cache)
    (possible : result ∈ support (NativeShakeReadLaw.sample input offset count cache)) :
    result.1.length = count ∧ result.2 = NativeShakeHistory.writeBytes cache input offset result.1 := by
  rw [support_eq_of_evalDistEq (NativeShakeReadLaw.sample_dist cache input offset count),support_map,Set.mem_image] at possible
  obtain ⟨raw,_,rfl⟩ := possible
  exact ⟨by rw [NativeShakeReadLaw.eager_bytes,List.length_ofFn],NativeShakeReadLaw.eager_records cache input offset count raw⟩

theorem sample_record (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (offset count : ℕ)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Input × Cache) (possible : result ∈ support (NativeShakeReadLaw.sample input offset count cache)) :
    record enc dummy shape ((ledger,cache),state) (.output input offset result.1) =
      ((if 0 < count then (NativeParentLedger.prepare ledger cache input).next
        else NativeParentLedger.discover ledger cache input,result.2),
       if 0 < count then RecordRoots.state shape (NativeParentLedger.prepare ledger cache input).requests state else state) := by
  obtain ⟨length,written⟩ := sample_records input offset count cache result possible
  have nonempty : result.1 = [] ↔ ¬ 0 < count := by
    rw [← List.length_eq_zero_iff,length]
    omega
  simp only [record,NativeParentHistory.record,nonempty,NativeShakeHistory.record,← written]
  by_cases positive : 0 < count <;> simp [positive]

/-- Every supported interpreter outcome has exactly the reconstructed ledger, both caches and shared state. -/
theorem execute_records_support (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (program : OracleProgram.Program A) (ledger : Ledger)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : (((A × List Observation) × Ledger) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape ledger program cache state)) :
    ((result.1.1.2,result.1.2),result.2) = result.1.1.1.2.foldl (record enc dummy shape) ((ledger,cache),state) := by
  induction program generalizing ledger cache state result with
  | pure value =>
    rw [NativeParentRootFreeze.execute_pure] at possible
    have same := eq_of_mem_support_pure _ possible
    subst result
    rfl
  | start input next ih =>
    rw [execute_start,support_map,Set.mem_image] at possible
    obtain ⟨rest,possible,rfl⟩ := possible
    simpa only [prependExecution,NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,
      List.foldl_cons,record,NativeParentHistory.record,NativeLazyStateExecution.record] using
      ih (NativeParentLedger.discover ledger cache input) cache state rest possible
  | read input offset count next ih =>
    by_cases positive : 0 < count
    · rw [NativeParentRootFreeze.execute_read enc dummy shape ledger input offset count next cache state positive,
        mem_support_bind_iff] at possible
      obtain ⟨first,sampled,possible⟩ := possible
      rw [bind_pure_comp,support_map,Set.mem_image] at possible
      obtain ⟨rest,possible,rfl⟩ := possible
      have updated := sample_record enc dummy shape ledger input offset count cache state first sampled
      simpa only [prependExecution,NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,
        List.foldl_cons,updated,ite_eq_left positive] using
        ih first.1 (NativeParentLedger.prepare ledger cache input).next first.2
          (RecordRoots.state shape (NativeParentLedger.prepare ledger cache input).requests state) rest possible
    · have zero : count = 0 := by omega
      subst count
      rw [NativeParentRootFreeze.execute_zero,support_map,Set.mem_image] at possible
      obtain ⟨rest,possible,rfl⟩ := possible
      simpa only [prependExecution,NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,
        List.foldl_cons,record,NativeParentHistory.record,ite_true,NativeShakeHistory.record,NativeShakeHistory.writeBytes] using
        ih [] (NativeParentLedger.discover ledger cache input) cache state rest possible
  | hash input next ih =>
    rw [execute_hash,mem_support_bind_iff] at possible
    obtain ⟨digest,_,possible⟩ := possible
    rw [bind_pure_comp,support_map,Set.mem_image] at possible
    obtain ⟨rest,possible,rfl⟩ := possible
    simpa only [prependExecution,NativeParentRootFreeze.prepend,NativeCheckpointProgram.prepend,
      List.foldl_cons,record,NativeParentHistory.record] using
      ih digest (NativeParentLedger.discover ledger cache input) cache
        (NativeLazyStateExecution.record enc dummy shape state (.hash input (List.ofFn digest))) rest possible

theorem project_value (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (program : OracleProgram.Program A) (ledger : Ledger)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun result => result.1.1.1) <$> execute enc dummy shape ledger program cache state =
      NativeLazyExecution.execute enc dummy shape program cache state := by
  have equal := congrArg (fun code => (fun packet => packet.1.1) <$> code)
    (NativeParentRootFreeze.execute_erasure enc dummy shape ledger program cache state)
  simpa only [Functor.map_map,NativeParentRootFreeze.project,Prod.map_def,id_eq,
    NativeLazyExecution.execute,NativeLazyStateExecution.execute] using equal

def reconstruct (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (packet : A × List Observation) :=
  let final := packet.2.foldl (record enc dummy shape) ((ledger,cache),state)
  (((packet,final.1.1),final.1.2),final.2)

/-- The complete instrumented execution is a deterministic decoration of the original native value/log. -/
theorem execute_records (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (program : OracleProgram.Program A) (ledger : Ledger)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape ledger program cache state =
      reconstruct enc dummy shape ledger cache state <$>
        NativeLazyExecution.execute enc dummy shape program cache state := by
  rw [← project_value enc dummy shape program ledger cache state,Functor.map_map]
  calc _ = (fun result => result) <$> execute enc dummy shape ledger program cache state := by simp
       _ = _ := by
        rw [← bind_pure_comp,← bind_pure_comp]
        apply OracleComp.bind_congr_of_forall_mem_support
        intro result possible
        congr 1
        unfold reconstruct
        rw [← execute_records_support enc dummy shape program ledger cache state result possible]

theorem record_hash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (state : State shape) (entry : Observation) :
    (record enc dummy shape state entry).2.hash = JointHashCache.record state.2.hash entry := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values =>
    simp only [record]
    split
    · rfl
    · exact RecordRoots.hash_eq _ _ _

theorem fold_hash (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (state : State shape) (log : List Observation) :
    (log.foldl (record enc dummy shape) state).2.hash = log.foldl JointHashCache.record state.2.hash := by
  induction log generalizing state with
  | nil => rfl
  | cons entry log ih => rw [List.foldl_cons,List.foldl_cons,ih,record_hash]

theorem fold_parent (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (state : State shape) (log : List Observation) :
    (log.foldl (record enc dummy shape) state).1 = log.foldl NativeParentHistory.record state.1 := by
  induction log generalizing state with
  | nil => rfl
  | cons entry log ih => rw [List.foldl_cons,List.foldl_cons,ih]; rfl

/-- The full ghost and physical state has the exact posterior law of the same ideal-world native log. -/
theorem state_law {P : Type} (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : (((A × List Observation) × Ledger) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (reconstruct enc dummy shape ledger (NativeShakeKernel.observed (past world).run.2 world) state
        (OracleProgram.run program other).run)} =
      Pr{let result ← execute enc dummy shape ledger program (NativeShakeKernel.observed (past world).run.2 world) state}[event result] := by
  rw [execute_records,prEvent_map]
  exact NativeLazyExecutionLaw.execute_law program replay world enc dummy shape state hashStart
    (fun packet => event (reconstruct enc dummy shape ledger (NativeShakeKernel.observed (past world).run.2 world) state packet))

theorem from_empty (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton)
    (event : (((A × List Observation) × Ledger) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    law {world | event (reconstruct enc dummy shape NativeParentLedger.empty NativeShakeCache.empty
      (CheckpointExecution.empty shape) (OracleProgram.run program world).run)} =
      Pr{let result ← (execute enc dummy shape NativeParentLedger.empty program NativeShakeCache.empty
        (CheckpointExecution.empty shape))}[event result] := by
  have proved := state_law program (past := fun _ => WriterT.mk ((),[]))
    (ObservationReplay.pure_replay ()) (fun _ => 0) enc dummy shape NativeParentLedger.empty (CheckpointExecution.empty shape) rfl event
  simp only [WriterT.run_mk] at proved
  have emptyCache : NativeShakeKernel.observed [] (fun _ => 0) = NativeShakeCache.empty := by
    funext key
    simp [NativeShakeKernel.observed,ObservationReplay.footprint,NativeShakeCache.empty]
  rw [emptyCache] at proved
  simpa using proved

/-- The same replayed prelude supplies the ledger, byte cache, checkpoints and hash cache together. -/
theorem after_prelude_law {P : Type} (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton)
    (event : (((A × List Observation) × Ledger) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    let initial := (past world).run.2.foldl (record enc dummy shape)
      ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
    (law[|{other | (past other).run = (past world).run}])
      {other | event (reconstruct enc dummy shape initial.1.1 initial.1.2 initial.2 (OracleProgram.run program other).run)} =
      Pr{let result ← (execute enc dummy shape initial.1.1 program initial.1.2 initial.2)}[event result] := by
  let initial := (past world).run.2.foldl (record enc dummy shape)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
  have hashStart : initial.2.hash = JointHashCache.project (past world).run.2 := by
    unfold initial
    rw [fold_hash]
    rfl
  have cacheStart : initial.1.2 = NativeShakeKernel.observed (past world).run.2 world := by
    unfold initial
    rw [fold_parent,NativeParentHistory.fold_cache]
    exact NativeShakeProjection.fold_observed _ world (replay.truthful world)
  have proved := state_law program replay world enc dummy shape initial.1.1 initial.2 hashStart event
  rw [← cacheStart] at proved
  exact proved

/-- Coverage records existence of an actual retained snapshot, without asserting source availability. -/
def Covered {shape : Digest → BinaryTree.Skeleton} (state : State shape) : Prop :=
  ∀ key ∈ state.1.1.frozen, ∃ log : MerkleTreeExtractor.QueryLog Input Digest,
    ⟨key.1,⟨key.2,log⟩⟩ ∈ state.2.checkpoints.checkpoints

theorem record_covered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (state : State shape) (entry : Observation)
    (covered : Covered state) : Covered (record enc dummy shape state entry) := by
  unfold Covered at covered ⊢
  cases entry with
  | start input =>
    change ∀ key ∈ (NativeParentLedger.discover state.1.1 state.1.2 input).frozen, _
    rw [NativeParentLedger.discover_frozen]
    exact covered
  | hash input digest =>
    change ∀ key ∈ (NativeParentLedger.discover state.1.1 state.1.2 input).frozen, _
    rw [NativeParentLedger.discover_frozen]
    exact covered
  | output input offset values =>
    by_cases empty : values = []
    · simpa only [record,NativeParentHistory.record,empty,ite_true,NativeParentLedger.discover_frozen] using covered
    · simp only [record,NativeParentHistory.record,empty,ite_false]
      intro key member
      by_cases old : key ∈ state.1.1.frozen
      · obtain ⟨log,present⟩ := covered key old
        exact ⟨log,RecordRoots.retains shape _ state.2 key.1 ⟨key.2,log⟩ present⟩
      · have requested : key ∈ (NativeParentLedger.prepare state.1.1 state.1.2 input).requests := by
          apply (NativeParentLedger.prepare_mem _ _ _ _).mpr
          rw [NativeParentLedger.prepare_frozen] at member
          exact ⟨List.mem_toFinset.mp ((Finset.mem_union.mp member).resolve_left old),old⟩
        exact ⟨state.2.hash.log,RecordRoots.recorded shape _ state.2 key requested⟩

theorem fold_covered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (state : State shape) (log : List Observation)
    (covered : Covered state) : Covered (log.foldl (record enc dummy shape) state) := by
  induction log generalizing state with
  | nil => exact covered
  | cons entry log ih => exact ih _ (record_covered enc dummy shape state entry covered)

theorem empty_covered (shape : Digest → BinaryTree.Skeleton) :
    Covered ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape) := by
  intro key member
  exact False.elim (Finset.notMem_empty key member)

theorem execute_covered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (program : OracleProgram.Program A) (ledger : Ledger)
    (cache : Cache) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (covered : Covered ((ledger,cache),state))
    (result : (((A × List Observation) × Ledger) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape ledger program cache state)) :
    Covered ((result.1.1.2,result.1.2),result.2) := by
  rw [execute_records_support enc dummy shape program ledger cache state result possible]
  exact fold_covered enc dummy shape _ _ covered

/-- Analysis suspension carries the same ledger, byte cache and shared state into the suffix. -/
theorem execute_bind {B : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (program : OracleProgram.Program A)
    (next : A → OracleProgram.Program B) (ledger : Ledger) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    execute enc dummy shape ledger (OracleProgram.bind program next) cache state = (do
      let first ← execute enc dummy shape ledger program cache state
      let second ← execute enc dummy shape first.1.1.2 (next first.1.1.1.1) first.1.2 first.2
      pure ((((second.1.1.1.1,first.1.1.1.2++second.1.1.1.2),second.1.1.2),second.1.2),second.2)) := by
  simp only [execute,NativeParentRootFreeze.compile_bind,StateT.run_bind,simulateQ_bind,
    StateT.run_pure,simulateQ_pure]

/-- Finite-prefix events include the actual residual program and complete reconstructed state. -/
theorem prefix_law {P : Type} (fuel : ℕ) (program : OracleProgram.Program A)
    {past : World → NativeTranscript.Execution P} (replay : ObservationReplay.Replayable past) (world : World)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashStart : state.hash = JointHashCache.project (past world).run.2)
    (event : ((((OracleProgram.Program A ⊕ A) × List Observation) × Ledger) × Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event (reconstruct enc dummy shape ledger (NativeShakeKernel.observed (past world).run.2 world) state
        (OracleProgram.runPrefix fuel program other).run)} =
      Pr{let result ← (execute enc dummy shape ledger (NativeProgramPrefix.take fuel program)
        (NativeShakeKernel.observed (past world).run.2 world) state)}[event result] := by
  simpa only [NativeProgramPrefix.take_run] using
    state_law (NativeProgramPrefix.take fuel program) replay world enc dummy shape ledger state hashStart event

/-- A resolved key already has an earlier snapshot, or this read records its actual pre-read hash log. -/
theorem resolved_snapshot (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Digest → BinaryTree.Skeleton) (ledger : Ledger) (input : Input) (offset count : ℕ)
    (next : Input → OracleProgram.Program A) (cache : Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (covered : Covered ((ledger,cache),state)) (positive : 0 < count)
    (key : NativeCanonicalLookupWire.Source) (resolved : key ∈ NativeParentLedger.resolve ledger cache input)
    (result : (((A × List Observation) × Ledger) × Cache) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (execute enc dummy shape ledger (.read input offset count next) cache state)) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ⟨key.1,⟨key.2,log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  by_cases old : key ∈ ledger.frozen
  · obtain ⟨log,present⟩ := covered key old
    exact ⟨log,CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape key.1
      ⟨key.2,log⟩ ((NativeParentRootFreeze.compile ledger (.read input offset count next)).run cache) state present result possible⟩
  · exact ⟨state.hash.log,NativeParentRootFreeze.read_snapshot enc dummy shape ledger input offset count next cache state
      positive key ((NativeParentLedger.prepare_mem _ _ _ _).mpr ⟨resolved,old⟩) result possible⟩

end
end FormalProof4FHE.HasteBoots.NativeParentStateExecution
