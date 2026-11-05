module

public import FormalProof4FHE.HasteBoots.OracleProgram
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
public import FormalProof4FHE.HasteBoots.InterleavedMerkleWorker

@[expose] public section

/-! Compile a native mixed prefix into the actual shared checkpoint execution.
The SHAKE reader is an explicit functional backend; this module does not assign
it a probability law or claim production freshness. Every SHA-512 call uses
the existing canonical cached handler, with all native observations retained. -/
namespace FormalProof4FHE.HasteBoots.NativeCheckpointProgram

open InputIndexedOracle (Byte Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp

abbrev Reader := Input → ℕ → Byte

def bytes (reader : Reader) (input : Input) (offset count : ℕ) : Input :=
  List.ofFn (fun index : Fin count => reader input (offset+index.val))

def prepend {A : Type} (entry : Observation) (result : A × List Observation) : A × List Observation :=
  (result.1,entry::result.2)

noncomputable section

def compile {Cfg A : Type} (reader : Reader) : OracleProgram.Program A →
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (A × List Observation)
  | .pure value => pure (value,[])
  | .start input next => prepend (.start input) <$> compile reader next
  | .read input offset count next =>
    let output := bytes reader input offset count
    prepend (.output input offset output) <$> compile reader (next output)
  | .hash input next => do
    let answer ← liftM ((CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inr (.inl input)))
    prepend (.hash input (List.ofFn answer)) <$> compile reader (next answer)

/-- Complete a world from the actual final cache; unqueried hashes use zero.
No future hash answer is used to choose a native input. -/
def world (reader : Reader) (cache : (Input →ₒ Digest).QueryCache) : World
  | .inl (input,offset) => reader input offset
  | .inr (input,index) => (cache input).getD (fun _ => 0) index

theorem world_reader (reader : Reader) (cache : (Input →ₒ Digest).QueryCache) :
    InputIndexedOracle.shake (world reader cache) = reader := rfl

theorem world_hash (reader : Reader) (cache : (Input →ₒ Digest).QueryCache)
    (input : Input) (answer : Digest) (known : cache input = some answer) :
    InputIndexedOracle.sha512 (world reader cache) input = answer := by
  funext index
  simp only [InputIndexedOracle.sha512,world,known,Option.getD_some]

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

variable {Cfg A Payload : Type} [SampleableType Digest]

/-- One actual shared hash step records precisely the returned native digest,
including cache hits and repeated calls. -/
theorem hash_record (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → BinaryTree.Skeleton) (input : Input)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (answer : Digest)
    (supported : (answer,after) ∈ support ((CheckpointExecution.handler
      (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape (.inr (.inl input))).run before)) :
    after.hash = JointHashCache.record before.hash (.hash input (List.ofFn answer)) := by
  change (answer,after) ∈ support ((fun result =>
      (result.1,CheckpointExecution.afterHash enc dummy shape before result.2)) <$>
        (CachedHashHandler.handler input).run before.hash) at supported
  rw [support_map,Set.mem_image] at supported
  obtain ⟨result,read,same⟩ := supported
  cases known : before.hash.cache input with
  | none =>
    rw [CachedHashHandler.run_fresh before.hash input known,support_map,Set.mem_image] at read
    obtain ⟨digest,_,returned⟩ := read
    subst result
    cases same
    simp only [CheckpointExecution.afterHash,JointHashCache.record,JointHashCache.decode_ofFn]
  | some saved =>
    rw [CachedHashHandler.run_cached before.hash input saved known] at read
    have returned := eq_of_mem_support_pure _ read
    subst result
    cases same
    simp only [CheckpointExecution.afterHash,JointHashCache.record,JointHashCache.decode_ofFn,
      JointHashCache.cacheQuery_known before.hash input saved known]

/-- Exact shared hash state after the prefix: no hidden hash call, key, log
entry or cache update is omitted from its retained native observations. -/
theorem supported_hash_state (reader : Reader) (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (A × List Observation) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (compile reader program)).run before)) :
    outcome.2.hash = outcome.1.2.foldl JointHashCache.record before.hash := by
  induction program generalizing before outcome with
  | pure value =>
    have same := eq_of_mem_support_pure _ supported
    subst outcome
    rfl
  | start input next ih =>
    rw [compile,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
    obtain ⟨rest,read,rfl⟩ := supported
    simpa only [prepend,List.foldl_cons,JointHashCache.record] using ih before rest read
  | read input offset count next ih =>
    rw [compile,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
    obtain ⟨rest,read,rfl⟩ := supported
    simpa only [prepend,List.foldl_cons,JointHashCache.record] using
      ih (bytes reader input offset count) before rest read
  | hash input next ih =>
    rw [compile,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,queried,tail⟩ := supported
    rw [simulateQ_map,StateT.run_map,support_map,Set.mem_image] at tail
    obtain ⟨rest,read,rfl⟩ := tail
    have recorded := hash_record enc dummy shape input before middle.2 middle.1 queried
    change rest.2.hash = _
    simpa only [prepend,List.foldl_cons,← recorded] using ih middle.1 middle.2 rest read

/-- Every supported compiled prefix is the original native computation in
any world matching its reader and actual final shared cache. This recovers
both the returned value and the entire ordered observation list. -/
theorem supported_replay (reader : Reader) (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (A × List Observation) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (compile reader program)).run before))
    (actual : World) (sameReader : InputIndexedOracle.shake actual = reader)
    (sameHash : ∀ input answer, outcome.2.hash.cache input = some answer → InputIndexedOracle.sha512 actual input = answer) :
    (OracleProgram.run program actual).run = outcome.1 := by
  induction program generalizing before outcome with
  | pure value =>
    have same := eq_of_mem_support_pure _ supported
    subst outcome
    rfl
  | start input next ih =>
    rw [compile,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
    obtain ⟨rest,read,rfl⟩ := supported
    have result := ih before rest read sameHash
    simpa only [OracleProgram.run,ObservationReplay.start,WriterT.run_mk,
      ObservationReplay.run_bind,List.singleton_append,prepend] using
      congrArg (prepend (.start input)) result
  | read input offset count next ih =>
    rw [compile,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
    obtain ⟨rest,read,rfl⟩ := supported
    have output : InputIndexedOracle.bytes actual input offset count = bytes reader input offset count := by
      unfold InputIndexedOracle.bytes InputIndexedOracle.block bytes
      rw [sameReader]
    have result := ih (bytes reader input offset count) before rest read sameHash
    simpa only [OracleProgram.run,ObservationReplay.read,WriterT.run_mk,
      ObservationReplay.run_bind,List.singleton_append,output,prepend] using
      congrArg (prepend (.output input offset (bytes reader input offset count))) result
  | hash input next ih =>
    rw [compile,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,queried,tail⟩ := supported
    rw [simulateQ_map,StateT.run_map,support_map,Set.mem_image] at tail
    obtain ⟨rest,read,rfl⟩ := tail
    have grows := CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy shape (compile reader (next middle.1)) middle.2 rest read
    have known := InterleavedMerkleWorker.hash_query_caches (QueryImpl.ofLift unifSpec ProbComp)
      enc dummy shape input before middle.2 middle.1 queried
    have answer := sameHash input middle.1 (grows known)
    have result := ih middle.1 middle.2 rest read sameHash
    simpa only [OracleProgram.run,ObservationReplay.hash,WriterT.run_mk,
      ObservationReplay.run_bind,List.singleton_append,answer,prepend] using
      congrArg (prepend (.hash input (List.ofFn middle.1))) result

/-- The native replay world is derived from this execution, not a supplied
prefix-success or cache-coherence certificate. Probability transport of the
reader/backend remains a separate obligation. -/
theorem supported_actual (reader : Reader) (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (A × List Observation) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (compile reader program)).run before)) :
    (OracleProgram.run program (world reader outcome.2.hash.cache)).run = outcome.1 :=
  supported_replay reader program enc dummy shape before outcome supported _ (world_reader _ _)
    (world_hash reader outcome.2.hash.cache)

/-- Later shared work may extend the cache. Replaying the prefix against that
same final cache retains its complete value and observations. -/
theorem supported_later (reader : Reader) (program : OracleProgram.Program A)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (A × List Observation) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (compile reader program)).run before))
    (later : (Input →ₒ Digest).QueryCache) (grows : outcome.2.hash.cache ≤ later) :
    (OracleProgram.run program (world reader later)).run = outcome.1 :=
  supported_replay reader program enc dummy shape before outcome supported _ (world_reader _ _)
    (fun input answer known => world_hash reader later input answer (grows known))

end
end FormalProof4FHE.HasteBoots.NativeCheckpointProgram
