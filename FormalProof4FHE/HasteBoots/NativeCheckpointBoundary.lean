module

public import FormalProof4FHE.HasteBoots.NativeHashPrefix
public import FormalProof4FHE.HasteBoots.RecordRoots

@[expose] public section

/-! A passive root-recording boundary between actual compiled native stages.
Every snapshot uses the actual earlier hash log; later stages retain it.
No digest, native observation, or native return value is changed by recording. -/
namespace FormalProof4FHE.HasteBoots.NativeCheckpointBoundary

open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

noncomputable section
variable {Cfg A B : Type}

def freeze (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (A × List Observation) := do
  let packet ← NativeCheckpointProgram.compile reader prelude
  let _ ← RecordRoots.program (roots packet.1)
  pure packet

def program (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) (next : A → OracleProgram.Program B) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (B × List Observation) := do
  let packet ← freeze reader prelude roots
  (fun later => (later.1,packet.2 ++ later.2)) <$> NativeCheckpointProgram.compile reader (next packet.1)

theorem freeze_independent (prelude : OracleProgram.Program A) (hashes : NativeHashPrefix.HashOnly prelude)
    (roots : A → List (Cfg × Digest)) (left right : NativeCheckpointProgram.Reader) :
    freeze left prelude roots = freeze right prelude roots := by
  unfold freeze
  rw [NativeHashPrefix.compile_independent prelude hashes left right]

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
variable {Payload : Type} [SampleableType Digest]

theorem freeze_origin (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) (enc : MerkleOracle.Encoding Input Digest Payload)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (packet : A × List Observation)
    (supported : (packet,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (freeze reader prelude roots)).run before)) :
    ∃ middle, (packet,middle) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (NativeCheckpointProgram.compile reader prelude)).run before) ∧
      after = RecordRoots.state shape (roots packet.1) middle := by
  rw [freeze,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨first,prepared,continued⟩ := supported
  rw [simulateQ_bind,StateT.run_bind,RecordRoots.run_program] at continued
  change (packet,after) ∈ support (pure (first.1,RecordRoots.state shape (roots first.1.1) first.2) : ProbComp _) at continued
  have same := eq_of_mem_support_pure _ continued
  cases same
  exact ⟨first.2,prepared,rfl⟩

/-- Every chosen root has the same actual pre-recording prelude log. -/
theorem freeze_recorded (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) (enc : MerkleOracle.Encoding Input Digest Payload)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (packet : A × List Observation)
    (supported : (packet,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (freeze reader prelude roots)).run before)) :
    ∃ middle, (packet,middle) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (NativeCheckpointProgram.compile reader prelude)).run before) ∧
      after.hash = middle.hash ∧ ∀ request ∈ roots packet.1,
        ⟨request.1,⟨request.2,middle.hash.log⟩⟩ ∈ after.checkpoints.checkpoints := by
  obtain ⟨middle,prepared,rfl⟩ := freeze_origin reader prelude roots enc dummy shape before after packet supported
  exact ⟨middle,prepared,RecordRoots.hash_eq _ _ _,fun request member => RecordRoots.recorded _ _ _ request member⟩

theorem program_origin (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) (next : A → OracleProgram.Program B)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : B × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program reader prelude roots next)).run before)) :
    ∃ packet middle later,
      (packet,middle) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (freeze reader prelude roots)).run before) ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (NativeCheckpointProgram.compile reader (next packet.1))).run middle) ∧
      result = (later.1,packet.2 ++ later.2) := by
  rw [program,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨first,prepared,continued⟩ := supported
  rw [simulateQ_map,StateT.run_map,support_map,Set.mem_image] at continued
  obtain ⟨last,executed,same⟩ := continued
  cases same
  exact ⟨first.1,first.2,last.1,prepared,executed,rfl⟩

/-- Recording erases exactly: complete native value and ordered observations
are recovered in the world supplied by the actual final cache. -/
theorem native_replay (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) (next : A → OracleProgram.Program B)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : B × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program reader prelude roots next)).run before)) :
    (OracleProgram.run (OracleProgram.bind prelude next) (NativeCheckpointProgram.world reader after.hash.cache)).run = result := by
  obtain ⟨packet,middle,later,frozen,continued,rfl⟩ := program_origin reader prelude roots next enc dummy shape before after result supported
  obtain ⟨earlier,prepared,same⟩ := freeze_origin reader prelude roots enc dummy shape before middle packet frozen
  have grows := CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (NativeCheckpointProgram.compile reader (next packet.1)) middle (later,after) continued
  rw [same,RecordRoots.hash_eq] at grows
  have initial := NativeCheckpointProgram.supported_later reader prelude enc dummy shape before (packet,earlier) prepared after.hash.cache grows
  have terminal := NativeCheckpointProgram.supported_actual reader (next packet.1) enc dummy shape middle (later,after) continued
  rw [OracleProgram.run_bind,ObservationReplay.run_bind,initial,terminal]

/-- Snapshots created before the continuation survive every later action,
without conditioning on acceptance or on an unset stability monitor. -/
theorem program_recorded (reader : NativeCheckpointProgram.Reader) (prelude : OracleProgram.Program A)
    (roots : A → List (Cfg × Digest)) (next : A → OracleProgram.Program B)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : B × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program reader prelude roots next)).run before)) :
    ∃ packet earlier middle later,
      (packet,earlier) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (NativeCheckpointProgram.compile reader prelude)).run before) ∧
      middle = RecordRoots.state shape (roots packet.1) earlier ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (NativeCheckpointProgram.compile reader (next packet.1))).run middle) ∧
      result = (later.1,packet.2 ++ later.2) ∧
      ∀ request ∈ roots packet.1, ⟨request.1,⟨request.2,earlier.hash.log⟩⟩ ∈ after.checkpoints.checkpoints := by
  obtain ⟨packet,middle,later,frozen,continued,sameResult⟩ := program_origin reader prelude roots next enc dummy shape before after result supported
  obtain ⟨earlier,prepared,same⟩ := freeze_origin reader prelude roots enc dummy shape before middle packet frozen
  refine ⟨packet,earlier,middle,later,prepared,same,continued,sameResult,?_⟩
  intro request member
  apply CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape request.1 ⟨request.2,earlier.hash.log⟩
    (NativeCheckpointProgram.compile reader (next packet.1)) middle ?_ (later,after) continued
  rw [same]
  exact RecordRoots.recorded shape (roots packet.1) earlier request member

end
end FormalProof4FHE.HasteBoots.NativeCheckpointBoundary
