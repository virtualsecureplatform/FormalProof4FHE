module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints

@[expose] public section

/-! One full lookup execution with earlier source and later helper snapshots.
All native observations are preserved. Global adversarial prequeries, the
reader probability law and downstream PCS composition remain obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution

open NativeSharedLookupCheckpoints (Context Prepared)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

noncomputable section
variable {C S B Cfg : Type}

def program (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader)
    (sourceTag : Fin ctx.registry.val.length → Cfg) (helperTag : Fin ctx.proof.roots.val.length → Cfg) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option NativeSharedLookupBody.Outcome × List Observation) := do
  let packet ← NativeSharedLookupCheckpoints.freeze ctx reader sourceTag
  (fun later => (later.1,packet.2 ++ later.2)) <$>
    NativeSharedLookupChildCheckpoints.program ctx packet.1 reader helperTag

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
variable [SampleableType Digest]

theorem origin (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader)
    (sourceTag : Fin ctx.registry.val.length → Cfg) (helperTag : Fin ctx.proof.roots.val.length → Cfg)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader sourceTag helperTag)).run before)) :
    ∃ packet middle later,
      (packet,middle) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeSharedLookupCheckpoints.freeze ctx reader sourceTag)).run before) ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeSharedLookupChildCheckpoints.program ctx packet.1 reader helperTag)).run middle) ∧
      result = (later.1,packet.2 ++ later.2) := by
  rw [program,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨first,prepared,continued⟩ := supported
  rw [simulateQ_map,StateT.run_map,support_map,Set.mem_image] at continued
  obtain ⟨last,executed,same⟩ := continued
  cases same
  exact ⟨first.1,first.2,last.1,prepared,executed,rfl⟩

theorem native_replay (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader)
    (sourceTag : Fin ctx.registry.val.length → Cfg) (helperTag : Fin ctx.proof.roots.val.length → Cfg)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader sourceTag helperTag)).run before)) :
    (OracleProgram.run ctx.native (NativeCheckpointProgram.world reader after.hash.cache)).run = result := by
  obtain ⟨packet,middle,later,frozen,continued,rfl⟩ := origin ctx reader sourceTag helperTag dummy shape before after result supported
  obtain ⟨earlier,prepared,same⟩ := NativeCheckpointBoundary.freeze_origin reader ctx.prepare
    (NativeSharedLookupCheckpoints.selected ctx sourceTag) NativeGoldColumnAuthentication.encoding dummy shape before middle packet frozen
  have grows := CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape
    (NativeSharedLookupChildCheckpoints.program ctx packet.1 reader helperTag) middle (later,after) continued
  rw [same,RecordRoots.hash_eq] at grows
  have initial := NativeCheckpointProgram.supported_later reader ctx.prepare NativeGoldColumnAuthentication.encoding dummy shape
    before (packet,earlier) prepared after.hash.cache grows
  have terminal := NativeSharedLookupChildCheckpoints.native_replay ctx packet.1 reader helperTag dummy shape middle after later continued
  rw [NativeSharedLookupCheckpoints.native_eq,OracleProgram.run_bind,ObservationReplay.run_bind,initial,terminal]

/-- Both families come from one run. Source snapshots use the pre-child log;
helper snapshots use the completed outer-sampler log, before equality. -/
theorem recorded_families (ctx : Context C S B) (reader : NativeCheckpointProgram.Reader)
    (sourceTag : Fin ctx.registry.val.length → Cfg) (helperTag : Fin ctx.proof.roots.val.length → Cfg)
    (dummy : Digest) (shape : Cfg → Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Option NativeSharedLookupBody.Outcome × List Observation)
    (supported : (result,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader sourceTag helperTag)).run before)) (returned : result.1 ≠ none) :
    ∃ packet sourceEarlier sourceMiddle later sampled observations helperEarlier,
      (packet,sourceEarlier) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader ctx.prepare)).run before) ∧
      sourceMiddle = RecordRoots.state shape (NativeSharedLookupCheckpoints.taggedRoots ctx.registry sourceTag) sourceEarlier ∧
      (later,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeSharedLookupChildCheckpoints.program ctx packet.1 reader helperTag)).run sourceMiddle) ∧
      ((some sampled,observations),helperEarlier) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader (NativeSharedLookupChildCheckpoints.head ctx packet.1))).run sourceMiddle) ∧
      (∃ geometry ready, packet.1.2 = some geometry ∧
        NativeSharedLookupHelperCheckpoints.gate (NativeSharedLookupChildCheckpoints.window ctx geometry sampled.child) sampled.batch = some ready) ∧
      (∀ slot : Fin ctx.registry.val.length,
        ⟨sourceTag slot,⟨(ctx.registry.val[slot.val]).root,sourceEarlier.hash.log⟩⟩ ∈ after.checkpoints.checkpoints) ∧
      (∀ index : Fin ctx.proof.roots.val.length,
        ⟨helperTag index,⟨ctx.proof.roots.val[index.val],helperEarlier.hash.log⟩⟩ ∈ after.checkpoints.checkpoints) := by
  obtain ⟨packet,middle,later,frozen,continued,resultSame⟩ := origin ctx reader sourceTag helperTag dummy shape before after result supported
  have childReturned : later.1 ≠ none := by rw [resultSame] at returned; exact returned
  obtain ⟨geometry,sampled,observations,ready,helperEarlier,helperMiddle,last,hasGeometry,sampledRun,gate,_,_,_,helperRecorded⟩ :=
    NativeSharedLookupChildCheckpoints.recorded_helpers ctx packet.1 reader helperTag dummy shape middle after later continued childReturned
  obtain ⟨sourceEarlier,prepared,same⟩ := NativeCheckpointBoundary.freeze_origin reader ctx.prepare
    (NativeSharedLookupCheckpoints.selected ctx sourceTag) NativeGoldColumnAuthentication.encoding dummy shape before middle packet frozen
  have chosen : NativeSharedLookupCheckpoints.selected ctx sourceTag packet.1 = NativeSharedLookupCheckpoints.taggedRoots ctx.registry sourceTag := by
    simp only [NativeSharedLookupCheckpoints.selected,hasGeometry]
  rw [chosen] at same
  refine ⟨packet,sourceEarlier,middle,later,sampled,observations,helperEarlier,prepared,same,continued,sampledRun,
    ⟨geometry,ready,hasGeometry,gate⟩,?_,helperRecorded⟩
  intro slot
  apply CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape
    (sourceTag slot) ⟨(ctx.registry.val[slot.val]).root,sourceEarlier.hash.log⟩
    (NativeSharedLookupChildCheckpoints.program ctx packet.1 reader helperTag) middle ?_ (later,after) continued
  rw [same]
  exact RecordRoots.recorded shape _ sourceEarlier _ (NativeSharedLookupCheckpoints.tagged_mem ctx.registry sourceTag slot)

end
end FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution
