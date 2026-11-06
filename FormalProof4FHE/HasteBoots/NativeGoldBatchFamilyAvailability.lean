module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchRawAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyRequests
public import FormalProof4FHE.HasteBoots.NativeRootFamilyState
@[expose] public section

/-! Global ideal-oracle batch availability under a fixed causal shape family.
Every new context/root records all 64 native-sized shapes. The global charge
includes those annotations; this is not a physical attacker-work bound. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Tag height shape tag)
open NativeGoldBatchRawAvailability (View Equations AnyFailure view equations_of_no_failure any_failure_implies_disagreement)
open OracleSpec OracleComp MerkleTreeMultiExtractability
noncomputable section
local instance digestDecisions : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- Reconstruct the ACTUAL parent-instrumented ledger, owned byte cache,
checkpoints and hash cache from the entire observed history, including prequeries. -/
def reconstructed (dummy : Digest) (history : List NativeTranscript.Observation) :
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape :=
  (history.foldl (NativeRootFamilyState.record encoding dummy)
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)).2

theorem reconstructed_hash (dummy : Digest) (history : List NativeTranscript.Observation) :
    (reconstructed dummy history).hash = JointHashCache.project history := by
  unfold reconstructed
  rw [NativeRootFamilyState.fold_hash]
  rfl

/-- Recorded snapshots and the final hash cache are those reconstructed from
this same complete native history. Replay evidence is derived, not supplied. -/
theorem accepted_equations {Memory : Type} (dummy : Digest) (context : Digest)
    (ctx : NativeGoldBatchPcsProgram.Context) (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : InputIndexedOracle.World) (work : NativeGoldBatchPcsProgram.Prepared)
    (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (requests : List (NativeGoldColumnWorker.Job × Request height)) (computed : NativeGoldBatchFamilyRequests.prepare context work = some requests)
    (history : List NativeTranscript.Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy history)) :
    ∀ entry ∈ requests,
      ∀ checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) entry.2.tag,
      ⟨entry.2.tag,checkpoint⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints → checkpoint.root = entry.2.root →
      Equations (view work requests) (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag checkpoint entry.2.position) entry.2.position.val := by
  have each := NativeGoldBatchFamilyRequests.accepted_replays context ctx choose fuel memory world work completion executed parent accepted
    requests computed history truthful observed
  intro entry member checkpoint recorded root
  have facts := each entry member
  have replayed : ParallelColumnAvailability.Replays encoding height entry.2 (reconstructed dummy history).hash.cache := by
    rw [reconstructed_hash]
    exact facts.1
  exact equations_of_no_failure dummy height (view work requests) entry.2 (List.mem_map.mpr ⟨entry,member,rfl⟩)
    (reconstructed dummy history) replayed checkpoint recorded root noFailure facts.2.1

/-- Exact event transport for the native byte/hash program and its actual
parent-instrumented caches/checkpoints. The byte reader has its real law. -/
theorem world_failure_law (dummy : Digest)
    (program : OracleProgram.Program (List (View height))) :
    InputIndexedOracle.law {world | AnyFailure dummy height (OracleProgram.run program world).run.1
      (reconstructed dummy (OracleProgram.run program world).run.2)} =
    Pr{let result ← NativeRootFamilyFreeze.execute encoding dummy NativeParentLedger.empty program NativeShakeCache.empty (CheckpointExecution.empty shape)}[
        AnyFailure dummy height result.1.1.1.1 result.2] := by
  simpa only [NativeRootFamilyState.reconstruct,reconstructed] using NativeRootFamilyState.from_empty program encoding dummy (fun result => AnyFailure dummy height result.1.1.1.1 result.2)

/-- One actual global hash charge, with no additional union factor for batches, groups,
columns or checkpoints. This is not yet a physical attacker-work bound. -/
theorem world_failure_le_charge (dummy : Digest)
    (program : OracleProgram.Program (List (View height))) :
    InputIndexedOracle.law {world | AnyFailure dummy height (OracleProgram.run program world).run.1
      (reconstructed dummy (OracleProgram.run program world).run.2)} ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (CheckpointCollision.loss unifSpec shape)
      ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
      (CheckpointExecution.empty shape) := by
  rw [world_failure_law]
  unfold NativeRootFamilyFreeze.execute
  have decisions : (fun left right : Digest => Fintype.decidablePiFintype left right) = digestDecisions := Subsingleton.elim _ _
  rw [decisions]
  apply le_trans (prEvent_mono _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge (QueryImpl.ofLift unifSpec ProbComp) encoding dummy
      shape
      ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
      (CheckpointExecution.empty shape)
      (CheckpointCollision.safe_empty encoding dummy shape))
  intro result failure
  exact any_failure_implies_disagreement dummy height result.1.1.1.1 result.2 failure
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
