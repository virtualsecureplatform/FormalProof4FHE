module

public import FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldBatchRawRequests
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnWorker
public import FormalProof4FHE.HasteBoots.NativeParentStateExecution
@[expose] public section

/-! Shared raw-row availability for all native batch response groups.
Actual accepted causal workers supply replay/check evidence. Snapshots and
caches are reconstructed from the full parent-instrumented native history.
One global ideal-oracle hash charge covers any selected batch/group/column
failure. Trusted context/shape and first-exposure coverage, full application
soundness, physical attacker work and Rust refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRawAvailability
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (GoldWord)
open InputIndexedOracle (Input)
open NativeGoldColumnAuthentication (encoding)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
noncomputable section
local instance digestDecisions : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure View {Cfg : Type} (height : Cfg → ℕ) where
  geometry : NativeBrakedownParameters.Geometry
  width : ℕ
  random : List GoldWord
  test : List GoldWord
  groups : List NativeGoldBatchColumnWorker.Response
  requests : List (Request height)

def Equations {Cfg : Type} {height : Cfg → ℕ} (view : View height) (values : ℕ → NativeFields.Goldilocks) (index : ℕ) : Prop :=
  ∀ response ∈ view.groups, NativeGoldRawAvailability.Equations view.geometry view.width view.random response.1 view.test response.2 values index

theorem equations_of_no_failure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (view : View height)
    (request : Request height) (member : request ∈ view.requests)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (replayed : ParallelColumnAvailability.Replays encoding height request state.hash.cache)
    (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag)
    (recorded : ⟨request.tag,checkpoint⟩ ∈ state.checkpoints.checkpoints) (root : checkpoint.root = request.root)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height view.requests state)
    (checked : NativeGoldBatchColumnWorker.check view.geometry view.width view.random view.test request.payload.val view.groups request.position.val = true) :
    Equations view (NativeGoldRawAvailability.frozenValue dummy height request.tag checkpoint request.position) request.position.val := by
  intro response responseMember
  exact NativeGoldRawAvailability.equations_of_no_failure dummy height view.requests request member state replayed checkpoint recorded root noFailure
    view.geometry view.width view.random response.1 view.test response.2
    (NativeGoldBatchColumnWorker.check_each _ _ _ _ _ _ _ checked response responseMember)

def Failure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (view : View height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag))) : Prop :=
  ∃ request ∈ view.requests, ParallelColumnAvailability.Replays encoding height request state.hash.cache ∧
    ∃ checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) request.tag,
      ⟨request.tag,checkpoint⟩ ∈ state.checkpoints.checkpoints ∧ checkpoint.root = request.root ∧
      NativeGoldBatchColumnWorker.check view.geometry view.width view.random view.test request.payload.val view.groups request.position.val = true ∧
      ¬Equations view (NativeGoldRawAvailability.frozenValue dummy height request.tag checkpoint request.position) request.position.val

theorem failure_implies_availability {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (view : View height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (failure : Failure dummy height view state) : ParallelColumnAvailability.Failure encoding dummy height view.requests state := by
  obtain ⟨request,member,replayed,checkpoint,recorded,root,checked,different⟩ := failure
  by_contra noFailure
  exact different (equations_of_no_failure dummy height view request member state replayed checkpoint recorded root noFailure checked)

/-- One global event covers every selected batch, column and response group. -/
def AnyFailure {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (views : List (View height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag))) : Prop :=
  ∃ view ∈ views, Failure dummy height view state

theorem any_failure_implies_disagreement {Cfg : Type} (dummy : Digest) (height : Cfg → ℕ) (views : List (View height))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (failure : AnyFailure dummy height views state) : CheckpointAvailability.Disagreement encoding dummy (fun tag => Skeleton.perfect (height tag)) state := by
  obtain ⟨view,_,failed⟩ := failure
  exact ParallelColumnAvailability.failure_implies_disagreement encoding dummy height view.requests state
    (failure_implies_availability dummy height view state failed)

section Runtime
variable {Cfg : Type} [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

theorem any_failure_le_charge (implBase : QueryImpl base ProbComp) (dummy : Digest) (height : Cfg → ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (List (View height)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe encoding dummy (fun tag => Skeleton.perfect (height tag)) state) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag))) program).run state}[
      AnyFailure dummy height result.1 result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program state := by
  apply le_trans (prEvent_mono _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge implBase encoding dummy (fun tag => Skeleton.perfect (height tag)) program state safe)
  intro result failure
  exact any_failure_implies_disagreement dummy height result.1 result.2 failure

theorem any_failure_from_empty_le_charge (implBase : QueryImpl base ProbComp) (dummy : Digest) (height : Cfg → ℕ)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (List (View height))) :
    Pr{let result ← (simulateQ (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag))) program).run (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))}[AnyFailure dummy height result.1 result.2] ≤
      ExpectedHazard.charge (CheckpointExecution.handler implBase encoding dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) :=
  any_failure_le_charge implBase dummy height program _ (CheckpointCollision.safe_empty encoding dummy (fun tag => Skeleton.perfect (height tag)))
end Runtime

/-- Reconstruct the ACTUAL parent-instrumented ledger, owned byte cache,
checkpoints and hash cache from the entire observed history, including prequeries. -/
def reconstructed (dummy : Digest) (height : Digest → ℕ) (history : List NativeTranscript.Observation) :
    CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)) :=
  (history.foldl (NativeParentStateExecution.record encoding dummy (fun tag => Skeleton.perfect (height tag)))
    ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))).2

theorem reconstructed_hash (dummy : Digest) (height : Digest → ℕ) (history : List NativeTranscript.Observation) :
    (reconstructed dummy height history).hash = JointHashCache.project history := by
  unfold reconstructed
  rw [NativeParentStateExecution.fold_hash]
  rfl

def view {Cfg : Type} {height : Cfg → ℕ} (work : NativeGoldBatchPcsProgram.Prepared)
    (requests : List (NativeGoldColumnWorker.Job × Request height)) : View height :=
  ⟨work.geometry,work.width,work.random,work.test,work.groups,requests.map Prod.snd⟩

/-- Recorded snapshots and the final hash cache are those reconstructed from
this same complete native history. Replay evidence is derived, not supplied. -/
theorem accepted_equations {Memory : Type} (dummy : Digest) (height : Digest → ℕ) (tag : Digest)
    (ctx : NativeGoldBatchPcsProgram.Context) (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : InputIndexedOracle.World) (work : NativeGoldBatchPcsProgram.Prepared)
    (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (requests : List (NativeGoldColumnWorker.Job × Request height)) (computed : NativeGoldBatchRawRequests.prepare height tag work = some requests)
    (matchesHeight : work.geometry.height = height tag) (history : List NativeTranscript.Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy height history)) :
    ∀ entry ∈ requests,
      ∀ checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) entry.2.tag,
      ⟨entry.2.tag,checkpoint⟩ ∈ (reconstructed dummy height history).checkpoints.checkpoints → checkpoint.root = entry.2.root →
      Equations (view work requests) (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag checkpoint entry.2.position) entry.2.position.val := by
  have each := NativeGoldBatchRawRequests.accepted_replays height tag ctx choose fuel memory world work completion executed parent accepted
    requests computed matchesHeight history truthful observed
  intro entry member checkpoint recorded root
  have facts := each entry member
  have replayed : ParallelColumnAvailability.Replays encoding height entry.2 (reconstructed dummy height history).hash.cache := by
    rw [reconstructed_hash]
    exact facts.1
  exact equations_of_no_failure dummy height (view work requests) entry.2 (List.mem_map.mpr ⟨entry,member,rfl⟩)
    (reconstructed dummy height history) replayed checkpoint recorded root noFailure facts.2.1

/-- Exact event transport for the native byte/hash program and its actual
parent-instrumented caches/checkpoints. The byte reader has its real law. -/
theorem world_failure_law (dummy : Digest) (height : Digest → ℕ)
    (program : OracleProgram.Program (List (View height))) :
    InputIndexedOracle.law {world | AnyFailure dummy height (OracleProgram.run program world).run.1
      (reconstructed dummy height (OracleProgram.run program world).run.2)} =
    Pr{let result ← NativeParentRootFreeze.execute encoding dummy (fun tag => Skeleton.perfect (height tag)) NativeParentLedger.empty program NativeShakeCache.empty (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))}[
        AnyFailure dummy height result.1.1.1.1 result.2] := by
  simpa only [NativeParentStateExecution.reconstruct,reconstructed] using NativeParentStateExecution.from_empty program encoding dummy
    (fun tag => Skeleton.perfect (height tag)) (fun result => AnyFailure dummy height result.1.1.1.1 result.2)

/-- One actual global hash charge, with no additional union factor for batches, groups,
columns or checkpoints. This is not yet a physical attacker-work bound. -/
theorem world_failure_le_charge (dummy : Digest) (height : Digest → ℕ)
    (program : OracleProgram.Program (List (View height))) :
    InputIndexedOracle.law {world | AnyFailure dummy height (OracleProgram.run program world).run.1
      (reconstructed dummy height (OracleProgram.run program world).run.2)} ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (CheckpointCollision.loss unifSpec (fun tag => Skeleton.perfect (height tag)))
      ((NativeParentRootFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
      (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) := by
  rw [world_failure_law]
  unfold NativeParentRootFreeze.execute
  have decisions : (fun left right : Digest => Fintype.decidablePiFintype left right) = digestDecisions := Subsingleton.elim _ _
  rw [decisions]
  apply le_trans (prEvent_mono _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge (QueryImpl.ofLift unifSpec ProbComp) encoding dummy
      (fun tag => Skeleton.perfect (height tag))
      ((NativeParentRootFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
      (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))
      (CheckpointCollision.safe_empty encoding dummy (fun tag => Skeleton.perfect (height tag))))
  intro result failure
  exact any_failure_implies_disagreement dummy height result.1.1.1.1 result.2 failure
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRawAvailability
