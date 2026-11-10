module
public import FormalProof4FHE.HasteBoots.SingleOpeningExposure
public import FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks
public import FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability
public import FormalProof4FHE.HasteBoots.NativeRootFamilyLifetime
@[expose] public section

/-! Accepted native single openings constrain one immutable raw source in the
same causal history as source batches. Source identity is the actual parameter
context hash and original root. Any missing source pays the existing single
whole-history hash charge, without a union over helpers, workers or owners. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningAvailability
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Height height shape)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeGoldRawAvailability (Equations)
open OracleProgram (Program run)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def tag (context : Digest) (work : Prepared) : NativeMerkleShapeFamily.Tag :=
  (context,Fin.ofNat 64 work.geometry.height)

theorem tag_height (context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : height (tag context work) = work.geometry.height := by
  have built := (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work prepared).1
  have small := NativeBrakedownParameters.path_shift NativeGoldBlockCode.description ctx.parameters work.geometry built
  exact Nat.mod_eq_of_lt (by omega)

def prepare (context : Digest) (work : Prepared) :=
  NativeGoldPcsRawAvailability.prepare height (tag context work) work

theorem prepare_complete (context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : ∃ requests, prepare context work = some requests :=
  NativeGoldPcsRawAvailability.prepare_complete height (tag context work) ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query
    ctx.claimed ctx.opening ctx.fieldFuel world work prepared (tag_height context ctx world work prepared).symm

/-- Both native coordinate families and payload authentication come from the
actual completed causal call, in the complete history's final shared cache. -/
theorem accepted_replays {Memory : Type} (context : Digest) (ctx : Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (requests : List (NativeGoldColumnWorker.Job × Request height)) (computed : prepare context work = some requests)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history) :
    ∀ entry ∈ requests, ParallelColumnAvailability.Replays encoding height entry.2 (JointHashCache.project history).cache ∧
      NativeGoldColumnChecks.check work.geometry work.width work.random work.structured work.test work.evaluation
        entry.2.payload.val entry.2.position.val = true := by
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have matchesHeight := (tag_height context ctx world work prepared).symm
  have spec := NativeGoldRawRequests.entries_spec height (tag context work) work.root work.jobs requests computed
  intro entry member
  have jobMember : entry.1 ∈ work.jobs := by rw [← spec.1]; exact List.mem_map.mpr ⟨entry,member,rfl⟩
  obtain ⟨leaf,siblings,decoded,_,authenticated,checked⟩ := NativeGoldPcsProgram.accepted_workers ctx choose fuel memory world work completion
    executed parent accepted history truthful observed entry.1 jobMember
  obtain ⟨bound,parsedLeaf,parsedSiblings,parsed,same⟩ := NativeGoldRawRequests.fromJob_spec height (tag context work) work.root entry.1 entry.2 (spec.2 entry member)
  have authentication : simulateQ (JointHashCache.project history).cache.toPartialImpl
      (NativeGoldColumnWorker.authentication work.geometry.height entry.1.index work.root entry.1.column) = some true := by
    simpa only [NativeGoldColumnWorker.authentication,decoded] using authenticated
  rw [matchesHeight] at authentication
  rw [same]
  exact ⟨by simpa only [ParallelColumnAvailability.Replays,NativeGoldColumnWorker.authentication,parsed] using authentication,checked⟩

/-- Explicit native framing/allocation domain, using the original single
opening payload. No future response or oracle answer appears in this bound. -/
def Framed (ctx : Context) : Prop := ∃ before : List TranscriptFrame.Frame,
  ctx.transcript.input = TranscriptFrame.encodeMany before ∧ (∀ frame ∈ before, TranscriptFrame.Valid frame) ∧
    (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit

def Accepted {Memory : Type} (world : World) (history : List Observation) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (work : Prepared) : Prop :=
  Framed ctx ∧ ∃ (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length) (parent : NativeTranscript.Transcript),
    (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion ∧
    completion.status = .accepted parent ∧
    (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history

def HasSource (dummy : Digest) (ctx : Context) (work : Prepared) (history : List Observation) (world : World) : Prop :=
  ∃ (context : Digest) (requests : List (NativeGoldColumnWorker.Job × Request height))
    (log : MerkleTreeExtractor.QueryLog Input Digest),
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
    prepare context work = some requests ∧
    (∀ index : Height, ⟨(context,index),⟨work.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) ∧
    ∀ entry ∈ requests,
      entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position ∧
      Equations work.geometry work.width work.random work.structured work.test work.evaluation
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val

/-- Original prepared execution derives the exposure and all typed requests;
no checkpoint, context digest, height or worker-acceptance certificate is input. -/
theorem accepted_has_source {Memory : Type} (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (ctx : Context) (choose : Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (work : Prepared) (accepted : Accepted world history ctx choose fuel memory work)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    HasSource dummy ctx work history world := by
  obtain ⟨⟨before,framed,valid,fits⟩,completion,parent,executed,status,observed⟩ := accepted
  have origin := NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  obtain ⟨context,hashed,frames,read⟩ := SingleOpeningExposure.prepared_exposure ctx world work origin.prepared before framed valid fits
  obtain ⟨requests,computed⟩ := prepare_complete context ctx world work origin.prepared
  have present : .output (SingleOpeningExposure.input before (SingleOpeningExposure.suffix work.geometry.randomCount)
      context ctx.root ctx.query ctx.claimed) 0
      (InputIndexedOracle.bytes world (SingleOpeningExposure.input before (SingleOpeningExposure.suffix work.geometry.randomCount)
        context ctx.root ctx.query ctx.claimed) 0 8) ∈ history := by
    apply observed.subset
    rw [origin.log]
    exact List.mem_append_left _ read
  have positive : InputIndexedOracle.bytes world (SingleOpeningExposure.input before (SingleOpeningExposure.suffix work.geometry.randomCount)
      context ctx.root ctx.query ctx.claimed) 0 8 ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [InputIndexedOracle.bytes,List.length_ofFn,List.length_nil] at lengths
    contradiction
  obtain ⟨log,snapshots⟩ := SingleOpeningExposure.history_snapshot dummy history before (SingleOpeningExposure.suffix work.geometry.randomCount)
    context ctx.root ctx.query ctx.claimed frames 0 _ positive present
  have root := (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world work origin.prepared).2.2
  change ∀ index : Height, ⟨(context,index),⟨ctx.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints at snapshots
  rw [← root] at snapshots
  refine ⟨context,requests,log,hashed,computed,snapshots,?_⟩
  have noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy history) :=
    fun failure => noDisagreement (ParallelColumnAvailability.failure_implies_disagreement encoding dummy height _ _ failure)
  have spec := NativeGoldRawRequests.entries_spec height (tag context work) work.root work.jobs requests computed
  have each := accepted_replays context ctx choose fuel memory world work completion executed parent status requests computed history truthful observed
  intro entry member
  have recorded : ⟨entry.2.tag,⟨entry.2.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints := by
    obtain ⟨bound,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (tag context work) work.root entry.1 entry.2 (spec.2 entry member)
    rw [same]
    exact snapshots (tag context work).2
  have replayed : ParallelColumnAvailability.Replays encoding height entry.2 (reconstructed dummy history).hash.cache := by
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    exact (each entry member).1
  refine ⟨NativeGoldRawAvailability.payload_of_no_failure dummy height (requests.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) (reconstructed dummy history) replayed ⟨entry.2.root,log⟩ recorded rfl noFailure,?_⟩
  exact NativeGoldRawAvailability.equations_of_no_failure dummy height (requests.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) (reconstructed dummy history) replayed ⟨entry.2.root,log⟩ recorded rfl noFailure
    work.geometry work.width work.random work.structured work.test work.evaluation (each entry member).2

/-- Quantify over any witnessed single opening in the same complete history. -/
def Failure (Memory : Type) (dummy : Digest) (history : List Observation) (world : World) : Prop :=
  ∃ (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (work : Prepared),
    Accepted world history ctx choose fuel memory work ∧ ¬HasSource dummy ctx work history world

theorem failure_implies_bad (Memory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (failed : Failure Memory dummy history world) :
    NativeRootFamilyLifetime.Bad dummy history := by
  obtain ⟨ctx,choose,fuel,memory,work,accepted,missing⟩ := failed
  have different : CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history) := by
    by_contra noDisagreement
    exact missing (accepted_has_source dummy world history truthful ctx choose fuel memory work accepted noDisagreement)
  have decisions : SingleOpeningAvailability.instDecidableEqDigest =
      (fun first second : Digest => Fintype.decidablePiFintype first second) := Subsingleton.elim _ _
  rw [decisions] at different
  exact NativeRootFamilyAudit.disagreement_implies_bad dummy world history truthful different

/-- One complete-program hash charge covers all helpers and source batch calls;
this bound does not claim a physical attacker-work bound. -/
theorem failure_le_charge {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    InputIndexedOracle.law {world | Failure Memory dummy (run program world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
        (CheckpointExecution.empty shape) := by
  have included : {world | Failure Memory dummy (run program world).run.2 world} ⊆
      {world | NativeRootFamilyLifetime.Bad dummy (run program world).run.2} := by
    intro world failed
    exact failure_implies_bad Memory dummy world _ ((OracleProgram.run_replay program).truthful world) failed
  exact (measure_mono included).trans (NativeRootFamilyAudit.bad_le_charge dummy program)

end
end FormalProof4FHE.HasteBoots.SingleOpeningAvailability
