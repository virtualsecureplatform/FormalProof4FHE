module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsExecution

@[expose] public section

/-! Original ordered opening checks from one supported accepted PCS execution.
The root-wide raw availability exception is unchanged. Checkpoint recording
before the outer lookup challenge and the reader's probability law remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsExecutionAgrees

open NativeGoldPcsExecution (Context Outcome program)
open NativeGoldPcsWorkers (Prepared)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeGoldRawRequests (Request)
open NativeGoldColumnAuthentication (encoding)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

variable {Cfg Memory : Type} [SampleableType Digest]

/-- One computed adapter failure event, with no caller-selected request list. -/
def Failure (height : Cfg → ℕ) (tag : Cfg) (dummy : Digest) (work : Prepared)
    (after : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag))) : Prop :=
  ∃ result, NativeGoldPcsRawAvailability.prepare height tag work = some result ∧
    ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) after

/-- The ordered draw vector, raw request list and prefix-success equation are
all obtained from this same accepted run, rather than supplied independently. -/
theorem accepted_agrees (ctx : Context) (reader : NativeCheckpointProgram.Reader)
    (choose : (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (work : Prepared) (observations : List Observation)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (supported : (Outcome.completed work observations completion,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (program ctx reader choose fuel memory)).run before))
    (next : NativeTranscript.Transcript) (accepted : completion.status = .accepted next)
    (matchesHeight : work.geometry.height = height tag)
    (noFailure : ¬Failure height tag dummy work after)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (recorded : ⟨tag,checkpoint⟩ ∈ after.checkpoints.checkpoints) (matchingRoot : checkpoint.root = ctx.root) :
    ∃ sample : NativeIndexRequest.Result, ∃ draw : Fin ctx.parameters.queries.val → Fin (2^(height tag)),
      NativeGoldPcsDraws.typed (height tag) ctx.parameters.queries.val sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = sample.draws ∧
      work.jobs.map NativeGoldColumnWorker.Job.index = NativeIndexRequest.distinct sample.draws ∧
      (∃ suffix, (OracleProgram.run (NativeIndexRequest.request
        (NativeGoldPcsWire.bindResponses suffix ctx.opening.test ctx.opening.evaluation)
        NativeGoldPcsColumns.label (NativeGoldBlockCode.description.row.blocks ctx.parameters.code) ctx.parameters.queries)
        (NativeCheckpointProgram.world reader after.hash.cache)).run.1 = some sample) ∧
      (∀ lane, ColumnOpening.Agrees
        (StructuredOpening.combine (NativeGoldPcsAgrees.weights work.geometry.rows work.width work.random lane)
          (NativeGoldPcsAgrees.source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
        (NativeGoldPcsAgrees.response work.geometry work.width (height tag) work.test lane) draw) ∧
      (∀ lane, ColumnOpening.Agrees
        (StructuredOpening.combine (NativeGoldPcsAgrees.weights work.geometry.rows work.width work.structured lane)
          (NativeGoldPcsAgrees.source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
        (NativeGoldPcsAgrees.response work.geometry work.width (height tag) work.evaluation lane) draw) := by
  obtain ⟨middle,_,continued⟩ := NativeGoldPcsExecution.completed_origin ctx reader choose fuel memory dummy _ before after work observations completion supported
  have native := congrArg Prod.fst (NativeGoldPcsExecution.completed_native ctx reader choose fuel memory dummy _ before after work observations completion supported)
  obtain ⟨result,prepared⟩ := NativeGoldPcsRawAvailability.prepare_complete height tag ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel
    (NativeCheckpointProgram.world reader after.hash.cache) work native matchesHeight
  have clear : ¬ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) after :=
    fun failed => noFailure ⟨result,prepared,failed⟩
  obtain ⟨poolSupported,allAccepted,_,_⟩ := NativeGoldPcsAcceptance.accepted_origin ctx.parameters ctx.query ctx.opening ctx.claimed work dummy _ (choose work)
    fuel memory middle (completion,after) continued next accepted
  have root := (NativeGoldPcsOpeningChecks.prepared_parameters ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel
    (NativeCheckpointProgram.world reader after.hash.cache) work native).2.2
  exact NativeGoldPcsOpeningChecks.prepared_agrees height tag ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel
    (NativeCheckpointProgram.world reader after.hash.cache) work native result prepared matchesHeight dummy (choose work) fuel memory middle
    (completion.pool,after) poolSupported allAccepted clear checkpoint recorded (matchingRoot.trans root.symm)

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsExecutionAgrees
