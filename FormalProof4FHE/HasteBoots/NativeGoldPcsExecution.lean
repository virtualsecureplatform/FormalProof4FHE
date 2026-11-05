module

public import FormalProof4FHE.HasteBoots.NativeCheckpointProgram
public import FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptanceSoundness

@[expose] public section

/-! One shared execution for the checked native mixed prefix and the general
interleaved raw worker/claim tail. Prefix success and the intermediate shared
cache are recovered from this run. The explicit SHAKE reader still needs its
joint-world probability law; checkpoint placement before outer lookup challenges
and native scheduler/compiler refinement are separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsExecution

open NativeGoldBlockCode (Tables Stored)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation)
open InputIndexedOracle (Input)
open NativeFieldRepresentation (goldValue)
open OracleSpec OracleComp

structure Context where
  tables : Tables
  parameters : Parameters Stored
  transcript : Transcript
  root : Digest
  query : Query
  claimed : Row
  opening : Opening
  fieldFuel : ℕ

def Context.prefix (ctx : Context) : OracleProgram.Program NativeGoldPcsWorkers.Outcome :=
  NativeGoldPcsWorkers.protocol ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel

inductive Outcome (Memory : Type) where
  | prefix (prior : NativeGoldPcsWorkers.Outcome) (observations : List Observation)
  | completed (work : Prepared) (observations : List Observation)
      (result : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)

noncomputable section

variable {Cfg Memory : Type}

/-- All prefix hashes and later scheduler/worker hashes share this one state.
The observation list is computed by the compiler, never supplied by a caller. -/
def program (ctx : Context) (reader : NativeCheckpointProgram.Reader)
    (choose : (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Outcome Memory) := do
  let packet ← NativeCheckpointProgram.compile reader ctx.prefix
  match packet.1 with
  | .prepared work =>
    (Outcome.completed work packet.2) <$>
      NativeGoldPcsAcceptance.program ctx.parameters ctx.query ctx.opening ctx.claimed work (choose work) fuel memory
  | prior => pure (.prefix prior packet.2)

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

variable [SampleableType Digest]

/-- The intermediate state is produced by the actual compiled prefix and
passed unchanged to the actual general pool; the caller supplies neither run. -/
theorem completed_origin (ctx : Context) (reader : NativeCheckpointProgram.Reader)
    (choose : (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (work : Prepared) (observations : List Observation)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (supported : (.completed work observations completion,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader choose fuel memory)).run before)) :
    ∃ middle, ((NativeGoldPcsWorkers.Outcome.prepared work,observations),middle) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeCheckpointProgram.compile reader ctx.prefix)).run before) ∧
      (completion,after) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeGoldPcsAcceptance.program ctx.parameters ctx.query ctx.opening ctx.claimed work (choose work) fuel memory)).run middle) := by
  rw [program,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨⟨prior,log⟩,middle⟩,prepared,continued⟩ := supported
  cases prior with
  | «prefix» prior =>
    have impossible := eq_of_mem_support_pure _ continued
    cases impossible
  | pairingUnavailable =>
    have impossible := eq_of_mem_support_pure _ continued
    cases impossible
  | prepared original =>
    rw [simulateQ_map,StateT.run_map,support_map,Set.mem_image] at continued
    obtain ⟨rest,run,same⟩ := continued
    cases same
    exact ⟨middle,prepared,run⟩

/-- Recover the original checked native prefix, including its observations,
in a world completed from the actual final cache of this very execution. -/
theorem completed_native (ctx : Context) (reader : NativeCheckpointProgram.Reader)
    (choose : (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (work : Prepared) (observations : List Observation)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (supported : (.completed work observations completion,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader choose fuel memory)).run before)) :
    (OracleProgram.run ctx.prefix (NativeCheckpointProgram.world reader after.hash.cache)).run = (.prepared work,observations) := by
  obtain ⟨middle,prepared,continued⟩ := completed_origin ctx reader choose fuel memory dummy shape before after work observations completion supported
  have grows := CheckpointCollision.cache_monotone_run (QueryImpl.ofLift unifSpec ProbComp)
    NativeGoldColumnAuthentication.encoding dummy shape
    (NativeGoldPcsAcceptance.program ctx.parameters ctx.query ctx.opening ctx.claimed work (choose work) fuel memory)
    middle (completion,after) continued
  exact NativeCheckpointProgram.supported_later reader ctx.prefix NativeGoldColumnAuthentication.encoding dummy shape
    before ((.prepared work,observations),middle) prepared after.hash.cache grows

/-- Final suffix semantics follow from one supported accepted execution;
there is no separate world/prefix-success or initial pool-state premise. -/
theorem accepted_value (ctx : Context) (reader : NativeCheckpointProgram.Reader)
    (choose : (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (work : Prepared) (observations : List Observation)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (supported : (.completed work observations completion,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader choose fuel memory)).run before))
    (next : Transcript) (accepted : completion.status = .accepted next) :
    next = work.transcript ∧ ctx.claimed.val.map goldValue = List.ofFn (FlatMatrixFold.foldAll
      ((ctx.query.models.drop ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val))
      (fun index lane => goldValue (ctx.opening.evaluation.val[lane.val*2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)+index.val]?.getD 0))) := by
  obtain ⟨middle,_,continued⟩ := completed_origin ctx reader choose fuel memory dummy shape before after work observations completion supported
  have native := congrArg Prod.fst (completed_native ctx reader choose fuel memory dummy shape before after work observations completion supported)
  exact NativeGoldPcsAcceptanceSoundness.accepted_value ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel
    (NativeCheckpointProgram.world reader after.hash.cache) work native dummy shape (choose work) fuel memory middle
    (completion,after) continued next accepted

/-- Acceptance in the same complete run enforces every original raw worker
against its actual final shared cache, including both coordinate families. -/
theorem accepted_workers (ctx : Context) (reader : NativeCheckpointProgram.Reader)
    (choose : (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (before after : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (work : Prepared) (observations : List Observation)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (supported : (.completed work observations completion,after) ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program ctx reader choose fuel memory)).run before))
    (next : Transcript) (accepted : completion.status = .accepted next) :
    ∀ job ∈ work.jobs, ∃ leaf siblings, NativeGoldColumnAuthentication.decodePath work.geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ after.hash.cache.toPartialImpl (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding work.geometry.height
        job.index job.column.values leaf work.root siblings) = some true ∧
      NativeGoldColumnChecks.check work.geometry work.width work.random work.structured work.test work.evaluation job.column.values.val job.index = true := by
  obtain ⟨middle,_,continued⟩ := completed_origin ctx reader choose fuel memory dummy shape before after work observations completion supported
  exact NativeGoldPcsAcceptanceSoundness.accepted_workers ctx.parameters ctx.query ctx.claimed ctx.opening work dummy shape
    (choose work) fuel memory middle (completion,after) continued next accepted

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsExecution
