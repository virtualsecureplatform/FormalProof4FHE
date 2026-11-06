module

public import FormalProof4FHE.HasteBoots.CausalHashWorkerPool
public import FormalProof4FHE.HasteBoots.NativeGoldPcsExecution
@[expose] public section

/-! The original checked native PCS prefix, interleaved raw workers and
computed suffix/claim acceptance in one causal mixed-oracle program.
No functional SHAKE reader or supplied pool/prefix-success certificate is
used. Raw authentication follows in the common history cache. Availability,
global Fiat–Shamir bounds, physical work and Rust/Rayon refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript Observation)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsExecution (Context)
open OracleProgram (Program bind run)
open OracleSpec OracleComp
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev Scheduler (Memory : Type) := (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
  Program (Option (Fin work.jobs.length) × Memory)

def workers (work : Prepared) := NativeGoldColumnWorker.workers work.geometry work.width work.random work.structured
  work.test work.evaluation work.root work.jobs

inductive Outcome (Memory : Type) where
  | prefix (prior : NativeGoldPcsWorkers.Outcome)
  | completed (work : Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)

def program {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) : Program (Outcome Memory) :=
  bind ctx.prefix (fun prior => match prior with
  | .prepared work => bind (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) (fun pool =>
      .pure (.completed work ⟨pool,NativeGoldPcsAcceptance.finish ctx.parameters ctx.query ctx.opening ctx.claimed work pool⟩))
  | prior => .pure (.prefix prior))

structure Origin {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length) : Prop where
  prepared : (run ctx.prefix world).run.1 = .prepared work
  pool : completion.pool = (run (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) world).run.1
  status : completion.status = NativeGoldPcsAcceptance.finish ctx.parameters ctx.query ctx.opening ctx.claimed work completion.pool
  log : (run (program ctx choose fuel memory) world).run.2 =
    (run ctx.prefix world).run.2 ++ (run (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) world).run.2

theorem completed_origin {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion) :
    Origin ctx choose fuel memory world work completion := by
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind] at executed
  cases prior : (run ctx.prefix world).run.1 with
  | «prefix» previous => simp only [prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | pairingUnavailable => simp only [prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | prepared original =>
    simp only [prior,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed
    cases executed
    refine ⟨prior,rfl,rfl,?_⟩
    simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind,prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem accepted_flags {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (next : Transcript) (accepted : completion.status = .accepted next) :
    HashWorkerPool.allAccepted completion.pool.workers = true ∧
      NativeGoldPcsClaim.verify ctx.parameters ctx.query ctx.opening.evaluation.val ctx.claimed = .ok () ∧ next = work.transcript := by
  have origin := completed_origin ctx choose fuel memory world work completion executed
  rw [origin.status] at accepted
  exact (NativeGoldPcsAcceptance.accepted_iff _ _ _ _ _ _ _).mp accepted

theorem accepted_value {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (next : Transcript) (accepted : completion.status = .accepted next) :
    next = work.transcript ∧ ctx.claimed.val.map NativeFieldRepresentation.goldValue = List.ofFn (FlatMatrixFold.foldAll
      ((ctx.query.models.drop ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val))
      (fun index lane => NativeFieldRepresentation.goldValue
        (ctx.opening.evaluation.val[lane.val*2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)+index.val]?.getD 0))) := by
  have origin := completed_origin ctx choose fuel memory world work completion executed
  have flags := accepted_flags ctx choose fuel memory world work completion executed next accepted
  have query := (NativeGoldPcsFinishComplete.prepared_finish ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel
    world work origin.prepared).1
  exact ⟨flags.2.2,NativeGoldPcsClaim.accepted_value _ _ _ _ query flags.2.1⟩

/-- Authentication and both coordinate checks use the final common cache of this whole causal run. -/
theorem accepted_workers {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (world : World) (work : Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (next : Transcript) (accepted : completion.status = .accepted next)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (program ctx choose fuel memory) world).run.2.Sublist history) :
    ∀ job ∈ work.jobs, ∃ leaf siblings, NativeGoldColumnAuthentication.decodePath work.geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ (JointHashCache.project history).cache.toPartialImpl
        (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding work.geometry.height job.index job.column.values leaf work.root siblings) = some true ∧
      NativeGoldColumnChecks.check work.geometry work.width work.random work.structured work.test work.evaluation job.column.values.val job.index = true := by
  have origin := completed_origin ctx choose fuel memory world work completion executed
  have flags := (accepted_flags ctx choose fuel memory world work completion executed next accepted).1
  have poolAccepted := flags
  rw [origin.pool] at poolAccepted
  have known : CausalHashWorkerPool.Known
      (JointHashCache.project history).cache
      (run (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) world).run.2 := by
    intro input digest member
    have contained : Observation.hash input (List.ofFn digest) ∈ (run (program ctx choose fuel memory) world).run.2 := by
      rw [origin.log]
      exact List.mem_append_right _ member
    exact NativeHashOracleBridge.cache_known world _ truthful input digest
      (observed.subset contained)
  intro job member
  obtain ⟨index,same⟩ := List.mem_iff_get.mp member
  subst job
  exact NativeGoldColumnWorker.worker_raw_replay _ _ _ _ _ _ _ _ _ _
    (CausalHashWorkerPool.accepted_replays (choose work) fuel (workers work) memory world _ known poolAccepted index)

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
