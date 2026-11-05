module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsClaim
public import FormalProof4FHE.HasteBoots.NativeGoldPcsFinishComplete

@[expose] public section

/-! Computed pool completion followed by native suffix/claim enforcement.
This closes the pool tail, not the mixed-prefix/checkpoint-state coupling or
native Rayon/compiler refinement. Analysis suspension is not native Err. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance

open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeBrakedownContext (Parameters)
open NativeTranscript (Transcript)
open OracleSpec OracleComp

inductive Status where
  | accepted (transcript : Transcript)
  | columns
  | claim (reason : NativeGoldPcsClaim.Error)
  | suspended

noncomputable section

def failed (worker : OracleComp (Input →ₒ Digest) Bool) : Bool :=
  OracleComp.casesOn worker (fun value => !value) (fun _ _ => false)

def anyRejected {count : ℕ} (workers : HashWorkerPool.Workers Input Digest count) : Bool :=
  (List.ofFn (fun index => failed (workers index))).any id

theorem failed_iff (worker : OracleComp (Input →ₒ Digest) Bool) :
    failed worker = true ↔ worker = pure false := by
  constructor
  · intro rejected
    cases worker with
    | pure value =>
      cases value with
      | false => rfl
      | true => exact (Bool.false_ne_true rejected).elim
    | queryBind input next => exact (Bool.false_ne_true rejected).elim
  · intro rejected
    rw [rejected]
    rfl

theorem anyRejected_iff {count : ℕ} (workers : HashWorkerPool.Workers Input Digest count) :
    anyRejected workers = true ↔ ∃ index, workers index = pure false := by
  constructor
  · intro rejected
    obtain ⟨flag,member,same⟩ := List.any_eq_true.mp rejected
    obtain ⟨index,value⟩ := List.mem_ofFn.mp member
    exact ⟨index,(failed_iff _).mp (value.trans same)⟩
  · rintro ⟨index,rejected⟩
    apply List.any_eq_true.mpr
    exact ⟨failed (workers index),List.mem_ofFn.mpr ⟨index,rfl⟩,(failed_iff _).mpr rejected⟩

/-- Only the pool's computed all-accepted flag reaches claim checking. -/
def finish {C Memory : Type} (parameters : Parameters C) (query : Query) (opening : Opening) (claimed : Row)
    (work : Prepared) (pool : HashWorkerPool.Outcome Input Digest Memory work.jobs.length) : Status :=
  if HashWorkerPool.allAccepted pool.workers then
    match NativeGoldPcsClaim.verify parameters query opening.evaluation.val claimed with
    | .error reason => .claim reason
    | .ok () => .accepted work.transcript
  else if anyRejected pool.workers then .columns else .suspended

theorem accepted_iff {C Memory : Type} (parameters : Parameters C) (query : Query) (opening : Opening) (claimed : Row)
    (work : Prepared) (pool : HashWorkerPool.Outcome Input Digest Memory work.jobs.length) (next : Transcript) :
    finish parameters query opening claimed work pool = .accepted next ↔
      HashWorkerPool.allAccepted pool.workers = true ∧
      NativeGoldPcsClaim.verify parameters query opening.evaluation.val claimed = .ok () ∧ next = work.transcript := by
  unfold finish
  by_cases ready : HashWorkerPool.allAccepted pool.workers = true
  · rw [ite_eq_left ready]
    cases checked : NativeGoldPcsClaim.verify parameters query opening.evaluation.val claimed with
    | error reason => simp only [reduceCtorEq,ready,true_and,false_and]
    | ok value =>
      cases value
      simp only [Status.accepted.injEq,ready,true_and]
      exact eq_comm
  · rw [ite_eq_right ready]
    split <;> simp only [reduceCtorEq,ready,Bool.false_eq_true,false_and]

structure Completion (Memory : Type) (count : ℕ) where
  pool : HashWorkerPool.Outcome Input Digest Memory count
  status : Status

def program {C Cfg Memory : Type} (parameters : Parameters C) (query : Query) (opening : Opening) (claimed : Row)
    (work : Prepared)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Completion Memory work.jobs.length) :=
  (fun pool => ⟨pool,finish parameters query opening claimed work pool⟩) <$>
    NativeGoldPcsWorkerSoundness.program work choose fuel memory

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

variable {C Cfg Memory : Type} [SampleableType Digest]

/-- The pure tail retains exactly the actual pool state, memory and cache;
it adds no hidden hash/checkpoint/randomness computation. -/
theorem program_origin (parameters : Parameters C) (query : Query) (opening : Opening) (claimed : Row)
    (work : Prepared) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Completion Memory work.jobs.length × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program parameters query opening claimed work choose fuel memory)).run before)) :
    ∃ original, original ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before) ∧
      outcome = (⟨original.1,finish parameters query opening claimed work original.1⟩,original.2) := by
  rw [program,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
  obtain ⟨original,read,same⟩ := supported
  exact ⟨original,read,same.symm⟩

/-- Acceptance comes from actual accepted workers and the computed suffix
comparison, retaining the original pool result and final shared state. -/
theorem accepted_origin (parameters : Parameters C) (query : Query) (opening : Opening) (claimed : Row)
    (work : Prepared) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Completion Memory work.jobs.length × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
      (program parameters query opening claimed work choose fuel memory)).run before))
    (next : Transcript) (accepted : outcome.1.status = .accepted next) :
    (outcome.1.pool,outcome.2) ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before) ∧
      HashWorkerPool.allAccepted outcome.1.pool.workers = true ∧
      NativeGoldPcsClaim.verify parameters query opening.evaluation.val claimed = .ok () ∧ next = work.transcript := by
  obtain ⟨original,read,rfl⟩ := program_origin parameters query opening claimed work dummy shape choose fuel memory before outcome supported
  exact ⟨read,(accepted_iff parameters query opening claimed work original.1 next).mp accepted⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsAcceptance
