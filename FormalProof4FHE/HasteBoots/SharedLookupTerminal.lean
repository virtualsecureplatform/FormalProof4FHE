module
public import FormalProof4FHE.HasteBoots.SharedLookupBatchSequence
public import FormalProof4FHE.HasteBoots.SharedLookupOpeningFamily
@[expose] public section

/-! Computed shared lookup terminal acceptance. Successful batch results
receive one global source vector family and one helper value per job. The
verifier computes every sum/helper and identity check before binding values.
Rejection retains receive work and skips binding. No decoded source is an
operational input. Native byte/field/transcript refinement remains separate. -/
open OracleSpec OracleComp BinaryTree
open scoped Classical
namespace FormalProof4FHE.HasteBoots.SharedLookupTerminal
noncomputable section

structure Values (F K : Type) (width count jobs : ℕ) where
  sources : Fin count → Fin width → F
  helpers : Fin jobs → K

structure Receiver (F K Memory Cfg Input Digest : Type) (width count jobs n : ℕ) where
  receive : SharedLookupBatchSequence.Points K jobs n →
    (SharedLookupBatchSequence.Equation jobs → PackedSumcheckSubclaim.Subclaim K 1 n) → Memory →
    OracleComp (SharedLookupBatchSequence.Shared Cfg Input Digest) (Values F K width count jobs × Memory)
  bindValues : SharedLookupOpeningFamily.Packet F K width count n jobs → Memory →
    OracleComp (SharedLookupBatchSequence.Shared Cfg Input Digest) Memory

variable {F K Memory Cfg Input Digest : Type} [Field F] [Field K] [Algebra F K]
  {d padding c row count jobs : ℕ} {columns : Fin jobs → ℕ}

/-- All jobs use the same point and global source family, gathering their
own ordered slot vectors. The pure checks precede any binding callback. -/
def guard (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (packet : SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs) : Bool :=
  (List.finRange jobs).all (fun job => decide (packet.sumExpected job = packet.helpers job) &&
    LookupPairTerminal.check basis shape (packet.equalityPoints job) packet.point (pairs job).2 (pairs job).1
      (active job) (enough job) (fun column => packet.sources (slots job column))
      (packet.helpers job) (packet.identityExpected job))

theorem guard_spec (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (slots : (job : Fin jobs) → Fin (columns job) → Fin count) (pairs : Fin jobs → K × K)
    (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (packet : SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs)
    (accepted : guard basis shape slots pairs active enough packet = true) (job : Fin jobs) :
    packet.sumExpected job = packet.helpers job ∧
      LookupPairTerminal.check basis shape (packet.equalityPoints job) packet.point (pairs job).2 (pairs job).1
        (active job) (enough job) (fun column => packet.sources (slots job column))
        (packet.helpers job) (packet.identityExpected job) = true := by
  have checked := List.all_eq_true.mp accepted job (List.mem_finRange job)
  obtain ⟨sumCheck,identityCheck⟩ := Bool.and_eq_true_iff.mp checked
  exact ⟨of_decide_eq_true sumCheck,identityCheck⟩

def prepare (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (receiver : Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (earlier : SharedLookupBatchSequence.Result K Memory jobs (c + row)) :
    OracleComp (SharedLookupBatchSequence.Shared Cfg Input Digest)
      (Option (SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs × Memory)) :=
  match earlier.2 with
  | none => pure none
  | some entry => do
    let proposal ← receiver.receive earlier.1.1 entry.1 entry.2
    let packet := SharedLookupOpeningFamily.ofBatch entry.1 (⟨0,jobsPositive⟩,false)
      proposal.1.sources proposal.1.helpers earlier.1.1
    if guard basis shape slots pairs active enough packet = true then
      let memory ← receiver.bindValues packet proposal.2
      pure (some (packet,memory))
    else pure none

variable {Payload : Type} [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- A returned packet is built from the actual batch subclaims and equality
points and has passed the computed guard. No acceptance bit is supplied. -/
theorem prepare_sound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (receiver : Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (earlier : SharedLookupBatchSequence.Result K Memory jobs (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : Option (SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs × Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (prepare basis shape jobsPositive slots pairs active enough receiver earlier)).run before))
    (packet : SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs) (memory : Memory)
    (returned : outcome.1 = some (packet,memory)) :
    ∃ claims batchMemory, earlier.2 = some (claims,batchMemory) ∧
      packet = SharedLookupOpeningFamily.ofBatch claims (⟨0,jobsPositive⟩,false)
        packet.sources packet.helpers earlier.1.1 ∧
      guard basis shape slots pairs active enough packet = true := by
  cases batchResult : earlier.2 with
  | none =>
    simp only [prepare,batchResult,simulateQ_pure,StateT.run_pure] at supported
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases returned
  | some entry =>
    simp only [prepare,batchResult,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨proposal,_,rest⟩ := supported
    by_cases checked : guard basis shape slots pairs active enough
        (SharedLookupOpeningFamily.ofBatch entry.1 (⟨0,jobsPositive⟩,false)
          proposal.1.1.sources proposal.1.1.helpers earlier.1.1) = true
    · simp only [checked,reduceIte,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at rest
      obtain ⟨newMemory,_,done⟩ := rest
      have equal := eq_of_mem_support_pure _ done
      subst outcome
      have samePacket := congrArg Prod.fst (Option.some.inj returned)
      dsimp only at samePacket
      subst packet
      exact ⟨entry.1,entry.2,rfl,rfl,checked⟩
    · simp only [checked] at rest
      have equal := eq_of_mem_support_pure _ rest
      subst outcome
      cases returned

variable {Message : Type} [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]

/-- The entire ordered EQ/batch, receipt, computed guard, and successful
binding execute on the same shared oracle state. -/
def program (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs (c + row))
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (totals : Fin jobs → K) (memory : Memory)
    (receiver : Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row)) :=
  SharedContinuation.program (SharedLookupBatchSequence.program p small schedule totals memory)
    (prepare basis shape jobsPositive slots pairs active enough receiver)
/-- Successful full executions derive the packet's original batch association
and common-query invariant internally, together with the computed checks. -/
theorem accepted_data (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (workerShape : Cfg → Skeleton)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (schedule : SharedLookupBatchSequence.Schedule K Message Memory Cfg Input Digest jobs (c + row))
    (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (jobsPositive : 0 < jobs) (slots : (job : Fin jobs) → Fin (columns job) → Fin count)
    (pairs : Fin jobs → K × K) (active : Fin jobs → ℕ) (enough : ∀ job, active job ≤ 2 ^ (c + row))
    (totals : Fin jobs → K) (memory : Memory)
    (receiver : Receiver F K Memory Cfg Input Digest (d + padding) count jobs (c + row))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (outcome : (SharedLookupBatchSequence.Result K Memory jobs (c + row) ×
      Option (SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs × Memory)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) workerShape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy workerShape)
      (program p small schedule basis shape jobsPositive slots pairs active enough totals memory receiver)).run before))
    (packet : SharedLookupOpeningFamily.Packet F K (d + padding) count (c + row) jobs) (finalMemory : Memory)
    (returned : outcome.1.2 = some (packet,finalMemory)) :
    ∃ claims batchMemory, outcome.1.1.2 = some (claims,batchMemory) ∧
      SharedScalarBatchQuery.Valid (some (claims,())) ∧
      packet = SharedLookupOpeningFamily.ofBatch claims (⟨0,jobsPositive⟩,false)
        packet.sources packet.helpers outcome.1.1.1.1 ∧
      guard basis shape slots pairs active enough packet = true := by
  obtain ⟨earlier,earlierSupported,later,laterSupported,equal⟩ :=
    (SharedContinuation.support_program enc dummy workerShape
      (SharedLookupBatchSequence.program p small schedule totals memory)
      (prepare basis shape jobsPositive slots pairs active enough receiver) before outcome).mp supported
  subst outcome
  have valid := SharedLookupBatchSequence.valid_result enc dummy workerShape p small schedule totals memory before earlier earlierSupported
  obtain ⟨claims,batchMemory,batchEq,origin,checked⟩ := prepare_sound enc dummy workerShape basis shape
    jobsPositive slots pairs active enough receiver earlier.1 earlier.2 later laterSupported packet finalMemory returned
  refine ⟨claims,batchMemory,batchEq,?_,origin,checked⟩
  rw [batchEq] at valid
  exact valid

end
end FormalProof4FHE.HasteBoots.SharedLookupTerminal
