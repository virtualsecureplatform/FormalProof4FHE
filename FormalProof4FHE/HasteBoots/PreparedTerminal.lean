module

public import FormalProof4FHE.HasteBoots.GuardedSumcheckTerminal

@[expose] public section

/-!
# Preparing checked terminal values before native openings

This normal form separates terminal receive/check/bind work from the subsequent
factor loop while retaining the original returned subclaim and private memory.
The program-level equality with `GuardedSumcheckTerminal.finish` preserves all
actual calls on accepted and rejected paths. Default query/value data are used
only to make rejected outcomes total; a successful preparation supplies the
actual earlier subclaim and its checked values.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PreparedTerminal

noncomputable section

variable {F Factor Term Memory Cfg Input Digest Payload : Type}
  [Field F] [DecidableEq F] [Fintype Term] {k n : ℕ}

/-- Total placeholder for a disabled terminal outcome; it issues no queries. -/
def zeroQuery : (n : ℕ) → Query F k n
  | 0 => .nil
  | n + 1 => .cons (fun _ => 0) (zeroQuery n)

structure Data (F Factor Memory : Type) (k : ℕ) where
  values : Factor → Fin k → F
  memory : Memory
  enabled : Bool

structure Packet (F Factor Memory : Type) (k n : ℕ) where
  earlier : Option (Subclaim F k n × Memory)
  data : Data F Factor Memory k

def query (packet : Packet F Factor Memory k n) : Query F k n :=
  match packet.earlier with | none => zeroQuery n | some entry => entry.1.query

def prepare (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) : Option (Subclaim F k n × Memory) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Data F Factor Memory k)
  | none => pure ⟨fun _ _ => 0, fallback, false⟩
  | some entry => do
      let proposal ← receiveValues entry.1 entry.2
      if PackedSumcheckTerminalOracle.check arity coefficient indices proposal.1 entry.1.expected then
        let memory ← bindValues entry.1 proposal.1 proposal.2
        pure ⟨proposal.1, memory, true⟩
      else pure ⟨proposal.1, proposal.2, false⟩

/-- Retaining the earlier subclaim does not introduce oracle calls. -/
def select (before : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)))
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Packet F Factor Memory k n) :=
  (fun pair => ⟨pair.1, pair.2⟩) <$> SharedContinuation.program before
    (prepare arity coefficient indices receiveValues bindValues fallback)

/-- Running the prepared factor loop is exactly the existing guarded terminal
program, including its failed-check and first-failed-opening branches. -/
def finish {Opening : Type} (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (openOne : Subclaim F k n → (Factor → Fin k → F) → Factor → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Opening Memory))
    (factors : List Factor) (fallback : Memory) (earlier : Option (Subclaim F k n × Memory)) := do
  let data ← prepare arity coefficient indices receiveValues bindValues fallback earlier
  match earlier with
  | none => pure none
  | some entry =>
      if data.enabled then do
        let opened ← ShortCircuitSequence.program (openOne entry.1 data.values) factors data.memory
        pure (some ((data.values, opened.memory), some opened))
      else pure (some ((data.values, data.memory), none))

theorem finish_eq {Opening : Type} (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (openOne : Subclaim F k n → (Factor → Fin k → F) → Factor → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult Opening Memory))
    (factors : List Factor) (fallback : Memory) (earlier : Option (Subclaim F k n × Memory)) :
    finish arity coefficient indices receiveValues bindValues openOne factors fallback earlier =
      GuardedSumcheckTerminal.finish arity coefficient indices receiveValues bindValues openOne factors earlier := by
  cases earlier with
  | none => rfl
  | some entry =>
    simp only [finish, prepare, GuardedSumcheckTerminal.finish, bind_assoc]
    congr 1
    funext proposal
    cases PackedSumcheckTerminalOracle.check arity coefficient indices proposal.1 entry.1.expected <;>
      simp only [Bool.false_eq_true, reduceIte, bind_assoc, pure_bind]

/-- The checked terminal identity either makes the retained subclaim truthful
on the fixed sources or exposes a wrong supplied factor at that same query. -/
theorem checked_truthful_or_wrong (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor n k) (packet : Packet F Factor Memory k n)
    (entry : Subclaim F k n × Memory) (earlier : packet.earlier = some entry)
    (checked : PackedSumcheckTerminalOracle.check arity coefficient indices packet.data.values entry.1.expected = true) :
    PackedSumcheckOracle.TruthfulResult arity coefficient indices tables packet.earlier ∨
      ∃ factor, packet.data.values factor ≠ (query packet).fold (tables factor) := by
  classical
  by_cases wrong : ∃ factor, packet.data.values factor ≠ (query packet).fold (tables factor)
  · exact Or.inr wrong
  left
  have sameQuery : query packet = entry.1.query := by simp only [query, earlier]
  have correct : packet.data.values = fun factor => entry.1.query.fold (tables factor) := by
    funext factor
    by_contra different
    exact wrong ⟨factor, by simpa only [sameQuery] using different⟩
  have identity := (PackedSumcheckTerminalOracle.check_iff arity coefficient indices packet.data.values entry.1.expected).mp checked
  rw [correct] at identity
  rw [earlier]
  exact funext (fun lane => (identity lane).symm)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Success of preparation proves that the actual earlier subclaim was present
and its supplied values passed the literal terminal identity check. -/
theorem prepare_sound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) (earlier : Option (Subclaim F k n × Memory))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Data F Factor Memory k × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (prepare arity coefficient indices receiveValues bindValues fallback earlier)).run before))
    (enabled : outcome.1.enabled = true) :
    ∃ entry, earlier = some entry ∧
      PackedSumcheckTerminalOracle.check arity coefficient indices outcome.1.values entry.1.expected = true := by
  cases earlier with
  | none =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact (Bool.false_ne_true enabled).elim
  | some entry =>
    rw [prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨proposal, _, rest⟩ := supported
    cases checked : PackedSumcheckTerminalOracle.check arity coefficient indices proposal.1.1 entry.1.expected with
    | false =>
      simp only [checked, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at rest
      have equal := eq_of_mem_support_pure _ rest
      subst outcome
      exact (Bool.false_ne_true enabled).elim
    | true =>
      simp only [checked, reduceIte, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨memory, _, returned⟩ := rest
      have equal := eq_of_mem_support_pure _ returned
      subst outcome
      exact ⟨entry, rfl, checked⟩

/-- The retained earlier event cannot gain probability during value reception
or binding. This includes every actual preparation call and final shared state. -/
theorem earlier_event_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)))
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (event : Option (Subclaim F k n × Memory) → Prop) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (select before arity coefficient indices receiveValues bindValues fallback)).run state}[event outcome.1.earlier] ≤
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) before).run state}[event outcome.1] := by
  rw [select, simulateQ_map, StateT.run_map, prEvent_map]
  exact SharedContinuation.earlier_event_le enc dummy shape before
    (prepare arity coefficient indices receiveValues bindValues fallback) state event

/-- A prepared packet that enables opening contains its real checked subclaim. -/
theorem select_sound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)))
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Factor → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Factor → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Packet F Factor Memory k n × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (select before arity coefficient indices receiveValues bindValues fallback)).run state))
    (enabled : outcome.1.data.enabled = true) :
    ∃ entry, outcome.1.earlier = some entry ∧
      PackedSumcheckTerminalOracle.check arity coefficient indices outcome.1.data.values entry.1.expected = true := by
  rw [select, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨packet, packetSupported, equal⟩ := supported
  subst outcome
  obtain ⟨earlier, _, prepared, preparedSupported, packetEqual⟩ :=
    (SharedContinuation.support_program enc dummy shape before
      (prepare arity coefficient indices receiveValues bindValues fallback) state packet).mp packetSupported
  subst packet
  exact prepare_sound enc dummy shape arity coefficient indices receiveValues bindValues fallback earlier.1
    earlier.2 prepared preparedSupported enabled

end

end FormalProof4FHE.HasteBoots.PreparedTerminal
