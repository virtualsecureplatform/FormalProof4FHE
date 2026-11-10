module

public import FormalProof4FHE.HasteBoots.PreparedTerminal
public import FormalProof4FHE.HasteBoots.PackedZeroOracle

@[expose] public section

/-! Prepare a ZeroCheck terminal with private values and verifier-computed
public factors. Only private values are received/bound/opened; the public
folds and EQ value are derived from the retained full query. Every actual
receive/bind call, rejected outcome and shared cache is retained. -/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedZeroOracle (Subclaim)

namespace FormalProof4FHE.HasteBoots.PreparedPublicZeroTerminal

noncomputable section

variable {F Private Public Term Memory Cfg Input Digest Payload : Type}
  [Field F] [DecidableEq F] [Fintype Term] {k n : ℕ}

abbrev Data := PreparedTerminal.Data

structure Packet (F Private Memory : Type) (k n : ℕ) where
  earlier : Option (Subclaim F k n × Memory)
  data : Data F Private Memory k

def query (nodes : PackedSumcheckRound.Node k ↪ F) (packet : Packet F Private Memory k n) : PackedSumcheckSubclaim.Query F k (n + 1) :=
  match packet.earlier with | none => PreparedTerminal.zeroQuery (n + 1) | some entry => entry.1.query nodes

def values (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (claimed : Private → Fin k → F) (claim : Subclaim F k n) : Sum Private Public → Fin k → F :=
  Sum.elim claimed (fun factor => (claim.query nodes).fold (publicTables factor))

def prepare (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Sum Private Public)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Private → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Private → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) : Option (Subclaim F k n × Memory) →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Data F Private Memory k)
  | none => pure ⟨fun _ _ => 0, fallback, false⟩
  | some entry => do
      let proposal ← receiveValues entry.1 entry.2
      if PackedZeroOracle.Subclaim.check arity coefficient indices (values nodes publicTables proposal.1 entry.1) entry.1 then
        let memory ← bindValues entry.1 proposal.1 proposal.2
        pure ⟨proposal.1, memory, true⟩
      else pure ⟨proposal.1, proposal.2, false⟩

/-- Retaining the earlier subclaim does not introduce oracle calls. -/
def select (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (before : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)))
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Sum Private Public)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Private → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Private → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Packet F Private Memory k n) :=
  (fun pair => ⟨pair.1, pair.2⟩) <$> SharedContinuation.program before
    (prepare nodes publicTables arity coefficient indices receiveValues bindValues fallback)

/-- Computed public factors cannot contribute a wrong-value alternative. -/
theorem checked_truthful_or_wrong_private (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Sum Private Public)
    (privateTables : Private → MatrixFold.Cube (n+1) → Fin k → F)
    (packet : Packet F Private Memory k n) (entry : Subclaim F k n × Memory)
    (earlier : packet.earlier = some entry)
    (checked : PackedZeroOracle.Subclaim.check arity coefficient indices
      (values nodes publicTables packet.data.values entry.1) entry.1 = true) :
    PackedZeroOracle.TruthfulResult nodes arity coefficient indices (Sum.elim privateTables publicTables) packet.earlier ∨
      ∃ factor, packet.data.values factor ≠ (query nodes packet).fold (privateTables factor) := by
  rcases PackedZeroOracle.Subclaim.checked_truthful_or_wrong nodes arity coefficient indices
    (Sum.elim privateTables publicTables) (values nodes publicTables packet.data.values entry.1) entry.1 checked with truthful | ⟨factor,wrong⟩
  · left
    simpa only [earlier,PackedZeroOracle.TruthfulResult] using truthful
  · right
    cases factor with
    | inl factor =>
      refine ⟨factor,?_⟩
      simpa only [earlier,query,values,Sum.elim_inl] using wrong
    | inr factor => exact False.elim (wrong rfl)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Success of preparation proves that the actual earlier subclaim was present
and its supplied values passed the literal terminal identity check. -/
theorem prepare_sound (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Sum Private Public)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Private → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Private → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) (earlier : Option (Subclaim F k n × Memory))
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Data F Private Memory k × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (prepare nodes publicTables arity coefficient indices receiveValues bindValues fallback earlier)).run before))
    (enabled : outcome.1.enabled = true) :
    ∃ entry, earlier = some entry ∧
      PackedZeroOracle.Subclaim.check arity coefficient indices (values nodes publicTables outcome.1.values entry.1) entry.1 = true := by
  cases earlier with
  | none =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact (Bool.false_ne_true enabled).elim
  | some entry =>
    rw [prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨proposal, _, rest⟩ := supported
    cases checked : PackedZeroOracle.Subclaim.check arity coefficient indices (values nodes publicTables proposal.1.1 entry.1) entry.1 with
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
theorem earlier_event_le (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)))
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Sum Private Public)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Private → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Private → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (event : Option (Subclaim F k n × Memory) → Prop) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (select nodes publicTables before arity coefficient indices receiveValues bindValues fallback)).run state}[event outcome.1.earlier] ≤
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) before).run state}[event outcome.1] := by
  rw [select, simulateQ_map, StateT.run_map, prEvent_map]
  exact SharedContinuation.earlier_event_le enc dummy shape before
    (prepare nodes publicTables arity coefficient indices receiveValues bindValues fallback) state event

/-- A prepared packet that enables opening contains its real checked subclaim. -/
theorem select_sound (nodes : PackedSumcheckRound.Node k ↪ F)
    (publicTables : Public → MatrixFold.Cube (n+1) → Fin k → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) (Option (Subclaim F k n × Memory)))
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Sum Private Public)
    (receiveValues : Subclaim F k n → Memory → OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest)
      ((Private → Fin k → F) × Memory))
    (bindValues : Subclaim F k n → (Private → Fin k → F) → Memory →
      OracleComp (PackedSumcheckOracle.Shared Cfg Input Digest) Memory)
    (fallback : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Packet F Private Memory k n × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (select nodes publicTables before arity coefficient indices receiveValues bindValues fallback)).run state))
    (enabled : outcome.1.data.enabled = true) :
    ∃ entry, outcome.1.earlier = some entry ∧
      PackedZeroOracle.Subclaim.check arity coefficient indices (values nodes publicTables outcome.1.data.values entry.1) entry.1 = true := by
  rw [select, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨packet, packetSupported, equal⟩ := supported
  subst outcome
  obtain ⟨earlier, _, prepared, preparedSupported, packetEqual⟩ :=
    (SharedContinuation.support_program enc dummy shape before
      (prepare nodes publicTables arity coefficient indices receiveValues bindValues fallback) state packet).mp packetSupported
  subst packet
  exact prepare_sound nodes publicTables enc dummy shape arity coefficient indices receiveValues bindValues fallback earlier.1
    earlier.2 prepared preparedSupported enabled

end

end FormalProof4FHE.HasteBoots.PreparedPublicZeroTerminal
