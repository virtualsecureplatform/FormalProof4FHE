module

public import FormalProof4FHE.HasteBoots.PreparedTerminal
public import FormalProof4FHE.HasteBoots.PackedZeroOracle

@[expose] public section

/-!
# Preparing original-factor values for a shared ZeroCheck opening

The public EQ terminal is computed from the retained ZeroCheck subclaim. Only
original-factor values are received and bound; failed terminal checks preserve
received memory and skip binding. This adapter retains every actual shared hash
call and exposes the fixed-source/wrong-original-factor alternative. Connection
to the concrete native opening loop remains a separate composition step.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedZeroOracle (Subclaim)

namespace FormalProof4FHE.HasteBoots.PreparedZeroTerminal

noncomputable section

variable {F Factor Term Memory Cfg Input Digest Payload : Type}
  [Field F] [DecidableEq F] [Fintype Term] {k n : ℕ}

abbrev Data := PreparedTerminal.Data

structure Packet (F Factor Memory : Type) (k n : ℕ) where
  earlier : Option (Subclaim F k n × Memory)
  data : Data F Factor Memory k

def query (nodes : PackedSumcheckRound.Node k ↪ F) (packet : Packet F Factor Memory k n) : PackedSumcheckSubclaim.Query F k (n + 1) :=
  match packet.earlier with | none => PreparedTerminal.zeroQuery (n + 1) | some entry => entry.1.query nodes

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
      if PackedZeroOracle.Subclaim.check arity coefficient indices proposal.1 entry.1 then
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

/-- Checked original values either make the actual returned ZeroCheck subclaim
truthful or expose a wrong original factor at its full query. -/
theorem checked_truthful_or_wrong (nodes : PackedSumcheckRound.Node k ↪ F)
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k) (packet : Packet F Factor Memory k n)
    (entry : Subclaim F k n × Memory) (earlier : packet.earlier = some entry)
    (checked : PackedZeroOracle.Subclaim.check arity coefficient indices packet.data.values entry.1 = true) :
    PackedZeroOracle.TruthfulResult nodes arity coefficient indices tables packet.earlier ∨
      ∃ factor, packet.data.values factor ≠ (query nodes packet).fold (tables factor) := by
  have alternative := PackedZeroOracle.Subclaim.checked_truthful_or_wrong nodes arity coefficient indices
    tables packet.data.values entry.1 checked
  simpa only [earlier, PackedZeroOracle.TruthfulResult, query] using alternative

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
      PackedZeroOracle.Subclaim.check arity coefficient indices outcome.1.values entry.1 = true := by
  cases earlier with
  | none =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact (Bool.false_ne_true enabled).elim
  | some entry =>
    rw [prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨proposal, _, rest⟩ := supported
    cases checked : PackedZeroOracle.Subclaim.check arity coefficient indices proposal.1.1 entry.1 with
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
      PackedZeroOracle.Subclaim.check arity coefficient indices outcome.1.data.values entry.1 = true := by
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

end FormalProof4FHE.HasteBoots.PreparedZeroTerminal
