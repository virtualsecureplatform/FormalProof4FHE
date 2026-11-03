module

public import FormalProof4FHE.HasteBoots.PackedLinear
public import FormalProof4FHE.HasteBoots.PreparedTerminal

@[expose] public section

/-!
# Common-query linear checking on the actual shared oracle execution

Enabled trusted shapes bind contexts/relations before sampling one matrix
query. The proposer then returns all source values and private memory. The
verifier computes the linear-check flag; it adds no separate value-binding
callback before that check. Opening-specific claim binding belongs inside
each later single opening. Disabled shapes issue no bind, coins or reception.
The truthful-value event is bounded here and discharged by actual PCS later.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PackedLinearOracle

noncomputable section

structure Packet (F Factor Memory : Type) (b n : ℕ) where
  query : Query F b n
  values : Factor → Fin b → F
  memory : Memory
  accepted : Bool

variable {F Factor Memory Cfg Input Digest Payload : Type} [Field F] [DecidableEq F] {b n : ℕ}

def packet (relations : List (PackedLinear.Relation F Factor))
    (result : Query F b n × (Factor → Fin b → F) × Memory) : Packet F Factor Memory b n :=
  ⟨result.1, result.2.1, result.2.2, PackedLinear.check relations result.2.1⟩

def disabled (memory : Memory) : Packet F Factor Memory b n :=
  ⟨PreparedTerminal.zeroQuery n, fun _ _ => 0, memory, false⟩

variable [SampleableType (Fin b → F)]

def program (nodes : PackedSumcheckRound.Node b ↪ F) (relations : List (PackedLinear.Relation F Factor))
    (enabled : Bool) (before : OracleComp (SharedSequence.Shared Cfg Input Digest) Memory)
    (receive : Memory → Query F b n → OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Fin b → F) × Memory))
    (fallback : Memory) : OracleComp (SharedSequence.Shared Cfg Input Digest) (Packet F Factor Memory b n) :=
  if enabled then do
    let memory ← before
    packet relations <$> SharedContinuation.program
      (PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample nodes n)) (receive memory)
  else pure (disabled fallback)

def Truthful (sources : Factor → MatrixFold.Cube n → Fin b → F) (result : Packet F Factor Memory b n) : Prop :=
  result.accepted = true ∧ ∀ factor, result.values factor = result.query.fold (sources factor)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype F]

/-- Arbitrary bind and receive work keep the fixed-source arithmetic bound.
There is one query for the whole relation/source family, with no size factor. -/
theorem truthful_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F) (relations : List (PackedLinear.Relation F Factor))
    (enabled : Bool) (before : OracleComp (SharedSequence.Shared Cfg Input Digest) Memory)
    (receive : Memory → Query F b n → OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Fin b → F) × Memory))
    (fallback : Memory) (sources : Factor → MatrixFold.Cube n → Fin b → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseClaim : ¬PackedLinear.Holds relations sources) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes relations enabled before receive fallback)).run state}[Truthful sources outcome.1] ≤
      (n : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  cases enabled with
  | false => simp [program, disabled, Truthful, prEvent_norm]
  | true =>
    rw [program, ite_eq_left rfl, simulateQ_bind, StateT.run_bind]
    apply prEvent_bind_le_of_forall_le
    intro prepared
    rw [simulateQ_map, StateT.run_map, prEvent_map]
    have retained := SharedContinuation.earlier_event_le enc dummy shape
      (PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample nodes n)) (receive prepared.1) prepared.2
      (fun query => ∀ relation ∈ relations, query.fold (PackedLinear.residual relation sources) = 0)
    have arithmetic := PackedLinear.agreement_bound nodes relations sources falseClaim
    have bound := retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_norm] using arithmetic)
    apply le_trans (prEvent_mono _ _ _ ?_) bound
    intro outcome truthful
    exact PackedLinear.truthful_agreement relations sources outcome.1.1 outcome.1.2.1 truthful.1 truthful.2

end

end FormalProof4FHE.HasteBoots.PackedLinearOracle
