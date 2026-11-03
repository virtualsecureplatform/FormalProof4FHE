module

public import FormalProof4FHE.HasteBoots.NTTRowCheck
public import FormalProof4FHE.HasteBoots.SharedContinuation
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# Shared execution of the NTT row-check prefix

Private tensor points precede an arbitrary adaptive row proposal. The actual
shared binding callback runs before the verifier computes the local transform
checks, including on rejected proposals. The retained points and actual cache
support the row-miss probability bound with arbitrary proposer/binder work.
False accepted rows reduce to that error or an accepted wrong proposed row.
Independent coefficient compression and authenticated source openings still
have to bound the latter event; no row-authentication certificate is assumed.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.NTTRowOracle

noncomputable section

structure Proposal (F Position Memory : Type) (k : ℕ) where
  coefficients : Fin k → Position → F
  evaluations : Fin k → Position → F
  memory : Memory

structure Checked (F Position Memory : Type) (k : ℕ) where
  proposal : Proposal F Position Memory k
  accepted : Bool

variable {F Position Memory Cfg Input Digest Payload : Type} [Field F] [DecidableEq F] [Fintype Position]
  {r k : ℕ} [SampleableType (Fin k → Fin r → F)]

/-- Native append-before-check order: binding work is issued even when the
proposed transform identity fails. Binding may change private memory only. -/
def next (transform : (Position → F) →ₗ[F] (Position → F))
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory) (points : Fin k → Fin r → F) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Checked F Position Memory k) := do
  let proposal ← receive points memory
  let retained ← bindRows points proposal
  pure ⟨{ proposal with memory := retained }, NTTRowCheck.check transform proposal.coefficients proposal.evaluations⟩

def program (transform : (Position → F) →ₗ[F] (Position → F))
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory) :=
  SharedContinuation.program
    (PrivateSampling.embed Cfg Input Digest ($ᵗ (Fin k → Fin r → F)))
    (next transform receive bindRows memory)

def WrongAccepted (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (result : (Fin k → Fin r → F) × Checked F Position Memory k) : Prop :=
  result.2.accepted = true ∧ ∃ repetition,
    result.2.proposal.coefficients repetition ≠ NTTRowCheck.fold (result.1 repetition) coefficients ∨
    result.2.proposal.evaluations repetition ≠ NTTRowCheck.fold (result.1 repetition) evaluations

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

omit [SampleableType (Fin k → Fin r → F)] in
/-- Every successful local result computes its flag from the actual received
polynomial pairs, after binding them on the actual shared state. -/
theorem next_checked (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (transform : (Position → F) →ₗ[F] (Position → F))
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory) (points : Fin k → Fin r → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Checked F Position Memory k × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (next transform receive bindRows memory points)).run state)) :
    outcome.1.accepted = NTTRowCheck.check transform outcome.1.proposal.coefficients outcome.1.proposal.evaluations := by
  rw [next, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨proposal, _, rest⟩ := supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at rest
  obtain ⟨retained, _, returned⟩ := rest
  have equal := eq_of_mem_support_pure _ returned
  subst outcome
  rfl

/-- The earlier row-miss event cannot gain probability while arbitrary actual
proposer and binding work runs on the same cache. -/
theorem miss_bound [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬NTTRowCheck.Relation transform coefficients evaluations) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program transform receive bindRows memory)).run state}[
        NTTRowCheck.RowsPass transform coefficients evaluations outcome.1.1] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest ($ᵗ (Fin k → Fin r → F)))
    (next transform receive bindRows memory) state (NTTRowCheck.RowsPass transform coefficients evaluations)
  have bound := NTTRowCheck.miss_bound (k := k) transform coefficients evaluations falseRelation
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_norm] using bound)

/-- Later compression and opening work retains this same row-miss bound;
every actual later hash remains in the complete shared execution. -/
theorem continued_miss_bound {Later : Type} [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory)
    (later : ((Fin k → Fin r → F) × Checked F Position Memory k) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬NTTRowCheck.Relation transform coefficients evaluations) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (program transform receive bindRows memory) later)).run state}[
        NTTRowCheck.RowsPass transform coefficients evaluations outcome.1.1.1] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) :=
  (SharedContinuation.earlier_event_le enc dummy shape (program transform receive bindRows memory) later state
    (fun result => NTTRowCheck.RowsPass transform coefficients evaluations result.1)).trans
      (miss_bound enc dummy shape transform coefficients evaluations receive bindRows memory state falseRelation)

/-- Accepted local prefixes expose the row-miss event or a wrong original
fold. This obligation is on the actual execution, never an opener certificate. -/
theorem accepted_implies_risks
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((Fin k → Fin r → F) × Checked F Position Memory k) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program transform receive bindRows memory)).run state))
    (accepted : outcome.1.2.accepted = true) :
    NTTRowCheck.RowsPass transform coefficients evaluations outcome.1.1 ∨ WrongAccepted coefficients evaluations outcome.1 := by
  obtain ⟨points, _, checked, checkedSupported, equal⟩ :=
    (SharedContinuation.support_program enc dummy shape _ _ state outcome).mp supported
  subst outcome
  have computed := next_checked enc dummy shape transform receive bindRows memory points.1 points.2 checked checkedSupported
  rw [computed] at accepted
  obtain missed | wrong := NTTRowCheck.checked_miss_or_wrong transform coefficients evaluations points.1
    checked.1.proposal.coefficients checked.1.proposal.evaluations accepted
  · exact Or.inl missed
  · exact Or.inr ⟨computed.trans accepted, wrong⟩

/-- The exact joint wrong-row event remains explicit until independent
compression and concrete source openings discharge it. -/
theorem soundness_reduction [Fintype F] [SampleableType F] [SampleableType (Fin r → F)]
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (receive : (Fin k → Fin r → F) → Memory → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Proposal F Position Memory k))
    (bindRows : (Fin k → Fin r → F) → Proposal F Position Memory k →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (falseRelation : ¬NTTRowCheck.Relation transform coefficients evaluations) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program transform receive bindRows memory)).run state}[outcome.1.2.accepted = true] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) +
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program transform receive bindRows memory)).run state}[WrongAccepted coefficients evaluations outcome.1] := by
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    NTTRowCheck.RowsPass transform coefficients evaluations outcome.1.1 ∨ WrongAccepted coefficients evaluations outcome.1) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add
      (miss_bound enc dummy shape transform coefficients evaluations receive bindRows memory state falseRelation) le_rfl)
  · intro outcome supported accepted
    exact accepted_implies_risks enc dummy shape transform coefficients evaluations receive bindRows memory state outcome supported accepted

end

end FormalProof4FHE.HasteBoots.NTTRowOracle
