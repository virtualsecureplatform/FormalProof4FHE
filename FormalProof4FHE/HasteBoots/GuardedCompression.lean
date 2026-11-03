module

public import FormalProof4FHE.HasteBoots.MatrixCompression
public import FormalProof4FHE.HasteBoots.SharedContinuation
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# One guarded fresh compression query after adaptive shared work

An actual earlier program fixes a whole family of proposed and correct rows.
If enabled, one fresh query is shared by all rows, followed by arbitrary actual
shared work. Rejection samples no compression coins and skips that callback.
The probability that some fixed row was wrong but every compressed row agrees
is bounded once, independently of the number of rows and retained cache state.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.GuardedCompression

noncomputable section

variable {F Row Earlier Later Cfg Input Digest Payload : Type} [Field F] {b c : ℕ}
  [SampleableType (Fin b → F)]

abbrev Shared := CheckpointExecution.Spec unifSpec

def finish (nodes : PackedSumcheckRound.Node b ↪ F) (enabled : Bool)
    (afterQuery : Query F b c → OracleComp (Shared Cfg Input Digest) Later) :
    OracleComp (Shared Cfg Input Digest) (Option (Query F b c × Later)) :=
  if enabled then
    some <$> SharedContinuation.program
      (PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample nodes c)) afterQuery
  else pure none

def program (nodes : PackedSumcheckRound.Node b ↪ F)
    (before : OracleComp (Shared Cfg Input Digest) Earlier) (enabled : Earlier → Bool)
    (afterQuery : Earlier → Query F b c → OracleComp (Shared Cfg Input Digest) Later) :=
  SharedContinuation.program before (fun earlier => finish nodes (enabled earlier) (afterQuery earlier))

def Agreement (first second : Row → MatrixFold.Cube c → Fin b → F) : Option (Query F b c × Later) → Prop
  | none => False
  | some entry => ∀ row, entry.1.fold (first row) = entry.1.fold (second row)

def WrongAgreement (first second : Earlier → Row → MatrixFold.Cube c → Fin b → F)
    (outcome : Earlier × Option (Query F b c × Later)) : Prop :=
  (∃ row, first outcome.1 row ≠ second outcome.1 row) ∧ Agreement (first outcome.1) (second outcome.1) outcome.2

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype F] [DecidableEq F]

/-- All subsequent actual calls retain the earlier query's fixed-row bound. -/
theorem finish_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F) (enabled : Bool)
    (afterQuery : Query F b c → OracleComp (Shared Cfg Input Digest) Later)
    (first second : Row → MatrixFold.Cube c → Fin b → F) (different : ∃ row, first row ≠ second row)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (finish nodes enabled afterQuery)).run state}[Agreement first second outcome.1] ≤
      (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  cases enabled with
  | false => simp [finish, Agreement, prEvent_norm]
  | true =>
    rw [finish, ite_eq_left rfl, simulateQ_map, StateT.run_map, prEvent_map]
    have retained := SharedContinuation.earlier_event_le enc dummy shape
      (PrivateSampling.embed Cfg Input Digest (MatrixCompression.sample nodes c)) afterQuery state
      (fun query => ∀ row, query.fold (first row) = query.fold (second row))
    exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_norm] using
      MatrixCompression.family_agreement_bound nodes first second different)

/-- Average the fresh bound over arbitrary actual earlier proposer, binder and
private-memory outcomes. No source-dependent checks occur in the program. -/
theorem wrong_agreement_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F)
    (before : OracleComp (Shared Cfg Input Digest) Earlier) (enabled : Earlier → Bool)
    (afterQuery : Earlier → Query F b c → OracleComp (Shared Cfg Input Digest) Later)
    (first second : Earlier → Row → MatrixFold.Cube c → Fin b → F)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes before enabled afterQuery)).run state}[WrongAgreement first second outcome.1] ≤
      (c : ENNReal) * (((((2 * b - 1 : ℕ) : ENNReal) / Fintype.card F) ^ b)) := by
  rw [program, SharedContinuation.program, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le
  intro earlier
  by_cases different : ∃ row, first earlier.1 row ≠ second earlier.1 row
  · simpa only [simulateQ_map, StateT.run_map, prEvent_norm, WrongAgreement, different, true_and] using
      finish_bound enc dummy shape nodes (enabled earlier.1) (afterQuery earlier.1)
        (first earlier.1) (second earlier.1) different earlier.2
  · simp [simulateQ_map, StateT.run_map, WrongAgreement, different, prEvent_norm]

omit [Fintype F] [DecidableEq F] in
/-- Enabling compression is proved by the actual control flow, not supplied
as a safety or acceptance certificate by the prover. -/
theorem finish_enabled (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node b ↪ F) (enabled : Bool)
    (afterQuery : Query F b c → OracleComp (Shared Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : Option (Query F b c × Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (finish nodes enabled afterQuery)).run state)) (present : outcome.1 ≠ none) : enabled = true := by
  cases enabled with
  | false =>
    simp only [finish, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at supported
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    exact (present rfl).elim
  | true => rfl

end

end FormalProof4FHE.HasteBoots.GuardedCompression
