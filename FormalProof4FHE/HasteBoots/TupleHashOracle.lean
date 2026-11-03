module

public import FormalProof4FHE.HasteBoots.TupleHash
public import FormalProof4FHE.HasteBoots.SharedContinuation
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# Tuple-hash misses through shared-oracle work

Fixed sources and a public table precede the fresh scalar hash challenge.
Arbitrary preparation and later adaptive shared work retain the collision
bound and all issued calls. This does not assert freshness for transcript-
derived coins or replace the reciprocal/algebraic/authentication components.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.TupleHashOracle

noncomputable section

variable {F K Position Memory Later Cfg Input Digest Payload : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {width : ℕ}

def program (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (next : Memory → K → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (K × Later) := do
  let memory ← before
  SharedContinuation.program (PrivateSampling.embed Cfg Input Digest ($ᵗ K)) (next memory)

theorem retained_miss_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sources : Position → Fin width → F) (table : List (Fin width → F)) (bad : ∃ position, sources position ∉ table)
    (next : K → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program (PrivateSampling.embed Cfg Input Digest ($ᵗ K)) next)).run state}[
        ∀ position, ∃ entry ∈ table, TupleHash.hash outcome.1.1 (sources position) = TupleHash.hash outcome.1.1 entry] ≤
      (table.length : ENNReal) * ((width - 1 : ℕ) / (Fintype.card K : ENNReal)) := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest ($ᵗ K)) next state
    (fun y => ∀ position, ∃ entry ∈ table, TupleHash.hash y (sources position) = TupleHash.hash y entry)
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_norm] using
    TupleHash.list_family_miss_bound (K := K) sources table bad)

theorem prepared_miss_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sources : Position → Fin width → F) (table : List (Fin width → F)) (bad : ∃ position, sources position ∉ table)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (next : Memory → K → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program before next)).run state}[
        ∀ position, ∃ entry ∈ table, TupleHash.hash outcome.1.1 (sources position) = TupleHash.hash outcome.1.1 entry] ≤
      (table.length : ENNReal) * ((width - 1 : ℕ) / (Fintype.card K : ENNReal)) := by
  rw [program, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le
  intro prepared
  exact retained_miss_bound enc dummy shape sources table bad (next prepared.1) prepared.2

end

end FormalProof4FHE.HasteBoots.TupleHashOracle
