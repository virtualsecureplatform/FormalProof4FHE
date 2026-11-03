module

public import FormalProof4FHE.HasteBoots.TupleLookupPair
public import FormalProof4FHE.HasteBoots.SharedContinuation
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# Independent lookup pairs retained through the shared execution

All ideal challenge pairs precede arbitrary later shared work, including
adaptive helper commitments, checks, openings or rejection. Preparation and
later calls remain on the same handler/state. The event here is the semantic
all-pairs reciprocal condition; actual lookup acceptance must still imply it
outside the sumcheck/ZeroCheck/PCS and hash-availability errors. Native
rejection-loop, transcript and work refinement remain open.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.TupleLookupPairOracle

noncomputable section

variable {F K Memory Later Cfg Input Digest Payload : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K] [Fintype K] [SampleableType K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] {width count size : ℕ}

def program (table : Fin size → Fin width → F) (repetitions : ℕ)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (next : Memory → Option (List (K × K)) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (List (K × K)) × Later) := do
  let memory ← before
  SharedContinuation.program
    (PrivateSampling.embed Cfg Input Digest (TupleLookupPair.repeats (K := K) table repetitions).run) (next memory)

variable {p : ℕ} [CharP K p]

theorem retained_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) (repetitions : ℕ)
    (next : Option (List (K × K)) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (SharedContinuation.program
        (PrivateSampling.embed Cfg Input Digest (TupleLookupPair.repeats (K := K) table repetitions).run) next)).run state}[
          outcome.1.1.elim False (TupleLookupPair.AllPass sources table multiplicities)] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  have retained := SharedContinuation.earlier_event_le enc dummy shape
    (PrivateSampling.embed Cfg Input Digest (TupleLookupPair.repeats (K := K) table repetitions).run) next state
    (fun result => result.elim False (TupleLookupPair.AllPass sources table multiplicities))
  have arithmetic := TupleLookupPair.repeated_bound sources table multiplicities bad small repetitions
  rw [OptionT.prEvent_eq_run] at arithmetic
  exact retained.trans (by simpa only [PrivateSampling.run_probComp, prEvent_norm] using arithmetic)

theorem prepared_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sources : Fin count → Fin width → F) (table : Fin size → Fin width → F) (multiplicities : Fin size → K)
    (bad : ∃ i, ∀ j, sources i ≠ table j) (small : count < p) (repetitions : ℕ)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Memory)
    (next : Memory → Option (List (K × K)) → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program table repetitions before next)).run state}[
          outcome.1.1.elim False (TupleLookupPair.AllPass sources table multiplicities)] ≤
      TupleLookupPair.error (Fintype.card K) width count size ^ repetitions := by
  rw [program, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le
  intro prepared
  exact retained_bound enc dummy shape sources table multiplicities bad small repetitions (next prepared.1) prepared.2

end

end FormalProof4FHE.HasteBoots.TupleLookupPairOracle
