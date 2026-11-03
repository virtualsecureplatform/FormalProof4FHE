module

public import FormalProof4FHE.HasteBoots.ChargedExecution
public import FormalProof4FHE.HasteBoots.PrivateSamplingCharge

@[expose] public section

/-!
# Private queries preserve the recorded availability account

Zero private-query hazard preserves both the actual shared state and its
existing charge account. All private observations, including partial byte
traces, keep their original law. Computational byte work is not set to zero.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.PrivateChargedSampling

noncomputable section

variable {Cfg Input Digest Payload A : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

variable (implBase : QueryImpl base ProbComp)
  (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
  (loss : (CheckpointExecution.Spec base Cfg Input Digest).Domain →
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
  (private_zero : ∀ query state, loss (.inl query) state = 0)

include private_zero in
/-- One actual private answer preserves both state and pre-existing account. -/
theorem run_query (query : base.Domain)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (spent : ENNReal) :
    (ChargedExecution.handler (CheckpointExecution.handler implBase enc dummy shape) loss (.inl query)).run
      (initial, spent) = (fun answer => (answer, (initial, spent))) <$> implBase query := by
  rw [ChargedExecution.run_handler]
  change (fun outcome => (outcome.1, (outcome.2, spent + loss (.inl query) initial))) <$>
    ((fun answer => (answer, initial)) <$> implBase query) = _
  rw [Functor.map_map, private_zero, add_zero]

include private_zero in
/-- Exact query-program equality preserves every private observation and the
complete incoming state/account, rather than merely its accepted value law. -/
theorem run_embed (program : OracleComp base A)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (spent : ENNReal) :
    (simulateQ (ChargedExecution.handler (CheckpointExecution.handler implBase enc dummy shape) loss)
      (PrivateSampling.embed Cfg Input Digest program)).run (initial, spent) =
      (fun result => (result, (initial, spent))) <$> simulateQ implBase program := by
  have same : simulateQ (ChargedExecution.handler (CheckpointExecution.handler implBase enc dummy shape) loss)
      (PrivateSampling.embed Cfg Input Digest program) =
      simulateQ (implBase.liftTarget
        (StateT (CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) ProbComp)) program := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro query
    rw [simulateQ_spec_query]
    apply StateT.ext
    intro current
    rw [QueryImpl.liftTarget_apply_run]
    exact run_query implBase enc dummy shape loss private_zero query current.1 current.2
  rw [same, simulateQ_liftTarget, StateT.run_monadLift, map_eq_bind_pure_comp]
  rfl

/-- Ideal private uniform sampling also keeps the whole recorded account. -/
theorem run_probComp
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (loss : (CheckpointExecution.Spec unifSpec Cfg Input Digest).Domain →
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
    (private_zero : ∀ query state, loss (.inl query) state = 0)
    (program : ProbComp A)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (spent : ENNReal) :
    (simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
      (PrivateSampling.embed Cfg Input Digest program)).run (initial, spent) =
      (fun result => (result, (initial, spent))) <$> program := by
  rw [run_embed (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape loss private_zero, simulateQ_ofLift_eq_self]

end

end FormalProof4FHE.HasteBoots.PrivateChargedSampling
