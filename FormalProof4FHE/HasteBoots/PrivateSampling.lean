module

public import FormalProof4FHE.HasteBoots.CheckpointExecution
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose

@[expose] public section

/-!
# Private computations inside the shared checkpoint handler

Routing private queries through the left summand leaves every hash/checkpoint
state component unchanged. With the forwarding uniform handler, any ProbComp
computation keeps exactly its original law. This supplies the operational
private-sampling bridge; production transcript-derived coins are not asserted
fresh by this lemma.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.PrivateSampling

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]
  {ι : Type} {base : OracleSpec ι}

/-- Explicit routing avoids confusing private uniform draws with cached hashes. -/
def embed (Cfg Input Digest : Type) {Result : Type} (program : OracleComp base Result) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result :=
  simulateQ (fun query => liftM ((CheckpointExecution.Spec base Cfg Input Digest).query (.inl query))) program

section Runtime

variable [SampleableType Digest]

/-- The full private subprogram is exactly its original interpretation with
one unchanged shared state carried alongside it. -/
theorem run_embed {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp base Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler implBase enc dummy shape)
      (embed Cfg Input Digest program)).run state =
      (fun result => (result, state)) <$> simulateQ implBase program := by
  have same : simulateQ (CheckpointExecution.handler implBase enc dummy shape) (embed Cfg Input Digest program) =
      simulateQ (implBase.liftTarget (StateT (CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ProbComp))
        program := by
    apply QueryImpl.simulateQ_simulateQ_eq_of_apply
    intro query
    rw [simulateQ_spec_query]
    apply StateT.ext
    intro current
    rw [QueryImpl.liftTarget_apply_run]
    rfl
  rw [same, simulateQ_liftTarget, StateT.run_monadLift, map_eq_bind_pure_comp]
  rfl

/-- Private uniform primitives have their original joint law and preserve the
entire cache, ordered log, key set, checkpoints and failure monitor. -/
theorem run_probComp {Result : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : ProbComp Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (embed Cfg Input Digest program)).run state = (fun result => (result, state)) <$> program := by
  rw [run_embed, simulateQ_ofLift_eq_self]

end Runtime

end

end FormalProof4FHE.HasteBoots.PrivateSampling
