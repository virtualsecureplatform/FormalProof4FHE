module

public import FormalProof4FHE.HasteBoots.PrivateSampling
public import FormalProof4FHE.HasteBoots.AdaptiveResponse

@[expose] public section

/-!
# Challenge, shared-oracle response and later private sampling

This is an actual program over the shared private/hash/checkpoint signature.
Its interpretation is exactly the kernel experiment retaining the response's
full resulting state. Arbitrary later programs cannot inflate an event already
determined by the challenge, response and column draw. Their own queries still
run through the same handler and remain in the complete program's work charge.
This supplies private ideal coins, not a production Fiat--Shamir freshness law.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.InteractiveSampling

noncomputable section

variable {Cfg Input Digest Payload Challenge Response Draw Result State : Type}
  [DecidableEq Input] [DecidableEq Digest]

/-- Fresh private challenge, arbitrary shared-oracle response, fresh later draw. -/
def program (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (draws : ProbComp Draw) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) ((Challenge × Response) × Draw) := do
  let challenge ← PrivateSampling.embed Cfg Input Digest coins
  let response ← respond challenge
  let draw ← PrivateSampling.embed Cfg Input Digest draws
  pure ((challenge, response), draw)

/-- The kernel form keeps the state returned by the response computation. -/
def experiment (coins : ProbComp Challenge) (respond : Challenge → ProbComp (Response × State))
    (draws : ProbComp Draw) : ProbComp ((Challenge × (Response × State)) × Draw) := do
  let pair ← AdaptiveResponse.choose coins respond
  let draw ← draws
  pure (pair, draw)

def restore (outcome : (Challenge × (Response × State)) × Draw) : ((Challenge × Response) × Draw) × State :=
  (((outcome.1.1, outcome.1.2.1), outcome.2), outcome.1.2.2)

def retain (outcome : ((Challenge × Response) × Draw) × State) : (Challenge × (Response × State)) × Draw :=
  ((outcome.1.1.1, (outcome.1.1.2, outcome.2)), outcome.1.2)

section Runtime

variable [SampleableType Digest]

/-- Exact same-state interpretation of the actual interactive prefix. -/
theorem run_program (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (draws : ProbComp Draw)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program coins respond draws)).run state =
      restore <$> experiment coins
        (fun challenge => (simulateQ
          (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
            (respond challenge)).run state) draws := by
  simp only [program, experiment, AdaptiveResponse.choose, simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, bind_map_left, bind_assoc]
  rfl

/-- Reassociating the complete output recovers the response-kernel law,
including its actual cache, logs, checkpoints and monitor at the response boundary. -/
theorem retain_run_program (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (draws : ProbComp Draw)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    retain <$> (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program coins respond draws)).run state =
      experiment coins
        (fun challenge => (simulateQ
          (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
            (respond challenge)).run state) draws := by
  rw [run_program, Functor.map_map]
  exact id_map _

/-- Include every later action while retaining the earlier sampling outcome. -/
def complete (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (draws : ProbComp Draw)
    (next : ((Challenge × Response) × Draw) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Result) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (((Challenge × Response) × Draw) × Result) := do
  let earlier ← program coins respond draws
  let result ← next earlier
  pure (earlier, result)

/-- Later adaptive hash/column work cannot inflate an earlier event. No
independence or losslessness premise about that continuation is required. -/
theorem earlier_event_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (coins : ProbComp Challenge)
    (respond : Challenge → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Response)
    (draws : ProbComp Draw)
    (next : ((Challenge × Response) × Draw) →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (bad : (Challenge × Response) × Draw → Prop) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (complete coins respond draws next)).run state}[bad outcome.1.1] ≤
      Pr{let earlier ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (program coins respond draws)).run state}[bad earlier.1] := by
  have bound := AdaptiveResponse.event_le
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program coins respond draws)).run state)
    (fun earlier => (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next earlier.1)).run earlier.2)
    (fun earlier => bad earlier.1)
  simpa only [complete, AdaptiveResponse.choose, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, simulateQ_map, StateT.run_map, prEvent_norm] using bound

end Runtime

end

end FormalProof4FHE.HasteBoots.InteractiveSampling
