module

public import FormalProof4FHE.HasteBoots.ExpectedChargeComposition
public import FormalProof4FHE.HasteBoots.PrivateSampling
public import FormalProof4FHE.HasteBoots.CheckpointCollision

@[expose] public section

/-!
# Private sampling and the actual availability charge

Private byte draws have zero availability hazard. This does not assign them
zero computational work. The exact sequential composition theorem retains
all later state-dependent helper/native charges, averaged over the complete
actual private sampling observation.
-/

open OracleSpec OracleComp BinaryTree MeasureTheory

namespace FormalProof4FHE.HasteBoots.PrivateSamplingCharge

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι} {A B : Type}

/-- Zero private-query losses give zero availability charge for the whole
embedded private computation, including every rejected or partial draw. -/
theorem zero (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (loss : (CheckpointExecution.Spec base Cfg Input Digest).Domain →
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
    (private_zero : ∀ query state, loss (.inl query) state = 0)
    (program : OracleComp base A)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape) loss
      (PrivateSampling.embed Cfg Input Digest program) initial = 0 := by
  unfold PrivateSampling.embed
  induction program using OracleComp.inductionOn generalizing initial with
  | pure result => simp only [simulateQ_pure, ExpectedHazard.charge_pure]
  | query_bind query tail ih =>
    rw [simulateQ_bind, simulateQ_spec_query, ExpectedHazard.charge_query_bind, private_zero]
    simp only [ih, OracleComp.evalDist_map_const, lintegral_dirac, zero_add]

/-- In particular the source-availability/collision loss used by the native
security bound assigns zero hazard to ideal private draws. -/
theorem availability_zero [Fintype Digest] (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp base A)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape) (CheckpointCollision.loss base shape)
      (PrivateSampling.embed Cfg Input Digest program) initial = 0 := by
  apply zero
  intro query state
  simp [CheckpointCollision.loss, CheckpointExecution.loss, CheckpointCollision.collisionLoss]

/-- The shared state is unchanged by private sampling, and the later charge
uses the exact sampled observation. Suspended/rejected observations are not
discarded or replaced by a value marginal. -/
theorem then_shared (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (loss : (CheckpointExecution.Spec base Cfg Input Digest).Domain →
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
    (private_zero : ∀ query state, loss (.inl query) state = 0)
    (program : OracleComp base A)
    (next : A → OracleComp (CheckpointExecution.Spec base Cfg Input Digest) B)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape) loss
      (PrivateSampling.embed Cfg Input Digest program >>= next) initial =
      ∫⁻ value, value ∂𝒟[(fun observed => ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy shape) loss (next observed) initial) <$>
          simulateQ implBase program] := by
  rw [ExpectedChargeComposition.bind, zero implBase enc dummy shape loss private_zero,
    zero_add, PrivateSampling.run_embed, Functor.map_map]

end

end FormalProof4FHE.HasteBoots.PrivateSamplingCharge
