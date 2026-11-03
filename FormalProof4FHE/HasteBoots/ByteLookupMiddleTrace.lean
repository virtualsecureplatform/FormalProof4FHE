module

public import FormalProof4FHE.HasteBoots.ByteLookupTraceOrder
public import FormalProof4FHE.HasteBoots.ByteLookupPairMiddle

@[expose] public section

/-!
# Completed byte observations through actual helper work

The entire interpreted helper outcome, including its final shared state,
increases with the three operational depths. The helper may inspect every
rejected byte. Completion has exactly the original sampler's probability;
no independence between its trace and later helper work is assumed.
-/

open OracleSpec OracleComp BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.ByteLookupMiddleTrace

noncomputable section

variable {F K Cfg Input Digest Payload HelperMemory : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {p degree width size repetitions : ℕ} [Module (ZMod p) K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

def complete {shape : Cfg → Skeleton}
    (outcome : ByteLookupPairMiddle.Emission p degree K Digest HelperMemory repetitions ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop :=
  outcome.1.1.values ≠ none

/-- Increasing every byte/retry depth preserves all completed helper records
and the actual cache/log, including trace-dependent helper behavior. -/
theorem grows (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (build : ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    {hashDepth inner outer hashDepth' inner' outer' : ℕ}
    (hh : hashDepth ≤ hashDepth') (hi : inner ≤ inner') (ho : outer ≤ outer') :
    CompletedObservation.LE
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (ByteLookupPairMiddle.program basis table hashDepth inner outer repetitions build)).run initial)
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (ByteLookupPairMiddle.program basis table hashDepth' inner' outer' repetitions build)).run initial) complete := by
  simp only [ByteLookupPairMiddle.program, SharedContinuation.program, simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, bind_map_left, simulateQ_pure, StateT.run_pure]
  apply CompletedObservation.bind (ByteLookupTraceOrder.typed basis table repetitions hh hi ho)
  · intro observed _
    exact CompletedObservation.refl _ _
  · intro observed suspended
    simp [prEvent_norm, complete, suspended]

/-- Helper work cannot change the completion mass of the retained sample,
even when it makes adaptive queries depending on the entire raw trace. -/
theorem completion (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (build : ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (hashDepth inner outer : ℕ) :
    Pr{let outcome ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (ByteLookupPairMiddle.program basis table hashDepth inner outer repetitions build)).run initial)}[complete outcome] =
      Pr{let observed ← ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions}[observed.values ≠ none] := by
  simp only [ByteLookupPairMiddle.program, SharedContinuation.program, simulateQ_bind, StateT.run_bind,
    PrivateSampling.run_probComp, bind_map_left, simulateQ_pure, StateT.run_pure]
  rw [prEvent_bind_eq_tsum, prEvent_eq_tsum_ite]
  apply tsum_congr
  intro observed
  by_cases done : observed.values ≠ none <;>
    simp [complete, done, prEvent_norm]

end

end FormalProof4FHE.HasteBoots.ByteLookupMiddleTrace
