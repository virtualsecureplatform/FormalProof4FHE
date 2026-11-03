module

public import FormalProof4FHE.HasteBoots.ShortCircuitSequence

@[expose] public section

/-!
# Root-indexed results in the actual short-circuit loop

Only the result type is packed. The trusted step index supplies the sigma tag;
prover output cannot choose it. Mapping the result adds no oracle calls and
retains rejection, returned memory and the actual shared state.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.DependentShortCircuitSequence

noncomputable section

variable {Index Memory Cfg Input Digest Payload : Type} {Result : Index → Type}

def pack (index : Index) (result : ShortCircuitSequence.StepResult (Result index) Memory) :
    ShortCircuitSequence.StepResult (Sigma Result) Memory :=
  ⟨⟨index, result.result⟩, result.memory, result.accepted⟩

def step (run : (index : Index) → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult (Result index) Memory))
    (index : Index) (memory : Memory) := pack index <$> run index memory

def program (run : (index : Index) → Memory →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult (Result index) Memory))
    (indices : List Index) (memory : Memory) :=
  ShortCircuitSequence.program (step run) indices memory

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Packing is passive: the native result, memory, flag and shared state are
exactly those returned by the root's real verifier. -/
theorem support_step (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : (index : Index) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult (Result index) Memory))
    (index : Index) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult (Sigma Result) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (step run index memory)).run before)) :
    ∃ native ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (run index memory)).run before),
      outcome = (pack index native.1, native.2) := by
  rw [step, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨native, present, equal⟩ := supported
  exact ⟨native, present, equal.symm⟩

/-- Every result in a successful loop carries its scheduled root index and
that root's native acceptance consequence, valid in the final shared cache. -/
theorem accepted_cache_results (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (run : (index : Index) → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (ShortCircuitSequence.StepResult (Result index) Memory))
    (indices : List Index) (checked : (index : Index) → Result index → (Input →ₒ Digest).QueryCache → Prop)
    (localCheck : ∀ index ∈ indices, ∀ memory initial result,
      result ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
        enc dummy shape) (run index memory)).run initial) → result.1.accepted = true →
      ∀ later : (Input →ₒ Digest).QueryCache, result.2.hash.cache ≤ later → checked index result.1.result later)
    (memory : Memory) (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.Outcome Index (Sigma Result) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program run indices memory)).run before))
    (accepted : outcome.1.accepted = true) :
    ∀ entry ∈ outcome.1.results, ∃ data : Result entry.1,
      entry.2 = ⟨entry.1, data⟩ ∧ checked entry.1 data outcome.2.hash.cache := by
  apply ShortCircuitSequence.accepted_cache_results enc dummy shape (step run) indices
    (fun index packed cache => ∃ data : Result index, packed = ⟨index, data⟩ ∧ checked index data cache) _
    memory before outcome supported accepted
  intro index member incoming initial result present passed later extension
  obtain ⟨native, nativeSupported, equal⟩ := support_step enc dummy shape run index incoming initial result present
  subst result
  exact ⟨native.1.result, rfl, localCheck index member incoming initial native nativeSupported passed later extension⟩

end

end FormalProof4FHE.HasteBoots.DependentShortCircuitSequence
