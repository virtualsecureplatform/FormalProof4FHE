module

public import FormalProof4FHE.HasteBoots.CachedHashHandler
public import FormalProof4FHE.HasteBoots.ExpectedHazard

@[expose] public section

/-!
# Checkpoint stability under the concrete cached hash handler

This is a one-step law for the actual handler, conditional on the whole current
state. Repeated inputs have zero loss even when their answers are targets.
Fresh inputs pay the shared deduplicated target-union bound. Whole-execution
accumulation and native phase/checkpoint placement remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree ProbabilityTheory MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.CachedHashCheckpoint

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]
  [Fintype Digest] [SampleableType Digest]

omit [Fintype Digest] in
/-- A cached hash cannot destabilize any recorded payload source. -/
theorem cached_loss_zero (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (state : CachedHashHandler.State Input Digest) (coherent : CachedHashHandler.Coherent state)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints state.log)
    (query : Input) (answer : Digest) (known : state.cache query = some answer) :
    Pr{let result ← (CachedHashHandler.handler query).run state}[
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints result.2.log] = 0 := by
  rw [CachedHashHandler.run_cached state query answer known]
  apply prEvent_eq_zero_of_forall_mem_support
  intro result supported changed
  have equal := eq_of_mem_support_pure _ supported
  subst result
  exact changed (MerklePayloadCheckpoints.stable_append_cached enc dummy shape checkpoints
    state.log stable query answer (coherent.cache_covered query answer known))

/-- A fresh step uses precisely the actual log and cache-key cover; the roots,
query and existing cache can already depend on all preceding answers. -/
theorem fresh_loss_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (state : CachedHashHandler.State Input Digest) (coherent : CachedHashHandler.Coherent state)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints state.log)
    (query : Input) (fresh : state.cache query = none) :
    Pr{let result ← (CachedHashHandler.handler query).run state}[
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints result.2.log] ≤
      ((min checkpoints.totalNodeBudget (2 * state.keys.card + checkpoints.checkpoints.length) : ℕ) : ENNReal) /
        Fintype.card Digest := by
  rw [CachedHashHandler.run_fresh state query fresh, prEvent_map]
  exact MerkleCheckpointProbability.destabilization_bound enc dummy shape checkpoints
    state.log state.cache state.keys coherent.toCover stable query

/-- One conditional hazard for the concrete handler, with cache hits free. -/
theorem step_loss_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (state : CachedHashHandler.State Input Digest) (coherent : CachedHashHandler.Coherent state)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints state.log)
    (query : Input) :
    Pr{let result ← (CachedHashHandler.handler query).run state}[
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints result.2.log] ≤
      if state.cache query = none then
        ((min checkpoints.totalNodeBudget (2 * state.keys.card + checkpoints.checkpoints.length) : ℕ) : ENNReal) /
          Fintype.card Digest
      else 0 := by
  cases known : state.cache query with
  | none =>
      simp only [reduceIte]
      exact fresh_loss_bound enc dummy shape checkpoints state coherent stable query known
  | some answer =>
      simp only [reduceCtorEq, reduceIte]
      exact le_of_eq (cached_loss_zero enc dummy shape checkpoints state coherent stable query answer known)


/-- Actual pre-answer charge: no charge for a repeated input. -/
def loss (shape : Cfg → Skeleton)
    (checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (query : Input) (state : CachedHashHandler.State Input Digest) : ENNReal :=
  if state.cache query = none then
    ((min checkpoints.totalNodeBudget (2 * state.keys.card + checkpoints.checkpoints.length) : ℕ) : ENNReal) /
      Fintype.card Digest
  else 0

/-- All fixed recorded sources survive an arbitrary adaptive hash suffix except
with probability at most its expected accumulated concrete fresh-answer charge.
This protects payload and digest stability together and has no query budget.
Native checkpoint placement, collisions, private sampling and physical-work
coupling still have to be composed into the complete protocol theorem. -/
theorem suffix_loss_bound {Result : Type}
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (checkpoints : MerklePayloadCheckpoints.State (Input := Input) (Digest := Digest) shape)
    (state : CachedHashHandler.State Input Digest) (coherent : CachedHashHandler.Coherent state)
    (stable : MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints state.log)
    (program : OracleComp (Input →ₒ Digest) Result) :
    Pr{let result ← (simulateQ CachedHashHandler.handler program).run state}[
      ¬MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints result.2.log] ≤
      ExpectedHazard.charge CachedHashHandler.handler (loss shape checkpoints) program state := by
  let good := fun current : CachedHashHandler.State Input Digest =>
    CachedHashHandler.Coherent current ∧
      MerklePayloadCheckpoints.StableAt enc dummy shape checkpoints current.log
  have step : ∀ query current, good current →
      Pr{let result ← (CachedHashHandler.handler query).run current}[¬good result.2] ≤
        loss shape checkpoints query current := by
    intro query current valid
    apply le_trans (prEvent_mono_of_support _ _ _ ?_)
      (step_loss_bound enc dummy shape checkpoints current valid.1 valid.2 query)
    intro result supported invalid
    exact fun stableAfter => invalid
      ⟨CachedHashHandler.coherent_step query current valid.1 result supported, stableAfter⟩
  exact (prEvent_mono _ _ _ (fun _ invalid valid => invalid valid.2)).trans
    (ExpectedHazard.terminal_failure_le_charge CachedHashHandler.handler (loss shape checkpoints)
      good step program state ⟨coherent, stable⟩)

end

end FormalProof4FHE.HasteBoots.CachedHashCheckpoint
