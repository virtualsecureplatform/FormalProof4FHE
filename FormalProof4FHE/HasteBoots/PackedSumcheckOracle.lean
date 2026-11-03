module

public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
public import FormalProof4FHE.HasteBoots.PrivateSampling

@[expose] public section

/-!
# Packed-sumcheck verifier on the actual shared oracle signature

Prover messages and post-challenge callbacks are arbitrary shared-oracle
programs. The verifier checks each message before its private lane draw and
returns only an ordered matrix query and expected terminal value. It never
receives or evaluates source tables. Rejection returns `none` while retaining
the actual final cache and logs in the interpreter. Production Fiat--Shamir,
terminal authentication and Rust refinement remain separate obligations.
-/

open OracleSpec OracleComp BinaryTree
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.PackedSumcheckOracle

noncomputable section

attribute [local instance] Classical.propDecidable

variable {F Message ProverState Cfg Input Digest Payload : Type} [Field F]
  {k : ℕ} [SampleableType (Fin k → F)]

abbrev Shared (Cfg Input Digest : Type) := CheckpointExecution.Spec unifSpec Cfg Input Digest

def prependResult {n : ℕ} (pair : MatrixFold.Pair (F := F) (Lane := Fin k))
    (result : Option (Subclaim F k n × ProverState)) : Option (Subclaim F k (n + 1) × ProverState) :=
  result.map (fun entry => (entry.1.prepend pair, entry.2))

/-- The operational verifier contains no ghost/source-table parameter. -/
def program (nodes : PackedSumcheckRound.Node k ↪ F) (interpret : Message → Polynomial F)
    (send : ℕ → ProverState → (Fin k → F) → OracleComp (Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (Shared Cfg Input Digest) ProverState) :
    (n : ℕ) → (Fin k → F) → ProverState → OracleComp (Shared Cfg Input Digest) (Option (Subclaim F k n × ProverState))
  | 0, claimed, state => pure (some (⟨.nil, claimed⟩, state))
  | n + 1, claimed, state => by
    classical
    exact do
      let packet ← send (n + 1) state claimed
      if PackedSumcheckProbability.Checks nodes claimed (interpret packet.1) then
        let challenge ← PrivateSampling.embed Cfg Input Digest ($ᵗ (Fin k → F))
        let nextState ← afterChallenge packet.2 challenge
        let result ← program nodes interpret send afterChallenge n
          (fun lane => (interpret packet.1).eval (challenge lane)) nextState
        pure (prependResult (PackedSumcheckRound.challengePair nodes challenge) result)
      else pure none

def TruthfulResult {Factor Term : Type} [Fintype Term] (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    {n : ℕ} (tables : PackedSumcheckExecution.Tables F Factor n k) :
    Option (Subclaim F k n × ProverState) → Prop
  | none => False
  | some entry => entry.1.Truthful arity coefficient indices tables

omit [SampleableType (Fin k → F)] in
theorem truthful_prepend_iff {Factor Term : Type} [Fintype Term]
    (arity : Term → ℕ) (coefficient : Term → F)
    (indices : (term : Term) → Fin (arity term) → Factor)
    {n : ℕ} (tables : PackedSumcheckExecution.Tables F Factor (n + 1) k)
    (pair : MatrixFold.Pair (F := F) (Lane := Fin k)) (result : Option (Subclaim F k n × ProverState)) :
    TruthfulResult arity coefficient indices tables (prependResult pair result) ↔
      TruthfulResult arity coefficient indices (fun factor => MatrixFold.foldFirst pair (tables factor)) result := by
  cases result with
  | none => rfl
  | some entry => exact Subclaim.truthful_prepend_iff arity coefficient indices tables pair entry.1

section Runtime

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Exact interpreted one-round law: every message/callback call uses the
same state, private coins preserve it, and rejected calls remain in the state. -/
theorem run_succ (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (nodes : PackedSumcheckRound.Node k ↪ F) (interpret : Message → Polynomial F)
    (send : ℕ → ProverState → (Fin k → F) → OracleComp (Shared Cfg Input Digest) (Message × ProverState))
    (afterChallenge : ProverState → (Fin k → F) → OracleComp (Shared Cfg Input Digest) ProverState)
    (n : ℕ) (claimed : Fin k → F) (privateState : ProverState)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program nodes interpret send afterChallenge (n + 1) claimed privateState)).run state =
    (do
      let packet ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (send (n + 1) privateState claimed)).run state
      if PackedSumcheckProbability.Checks nodes claimed (interpret packet.1.1) then
        let challenge ← $ᵗ (Fin k → F)
        let nextState ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (afterChallenge packet.1.2 challenge)).run packet.2
        let result ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (program nodes interpret send afterChallenge n
            (fun lane => (interpret packet.1.1).eval (challenge lane)) nextState.1)).run nextState.2
        pure (prependResult (PackedSumcheckRound.challengePair nodes challenge) result.1, result.2)
      else pure (none, packet.2)) := by
  classical
  rw [program, simulateQ_bind, StateT.run_bind]
  congr 1
  funext packet
  by_cases checked : PackedSumcheckProbability.Checks nodes claimed (interpret packet.1.1)
  · simp only [checked, reduceIte, simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp,
      bind_map_left, simulateQ_pure, StateT.run_pure]
  · simp only [checked, ite_false, simulateQ_pure, StateT.run_pure]

end Runtime

end

end FormalProof4FHE.HasteBoots.PackedSumcheckOracle
