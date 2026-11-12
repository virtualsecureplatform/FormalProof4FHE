module

public import FormalProof4FHE.HasteBoots.DependentShortCircuitSequence
public import FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix

@[expose] public section

/-! Original-root single openings with independent physical PCS layouts.
Each native single worker receives its source's own code/domain/root geometry.
No batch-mixing challenge is introduced. -/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.HeterogeneousSingleOpening

noncomputable section

structure Layout where
  front : ℕ
  suffix : ℕ
  m : ℕ
  queries : ℕ

variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b : ℕ}

abbrev Protocol (F Input Digest Cfg Response Memory : Type) (b : ℕ)
    (heights : Cfg → ℕ) (tag : Factor → Cfg) (layout : Factor → Layout) (factor : Factor) [Field F] :=
  NativeMatrixVerifier.Protocol F Unit Input Digest Cfg Response Memory (2^(layout factor).front) b
    (layout factor).m (2^(layout factor).suffix) (layout factor).queries (heights (tag factor))

abbrev Data (F Digest Response : Type) (b : ℕ)
    (heights : Cfg → ℕ) (tag : Factor → Cfg) (layout : Factor → Layout) (factor : Factor) :=
  JointMatrixOpening.Data F Digest Response (2 ^ (layout factor).front) b (heights (tag factor)) (layout factor).queries

def requests (tag : Factor → Cfg) (indices : List Factor)
    (emission : (Factor → Digest) × CommitMemory) : List (Cfg × Digest) :=
  indices.map (fun factor => (tag factor, emission.1 factor))

def snapshots (heights : Cfg → ℕ) (tag : Factor → Cfg)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (factor : Factor) : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) (tag factor) :=
  ⟨first.1.1 factor, first.2.hash.log⟩

omit [DecidableEq Input] [DecidableEq Digest] in
theorem snapshots_recorded (heights : Cfg → ℕ) (tag : Factor → Cfg) (indices : List Factor)
    (complete : ∀ factor, factor ∈ indices)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) (factor : Factor) :
    ⟨tag factor, snapshots heights tag first factor⟩ ∈
      (RecordRoots.state (fun cfg => Skeleton.perfect (heights cfg)) (requests tag indices first.1)
        first.2).checkpoints.checkpoints :=
  RecordRoots.recorded _ _ first.2 (tag factor, first.1.1 factor) (List.mem_map_of_mem (complete factor))

def protocol (enc : MerkleOracle.Encoding Input Digest (List F)) (heights : Cfg → ℕ) (tag : Factor → Cfg)
    (layout : Factor → Layout) (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (emission : (Factor → Digest) × CommitMemory) (query : QueryData) (factor : Factor) :
    Protocol F Input Digest Cfg Response Memory b heights tag layout factor :=
  { build emission query factor with encoding := enc, domain := domain factor, root := fun _ => emission.1 factor }

variable {heights : Cfg → ℕ} {tag : Factor → Cfg} {layout : Factor → Layout}
  [∀ factor, SampleableType (TestMatrix F (2 ^ (layout factor).front) b)]
  [∀ factor, SampleableType (Fin (layout factor).queries → Fin (2 ^ heights (tag factor)))]

def continuation (enc : MerkleOracle.Encoding Input Digest (List F))
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (factors : List Factor) (emission : (Factor → Digest) × CommitMemory) :=
  SharedContinuation.program (selectQuery emission) (fun query => if enabled emission query then
    DependentShortCircuitSequence.program
      (fun factor => NativeMatrixVerifier.step (protocol enc heights tag layout domain build emission query factor) ())
      factors (start emission query)
    else pure ⟨[], start emission query, false⟩)

/-- The proof snapshot erases to the exact real program, including rejected
and disabled branches and every actual hash call. -/
theorem project_witness [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory) (factors : List Factor) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$>
      MultiCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg)) (requests tag factors) commit
        (continuation enc domain build selectQuery enabled start factors)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (fun cfg => Skeleton.perfect (heights cfg)))
        (MultiCommitmentPrefix.program (requests tag factors) commit
          (continuation enc domain build selectQuery enabled start factors))).run
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) :=
  MultiCommitmentPrefix.project_witness enc dummy _ _ _ _ _


end
end FormalProof4FHE.HasteBoots.HeterogeneousSingleOpening
