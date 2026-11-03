module

public import FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening

@[expose] public section

/-!
# Native heterogeneous batches against already-recorded original checkpoints

The checkpoints need not share one recording time. The staged-prefix adapter
establishes membership and root identity from actual execution; these are
bookkeeping premises, not replay, safety or PCS security certificates.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.HeterogeneousBatchOpening

namespace FormalProof4FHE.HasteBoots.RecordedHeterogeneousBatchOpening

noncomputable section

variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest] {b : ℕ}
  {heights : Cfg → ℕ} {tag : Factor → Cfg} {layout : Factor → Layout}

abbrev Snapshots (Input Digest : Type) (heights : Cfg → ℕ) (tag : Factor → Cfg) :=
  ∀ factor, Checkpoint Input Digest
    (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) (tag factor)

def Arithmetic (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * b) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (emission : (Factor → Digest) × CommitMemory) (checkpoint : Snapshots Input Digest heights tag)
    (query : QueryData) (entry : Sigma (Data F Digest Response b heights tag layout)) : Prop :=
  let p := protocol enc heights tag layout domain build emission query entry.1
  BatchMatrixSampling.ArithmeticBad (domain entry.1) (capacity entry.1) (radius entry.1)
    (word enc dummy heights (tag entry.1) (checkpoint entry.1))
    (NativeBatchChecks.left (front := (layout entry.1).front) (suffix := (layout entry.1).suffix) p.query)
    (NativeBatchChecks.right (front := (layout entry.1).front) (suffix := (layout entry.1).suffix) p.query)
    p.values p.testResponse (NativeBatchChecks.structured p.query p.groupResponse) entry.2.1

def Wrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * b) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (emission : (Factor → Digest) × CommitMemory) (checkpoint : Snapshots Input Digest heights tag)
    (last : (QueryData × ShortCircuitSequence.Outcome Factor
      (Sigma (Data F Digest Response b heights tag layout)) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) : Prop :=
  last.1.2.accepted = true ∧ ∃ factor claim,
    (protocol enc heights tag layout domain build emission last.1.1 factor).values claim ≠
      matrixEvaluation
        (NativeBatchChecks.left (front := (layout factor).front) (suffix := (layout factor).suffix)
          (protocol enc heights tag layout domain build emission last.1.1 factor).query claim)
        (NativeBatchChecks.right (front := (layout factor).front) (suffix := (layout factor).suffix)
          (protocol enc heights tag layout domain build emission last.1.1 factor).query claim)
        (MatrixOpeningSecurity.extract (domain factor) (capacity factor) (radius factor)
          (word enc dummy heights (tag factor) (checkpoint factor)))

variable [SampleableType Digest]
  [∀ factor, SampleableType (TestMatrix F (2 ^ (layout factor).front) b)]
  [∀ factor, SampleableType (Fin (layout factor).queries → Fin (2 ^ heights (tag factor)))]

/-- Successful wrong values reduce to actual root arithmetic or one global
availability event, measured against the supplied immutable original snapshots. -/
theorem reduce_wrong
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * b) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (emission : (Factor → Digest) × CommitMemory) (checkpoint : Snapshots Input Digest heights tag)
    (rootEq : ∀ factor, (checkpoint factor).root = emission.1 factor)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (recorded : ∀ factor, ⟨tag factor, checkpoint factor⟩ ∈ before.checkpoints.checkpoints)
    (last : (QueryData × ShortCircuitSequence.Outcome Factor
      (Sigma (Data F Digest Response b heights tag layout)) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : last ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (continuation enc domain build selectQuery enabled start factors emission)).run before))
    (wrong : Wrong enc dummy domain capacity radius build emission checkpoint last) :
    SharedSequence.AnyBad (fun _ => Arithmetic enc dummy domain capacity radius build emission checkpoint last.1.1) last.1.2.results ∨
      CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) last.2 := by
  let p := protocol enc heights tag layout domain build
  obtain ⟨passed, factor, claim, different⟩ := wrong
  have finalRecorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (fun cfg => Skeleton.perfect (heights cfg)) (tag factor) (checkpoint factor)
    (continuation enc domain build selectQuery enabled start factors emission) before (recorded factor) last supported
  obtain ⟨selected, _, opened, openedSupported, equal⟩ :=
    (SharedContinuation.support_program enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (selectQuery emission) (fun query => if enabled emission query then
        DependentShortCircuitSequence.program (fun factor => NativeBatchVerifier.step (p emission query factor))
          factors (start emission query)
        else pure ⟨[], start emission query, false⟩) before last).mp supported
  subst last
  cases gate : enabled emission selected.1 with
  | false =>
    simp only [gate, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at openedSupported
    have equal := eq_of_mem_support_pure _ openedSupported
    subst opened
    exact (Bool.false_ne_true passed).elim
  | true =>
    simp only [gate, reduceIte] at openedSupported
    have verified := DependentShortCircuitSequence.accepted_cache_results enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (fun factor => NativeBatchVerifier.step (p emission selected.1 factor)) factors
      (fun factor data cache => NativeBatchVerifier.checks (p emission selected.1 factor) data = true ∧
        ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc heights
          (AuthenticatedColumnChecks.request heights (tag factor) (emission.1 factor) column) cache)
      (by
        intro factor _ memory state outcome present accepted later extension
        have native := NativeBatchVerifier.step_accepts_later (p emission selected.1 factor) dummy
          (fun cfg => Skeleton.perfect (heights cfg)) (tag factor) memory state outcome present accepted later extension
        simpa only [p, protocol, ParallelColumnAvailability.Replays, AuthenticatedColumnChecks.request] using native)
      (start emission selected.1) selected.2 opened openedSupported passed
    have allFactors := ShortCircuitSequence.accepted_indices enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (DependentShortCircuitSequence.step (fun factor => NativeBatchVerifier.step (p emission selected.1 factor))) factors
      (start emission selected.1) selected.2 opened openedSupported passed
    have occurs : factor ∈ opened.1.results.map Prod.fst := by rw [allFactors]; exact complete factor
    obtain ⟨entry, member, same⟩ := List.mem_map.mp occurs
    subst factor
    obtain ⟨data, dataEq, checked, replayed⟩ := verified entry member
    obtain arithmeticBad | unavailable := VariableHeightBatchVerifier.checks_wrong_implies_arithmetic_or_disagreement enc dummy
      heights (tag entry.1) (checkpoint entry.1) (domain entry.1) (p emission selected.1 entry.1).query
      (p emission selected.1 entry.1).values (capacity entry.1) (radius entry.1) (p emission selected.1 entry.1).testResponse
      (p emission selected.1 entry.1).groupResponse data opened.2 finalRecorded
      (by simpa only [rootEq] using replayed) checked ⟨claim, different⟩
    · refine Or.inl ⟨entry, member, ?_⟩
      rw [dataEq]
      exact arithmeticBad
    · exact Or.inr unavailable

variable [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [∀ factor, SampleableType ((Fin (2 ^ (layout factor).front) × Fin b) → K)]

/-- Fixed original checkpoints may have arbitrary earlier recording times.
No authentication premise is needed for this uniform native arithmetic bound. -/
theorem arithmetic_bound [NeZero b] [∀ factor, NeZero (layout factor).m]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (factors : List Factor)
    (domain : ∀ factor, Fin (2 ^ heights (tag factor)) ↪ F)
    (enough : ∀ factor, (layout factor).m ≤ Fintype.card (Fin (2 ^ heights (tag factor))))
    (capacity : ∀ factor, 2 ^ (layout factor).suffix ≤ (layout factor).m * b) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (emission : (Factor → Digest) × CommitMemory) (checkpoint : Snapshots Input Digest heights tag)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (domain factor)) (layout factor).m :
        Set (Fin (2 ^ heights (tag factor)) → K)) : ℚ≥0) / 3) :
    Pr{let last ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (continuation enc domain build selectQuery enabled start factors emission)).run before}[
        SharedSequence.AnyBad (fun _ => Arithmetic enc dummy domain capacity radius build emission checkpoint last.1.1) last.1.2.results] ≤
      (factors.map (fun factor => JointMatrixOpening.error (K := K) (m := (layout factor).m) (b := b)
        (queries := (layout factor).queries) (domain factor) (radius factor))).sum := by
  let p := protocol enc heights tag layout domain build
  apply SharedContinuation.later_event_le enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (selectQuery emission) (fun query => if enabled emission query then
      DependentShortCircuitSequence.program (fun factor => NativeBatchVerifier.step (p emission query factor)) factors (start emission query)
      else pure ⟨[], start emission query, false⟩) before
    (fun query outcome => SharedSequence.AnyBad (fun _ => Arithmetic enc dummy domain capacity radius build emission checkpoint query) outcome.1.results)
  intro query initial
  cases gate : enabled emission query with
  | false => simp [SharedSequence.AnyBad, prEvent_norm]
  | true =>
    simp only [reduceIte]
    apply ShortCircuitSequence.arithmetic_union_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (DependentShortCircuitSequence.step (fun factor => NativeBatchVerifier.step (p emission query factor)))
      (fun _ => Arithmetic enc dummy domain capacity radius build emission checkpoint query)
      (fun factor => JointMatrixOpening.error (K := K) (m := (layout factor).m) (b := b)
        (queries := (layout factor).queries) (domain factor) (radius factor)) factors _ (start emission query) initial
    intro factor _ memory state
    simp only [DependentShortCircuitSequence.step, simulateQ_map, StateT.run_map, prEvent_map]
    exact NativeBatchVerifier.arithmetic_bound (p emission query factor) basis dummy
      (fun cfg => Skeleton.perfect (heights cfg)) (enough factor) (capacity factor) (radius factor)
      (word enc dummy heights (tag factor) (checkpoint factor)) memory state (small factor)

end

end FormalProof4FHE.HasteBoots.RecordedHeterogeneousBatchOpening
