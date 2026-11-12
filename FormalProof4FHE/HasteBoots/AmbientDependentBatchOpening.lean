module
public import FormalProof4FHE.HasteBoots.AmbientCommittedBatchSafeBound
public import FormalProof4FHE.HasteBoots.AmbientBatchChecks
public import FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound
@[expose] public section

/-! Native source batches can have different numbers of claims, selected after
the common query. They retain the entire ambient checkpoint history. -/
namespace FormalProof4FHE.HasteBoots.AmbientDependentBatchOpening
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening CommittedBatchOpening
noncomputable section
variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix m queries height : ℕ}
  {claims : QueryData → Factor → ℕ}
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq K] [SampleableType ((Fin (2^front) × Fin b) → K)]


abbrev snapshots := @AmbientCommittedBatchSafeBound.snapshots
abbrev frozen := @AmbientCommittedBatchSafeBound.frozen

def protocol (enc : MerkleOracle.Encoding Input Digest (List F)) (domain : Fin (2 ^ height) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → (query : QueryData) → (factor : Factor) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix (claims query factor) m queries height)
    (emission : (Factor → Digest) × CommitMemory) (query : QueryData) (factor : Factor) :
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix (claims query factor) m queries height :=
  { build emission query factor with encoding := enc, domain := domain, root := emission.1 factor }

def continuation (enc : MerkleOracle.Encoding Input Digest (List F)) (domain : Fin (2 ^ height) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → (query : QueryData) → (factor : Factor) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix (claims query factor) m queries height)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (factors : List Factor) (emission : (Factor → Digest) × CommitMemory) :=
  SharedContinuation.program (selectQuery emission) (fun query => if enabled emission query then
    ShortCircuitSequence.program (fun factor => NativeBatchVerifier.step (protocol enc domain build emission query factor))
      factors (start emission query)
    else pure ⟨[], start emission query, false⟩)


def Wrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (heights : Cfg → ℕ) (tag : Factor → Cfg)
    (domain : Fin (2 ^ height) ↪ F) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (build : ((Factor → Digest) × CommitMemory) → (query : QueryData) → (factor : Factor) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix (claims query factor) m queries height)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (last : (QueryData × ShortCircuitSequence.Outcome Factor
      (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)) : Prop :=
  last.1.2.accepted = true ∧ ∃ factor claim,
    (protocol enc domain build first.1 last.1.1 factor).values claim ≠
      matrixEvaluation
        (NativeBatchChecks.left (front := front) (suffix := suffix) (protocol enc domain build first.1 last.1.1 factor).query claim)
        (NativeBatchChecks.right (front := front) (suffix := suffix) (protocol enc domain build first.1 last.1.1 factor).query claim)
        (MatrixOpeningSecurity.extract domain capacity radius
          (frozen enc dummy heights tag first factor))


theorem soundness [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Factor → Cfg) (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (geometry : ∀ factor, heights (tag factor) = height)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (build : ((Factor → Digest) × CommitMemory) → (query : QueryData) → (factor : Factor) →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix (claims query factor) m queries height)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m : Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (AmbientMatrixSource.Shape heights)
      (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
      initial)}[
        Wrong enc dummy heights tag domain capacity radius build outcome.1 outcome.2 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum := by
  let p := protocol enc domain build
  let arithmetic := fun first query factor (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) =>
    BatchMatrixSampling.ArithmeticBad domain capacity radius
      (frozen enc dummy heights tag first factor)
      (NativeBatchChecks.left (front := front) (suffix := suffix) (p first.1 query factor).query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) (p first.1 query factor).query)
      (p first.1 query factor).values (p first.1 query factor).testResponse
      (NativeBatchChecks.structured (p first.1 query factor).query (p first.1 query factor).groupResponse) data.1
  apply CommittedPrefixSafeBound.event_bound enc dummy (AmbientMatrixSource.Shape heights)
    (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
    initial audited (Wrong enc dummy heights tag domain capacity radius build)
    (fun first last => SharedSequence.AnyBad (arithmetic first last.1.1) last.1.2.results) _
  · intro first
    apply SharedContinuation.later_event_le enc dummy (AmbientMatrixSource.Shape heights)
      (selectQuery first.1) (fun query => if enabled first.1 query then
        ShortCircuitSequence.program (fun factor => NativeBatchVerifier.step (p first.1 query factor)) factors (start first.1 query)
        else pure ⟨[], start first.1 query, false⟩)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (fun query outcome => SharedSequence.AnyBad (arithmetic first query) outcome.1.results)
    intro query initial
    cases gate : enabled first.1 query with
    | false => simp [SharedSequence.AnyBad, prEvent_norm]
    | true =>
      simp only [reduceIte]
      exact ShortCircuitSequence.arithmetic_union_bound enc dummy (AmbientMatrixSource.Shape heights)
        (fun factor => NativeBatchVerifier.step (p first.1 query factor)) (arithmetic first query)
        (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius) factors
        (fun factor _ memory state => NativeBatchVerifier.arithmetic_bound (p first.1 query factor) basis dummy
          (AmbientMatrixSource.Shape heights) enough capacity radius
          (frozen enc dummy heights tag first factor) memory state small)
        (start first.1 query) initial
  · intro first last supported accepted
    obtain ⟨passed, factor, claim, different⟩ := accepted
    have recorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (AmbientMatrixSource.Shape heights) (tag factor) (snapshots heights tag first factor)
      (continuation enc domain build selectQuery enabled start factors first.1)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (RecordRoots.recorded _ _ first.2 (tag factor,first.1.1 factor) (List.mem_map_of_mem (complete factor))) last supported
    obtain ⟨selected, _, opened, openedSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy (AmbientMatrixSource.Shape heights)
        (selectQuery first.1) (fun query => if enabled first.1 query then
          ShortCircuitSequence.program (fun factor => NativeBatchVerifier.step (p first.1 query factor)) factors (start first.1 query)
          else pure ⟨[], start first.1 query, false⟩)
        (RecordRoots.state _ (requests tag factors first.1) first.2) last).mp supported
    subst last
    cases gate : enabled first.1 selected.1 with
    | false =>
      simp only [gate, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at openedSupported
      have equal := eq_of_mem_support_pure _ openedSupported
      subst opened
      exact (Bool.false_ne_true passed).elim
    | true =>
      simp only [gate, reduceIte] at openedSupported
      have verified := ShortCircuitSequence.accepted_cache_results enc dummy (AmbientMatrixSource.Shape heights)
        (fun factor => NativeBatchVerifier.step (p first.1 selected.1 factor)) factors
        (fun factor data cache => NativeBatchVerifier.checks (p first.1 selected.1 factor) data = true ∧
          ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
            (AuthenticatedColumnChecks.request (fun _ : Cfg => height) (tag factor) (first.1.1 factor) column) cache)
        (fun factor _ memory state outcome present accepted later extension =>
          NativeBatchVerifier.step_accepts_later (p first.1 selected.1 factor) dummy
            (AmbientMatrixSource.Shape heights) (tag factor) memory state outcome present accepted later extension)
        (start first.1 selected.1) selected.2 opened openedSupported passed
      have allFactors := ShortCircuitSequence.accepted_indices enc dummy (AmbientMatrixSource.Shape heights)
        (fun factor => NativeBatchVerifier.step (p first.1 selected.1 factor)) factors
        (start first.1 selected.1) selected.2 opened openedSupported passed
      have occurs : factor ∈ opened.1.results.map Prod.fst := by rw [allFactors]; exact complete factor
      obtain ⟨entry, member, same⟩ := List.mem_map.mp occurs
      subst factor
      obtain arithmeticBad | unavailable := AmbientBatchChecks.wrong_implies_arithmetic_or_disagreement enc dummy heights
        (tag entry.1) (geometry entry.1) (snapshots heights tag first entry.1) domain (p first.1 selected.1 entry.1).query
        (p first.1 selected.1 entry.1).values capacity radius (p first.1 selected.1 entry.1).testResponse
        (p first.1 selected.1 entry.1).groupResponse entry.2 opened.2 recorded
        (verified entry member).2 (verified entry member).1 ⟨claim, different⟩
      · exact Or.inl ⟨entry, member, arithmeticBad⟩
      · exact Or.inr unavailable


end
end FormalProof4FHE.HasteBoots.AmbientDependentBatchOpening
