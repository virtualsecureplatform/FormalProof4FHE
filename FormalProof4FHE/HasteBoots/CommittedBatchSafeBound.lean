module
public import FormalProof4FHE.HasteBoots.CommittedBatchOpening
public import FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound
@[expose] public section

/-! Native batch errors conditional on one arbitrary audited incoming state,
outside the final shared collision event. Each original root pays once for its
entire batch; the whole caller is responsible for the single hash charge. -/
namespace FormalProof4FHE.HasteBoots.CommittedBatchSafeBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening CommittedJointMatrixOpening CommittedBatchOpening
noncomputable section
variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix claims m queries height : ℕ}
  [SampleableType (TestMatrix F (2^front) b)] [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType Digest] [Field K] [Algebra F K]
  [Fintype F] [Fintype K] [DecidableEq K] [SampleableType ((Fin (2^front) × Fin b) → K)]

theorem soundness [NeZero m] [NeZero b]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (tag : Factor → Cfg) (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (domain : Fin (2 ^ height) ↪ F) (enough : m ≤ Fintype.card (Fin (2 ^ height)))
    (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → Factor →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m : Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (audited : CheckpointExecution.Audited enc dummy (fun _ : Cfg => Skeleton.perfect height) initial) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
      initial)}[
        Wrong enc dummy tag domain capacity radius build outcome.1 outcome.2 ∧
        ¬CheckpointCollision.Bad (fun _ : Cfg => Skeleton.perfect height) outcome.2.2] ≤
      (factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum := by
  let p := protocol enc domain build
  let arithmetic := fun first query factor (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) =>
    BatchMatrixSampling.ArithmeticBad domain capacity radius
      (JointMatrixOpening.frozen enc dummy tag (snapshots tag first) factor)
      (NativeBatchChecks.left (front := front) (suffix := suffix) (p first.1 query factor).query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) (p first.1 query factor).query)
      (p first.1 query factor).values (p first.1 query factor).testResponse
      (NativeBatchChecks.structured (p first.1 query factor).query (p first.1 query factor).groupResponse) data.1
  apply CommittedPrefixSafeBound.event_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
    initial audited (Wrong enc dummy tag domain capacity radius build)
    (fun first last => SharedSequence.AnyBad (arithmetic first last.1.1) last.1.2.results) _
  · intro first
    apply SharedContinuation.later_event_le enc dummy (fun _ : Cfg => Skeleton.perfect height)
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
      exact ShortCircuitSequence.arithmetic_union_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
        (fun factor => NativeBatchVerifier.step (p first.1 query factor)) (arithmetic first query)
        (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius) factors
        (fun factor _ memory state => NativeBatchVerifier.arithmetic_bound (p first.1 query factor) basis dummy
          (fun _ : Cfg => Skeleton.perfect height) enough capacity radius
          (JointMatrixOpening.frozen enc dummy tag (snapshots tag first) factor) memory state small)
        (start first.1 query) initial
  · intro first last supported accepted
    obtain ⟨passed, factor, claim, different⟩ := accepted
    have recorded := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
      (fun _ : Cfg => Skeleton.perfect height) (tag factor) (snapshots tag first factor)
      (continuation enc domain build selectQuery enabled start factors first.1)
      (RecordRoots.state _ (requests tag factors first.1) first.2)
      (snapshots_recorded tag factors complete first factor) last supported
    obtain ⟨selected, _, opened, openedSupported, equal⟩ :=
      (SharedContinuation.support_program enc dummy (fun _ : Cfg => Skeleton.perfect height)
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
      have verified := ShortCircuitSequence.accepted_cache_results enc dummy (fun _ : Cfg => Skeleton.perfect height)
        (fun factor => NativeBatchVerifier.step (p first.1 selected.1 factor)) factors
        (fun factor data cache => NativeBatchVerifier.checks (p first.1 selected.1 factor) data = true ∧
          ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
            (AuthenticatedColumnChecks.request (fun _ : Cfg => height) (tag factor) (first.1.1 factor) column) cache)
        (fun factor _ memory state outcome present accepted later extension =>
          NativeBatchVerifier.step_accepts_later (p first.1 selected.1 factor) dummy
            (fun _ : Cfg => Skeleton.perfect height) (tag factor) memory state outcome present accepted later extension)
        (start first.1 selected.1) selected.2 opened openedSupported passed
      have allFactors := ShortCircuitSequence.accepted_indices enc dummy (fun _ : Cfg => Skeleton.perfect height)
        (fun factor => NativeBatchVerifier.step (p first.1 selected.1 factor)) factors
        (start first.1 selected.1) selected.2 opened openedSupported passed
      have occurs : factor ∈ opened.1.results.map Prod.fst := by rw [allFactors]; exact complete factor
      obtain ⟨entry, member, same⟩ := List.mem_map.mp occurs
      subst factor
      obtain arithmeticBad | unavailable := NativeBatchChecks.wrong_implies_arithmetic_or_disagreement enc dummy
        (tag entry.1) (snapshots tag first entry.1) domain (p first.1 selected.1 entry.1).query
        (p first.1 selected.1 entry.1).values capacity radius (p first.1 selected.1 entry.1).testResponse
        (p first.1 selected.1 entry.1).groupResponse entry.2 opened.2 recorded
        (verified entry member).2 (verified entry member).1 ⟨claim, different⟩
      · exact Or.inl ⟨entry, member, arithmeticBad⟩
      · exact Or.inr unavailable


end
end FormalProof4FHE.HasteBoots.CommittedBatchSafeBound
