module

public import FormalProof4FHE.HasteBoots.NativeBatchVerifier
public import FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix

@[expose] public section

/-!
# Committed native batches with one whole-execution availability charge

Roots freeze at the actual commitment prefix before adaptive query selection.
Each root uses one shared-test/shared-column batch. A disabled gate skips all
opening work; the root loop stops on its first rejection. Trusted encoding,
domain and roots override the behavior factory. Successful wrong supplied
values cost one PCS arithmetic error per listed root and one expected hash
charge for this exact complete execution, with no query-count multiplier or
replay/safety/PCS certificate. Fiat--Shamir, native NTT/Rust refinement and
honest scheduler completion remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.CommittedJointMatrixOpening

namespace FormalProof4FHE.HasteBoots.CommittedBatchOpening

noncomputable section

variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix claims m queries height : ℕ}

def protocol (enc : MerkleOracle.Encoding Input Digest (List F)) (domain : Fin (2 ^ height) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → Factor →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (emission : (Factor → Digest) × CommitMemory) (query : QueryData) (factor : Factor) :
    NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height :=
  { build emission query factor with encoding := enc, domain := domain, root := emission.1 factor }

variable [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

def continuation (enc : MerkleOracle.Encoding Input Digest (List F)) (domain : Fin (2 ^ height) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → Factor →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (factors : List Factor) (emission : (Factor → Digest) × CommitMemory) :=
  SharedContinuation.program (selectQuery emission) (fun query => if enabled emission query then
    ShortCircuitSequence.program (fun factor => NativeBatchVerifier.step (protocol enc domain build emission query factor))
      factors (start emission query)
    else pure ⟨[], start emission query, false⟩)

/-- Erasing the proof-only commitment snapshot gives exactly the actual
complete shared execution, including disabled and rejected branches. -/
theorem project_witness [SampleableType Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (tag : Factor → Cfg)
    (domain : Fin (2 ^ height) ↪ F)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → Factor →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory) (factors : List Factor) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$>
      MultiCommitmentPrefix.witness enc dummy (fun _ : Cfg => Skeleton.perfect height) (requests tag factors) commit
        (continuation enc domain build selectQuery enabled start factors)
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (fun _ : Cfg => Skeleton.perfect height))
        (MultiCommitmentPrefix.program (requests tag factors) commit
          (continuation enc domain build selectQuery enabled start factors))).run
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) :=
  MultiCommitmentPrefix.project_witness enc dummy (fun _ : Cfg => Skeleton.perfect height) (requests tag factors) commit
    (continuation enc domain build selectQuery enabled start factors) (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height))

/-- False supplied values refer to the one prefix-frozen decoded source of
that root, even though its batch queries are selected adaptively afterwards. -/
def Wrong (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (tag : Factor → Cfg)
    (domain : Fin (2 ^ height) ↪ F) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → Factor →
      NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (first : ((Factor → Digest) × CommitMemory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (last : (QueryData × ShortCircuitSequence.Outcome Factor
      (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height)) : Prop :=
  last.1.2.accepted = true ∧ ∃ factor claim,
    (protocol enc domain build first.1 last.1.1 factor).values claim ≠
      matrixEvaluation
        (NativeBatchChecks.left (front := front) (suffix := suffix) (protocol enc domain build first.1 last.1.1 factor).query claim)
        (NativeBatchChecks.right (front := front) (suffix := suffix) (protocol enc domain build first.1 last.1.1 factor).query claim)
        (MatrixOpeningSecurity.extract domain capacity radius
          (JointMatrixOpening.frozen enc dummy tag (snapshots tag first) factor))

variable [SampleableType Digest] [Fintype Digest] [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

/-- No initial root-safety certificate or adversary query budget is assumed.
The charge includes the commitment, adaptive query phase, rejected paths and
all actually issued interleaved worker calls, exactly once. -/
theorem soundness_from_empty [NeZero m] [NeZero b]
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
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) domain) m : Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (fun _ : Cfg => Skeleton.perfect height)
      (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
      (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)))}[
        Wrong enc dummy tag domain capacity radius build outcome.1 outcome.2] ≤
      (factors.map (fun _ => JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) domain radius)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun _ : Cfg => Skeleton.perfect height))
        (CheckpointCollision.loss unifSpec (fun _ : Cfg => Skeleton.perfect height))
        (MultiCommitmentPrefix.program (requests tag factors) commit
          (continuation enc domain build selectQuery enabled start factors))
        (CheckpointExecution.empty (fun _ : Cfg => Skeleton.perfect height)) := by
  let p := protocol enc domain build
  let arithmetic := fun first query factor (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) =>
    BatchMatrixSampling.ArithmeticBad domain capacity radius
      (JointMatrixOpening.frozen enc dummy tag (snapshots tag first) factor)
      (NativeBatchChecks.left (front := front) (suffix := suffix) (p first.1 query factor).query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) (p first.1 query factor).query)
      (p first.1 query factor).values (p first.1 query factor).testResponse
      (NativeBatchChecks.structured (p first.1 query factor).query (p first.1 query factor).groupResponse) data.1
  apply MultiCommitmentPrefix.event_bound enc dummy (fun _ : Cfg => Skeleton.perfect height)
    (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors)
    (Wrong enc dummy tag domain capacity radius build)
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

end FormalProof4FHE.HasteBoots.CommittedBatchOpening
