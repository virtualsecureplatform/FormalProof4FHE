module
public import FormalProof4FHE.HasteBoots.RecordedHeterogeneousBatchOpening
public import FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound
@[expose] public section

/-! Native original-root batches with per-source physical layouts on arbitrary
inherited audited histories. No handler restart or local hash charge is used. -/
namespace FormalProof4FHE.HasteBoots.AmbientHeterogeneousBatchOpening
open OracleSpec OracleComp BinaryTree Matrix
open InteractiveAuthenticatedOpening HeterogeneousBatchOpening
noncomputable section
variable {F K Factor Input Digest Cfg Response Memory CommitMemory QueryData : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b : ℕ} {heights : Cfg → ℕ} {tag : Factor → Cfg} {layout : Factor → Layout}
  [SampleableType Digest]
  [∀ factor, SampleableType (TestMatrix F (2^(layout factor).front) b)]
  [∀ factor, SampleableType (Fin (layout factor).queries → Fin (2^heights (tag factor)))]
  [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [∀ factor, SampleableType ((Fin (2^(layout factor).front) × Fin b) → K)]

/-- Every source pays its own PCS rate once, even with many claims or aliased
contexts. Root snapshots are frozen before query selection, while the complete
incoming audit and all other checkpoint heights are preserved. -/
theorem soundness [NeZero b] [∀ factor, NeZero (layout factor).m]
    (basis : Module.Basis (Fin b) F K)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (domain : ∀ factor, Fin (2^heights (tag factor)) ↪ F)
    (enough : ∀ factor, (layout factor).m ≤ Fintype.card (Fin (2^heights (tag factor))))
    (capacity : ∀ factor, 2^(layout factor).suffix ≤ (layout factor).m*b) (radius : Factor → ℕ)
    (build : ((Factor → Digest) × CommitMemory) → QueryData → (factor : Factor) →
      Protocol F Input Digest Cfg Response Memory b heights tag layout factor)
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) ((Factor → Digest) × CommitMemory))
    (selectQuery : ((Factor → Digest) × CommitMemory) → OracleComp (SharedSequence.Shared Cfg Input Digest) QueryData)
    (enabled : ((Factor → Digest) × CommitMemory) → QueryData → Bool)
    (start : ((Factor → Digest) × CommitMemory) → QueryData → Memory)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (domain factor)) (layout factor).m :
        Set (Fin (2^heights (tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) initial) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors) initial)}[
      Wrong enc dummy domain capacity radius build outcome.1 outcome.2 ∧
      ¬CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2] ≤
      (factors.map (fun factor => JointMatrixOpening.error (K := K) (m := (layout factor).m) (b := b)
        (queries := (layout factor).queries) (domain factor) (radius factor))).sum := by
  apply CommittedPrefixSafeBound.event_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (requests tag factors) commit (continuation enc domain build selectQuery enabled start factors) initial audited
    (Wrong enc dummy domain capacity radius build)
    (fun first last => SharedSequence.AnyBad (fun _ => RecordedHeterogeneousBatchOpening.Arithmetic enc dummy domain capacity radius build
      first.1 (snapshots heights tag first) last.1.1) last.1.2.results) _
  · intro first
    exact RecordedHeterogeneousBatchOpening.arithmetic_bound basis enc dummy factors domain enough capacity radius build
      selectQuery enabled start first.1 (snapshots heights tag first)
      (RecordRoots.state (fun cfg => Skeleton.perfect (heights cfg)) (requests tag factors first.1) first.2) small
  · intro first last supported wrong
    exact RecordedHeterogeneousBatchOpening.reduce_wrong enc dummy factors complete domain capacity radius build selectQuery enabled start
      first.1 (snapshots heights tag first) (fun _ => rfl)
      (RecordRoots.state (fun cfg => Skeleton.perfect (heights cfg)) (requests tag factors first.1) first.2)
      (snapshots_recorded heights tag factors complete first) last supported wrong

end
end FormalProof4FHE.HasteBoots.AmbientHeterogeneousBatchOpening
