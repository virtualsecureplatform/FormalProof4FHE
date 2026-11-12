module
public import FormalProof4FHE.HasteBoots.PaddedMixedWidthRequestSharedLookup
@[expose] public section

/-! False original tuple acceptance for the actual ideal private request
sampler, adaptive helpers, ordered EQ/common scalar batch, computed terminal
guard and original grouped PCS. Each request keeps its own table and actual
repetition count. One complete-run hash charge also covers terminal Bad. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.PaddedMixedWidthStagedPrivateSharedLookup
noncomputable section
variable {F K Message Memory Cfg Input Digest Response SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg} {g : Geometry c row count (∑ i, repetitions i)}
  {L : Root count (∑ i, repetitions i) → Type}
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]

/-- False original requests and all sampled jobs passing are bounded by the
maximum request-specific repeated error, without a union over requests. -/
theorem allPass_bound {p : ℕ} [CharP K p]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : PaddedMixedWidthRequestSharedLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
      d padding c row count requests widths sizes repetitions mode)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (build : PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (PaddedMixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (next : PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory → RequestLookupPairMiddle.Emission K Digest HelperMemory repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg))) :
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
      (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit
      (fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)) next initial)}[
        (∃ index i, ∀ j, PaddedMixedWidthRequestSharedLookup.tuples enc dummy config domain capacity radius outcome.1 index i ≠ config.tables index j) ∧
        PaddedMixedWidthStagedSharedLookup.AllPass enc dummy (PaddedMixedWidthRequestSharedLookup.toParameters config) domain capacity radius outcome.1 outcome.2.1] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions := by
  have bound := RequestLookupPairMiddle.staged_bound enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
    (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit config.tables pairEnough build next
    config.active (PaddedMixedWidthRequestSharedLookup.tuples enc dummy config domain capacity radius)
    (fun first index i => algebraMap F K (config.multiplicities first index i)) lookupSmall initial
  refine (prEvent_mono _ _ _ ?_).trans bound
  intro outcome event
  exact ⟨event.1,(PaddedMixedWidthRequestSharedLookup.allPass_iff enc dummy config domain capacity radius outcome.1 outcome.2.1).mp event.2⟩

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [Fintype Digest] [∀ root, Field (L root)] [∀ root, Algebra F (L root)] [Fintype F] [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → L root)]

/-- Fresh-source false lookup acceptance OR the common terminal history
exception on the complete request-specific private shared execution. The
pair, arithmetic, and PCS bounds are derived internally; source tuples remain
fixed at their original pre-pair prefix. -/
theorem false_acceptance_or_bad_bound [∀ root : Root count (∑ i, repetitions i), NeZero (packedWidth (d + padding) (d + helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (d + padding) (d + helperPadding) root)) F (L root))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : PaddedMixedWidthRequestSharedLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
      d padding c row count requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) (∑ i, repetitions i))
    (behavior : PaddedMixedWidthStagedSharedLookup.Emission count (∑ i, repetitions i) Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      PaddedMixedWidthSharedLookupPCS.Selection F K Memory (d + padding) count (∑ i, repetitions i) (c + row) →
      (root : Root count (∑ i, repetitions i)) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : PaddedMixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (PaddedMixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3) :
    let helperCommit := fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)
    let next := PaddedMixedWidthStagedSharedLookup.continuation enc (PaddedMixedWidthRequestSharedLookup.toParameters config) p small domain fallback behavior
    let experiment := StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
      (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
    Pr{let outcome ← experiment}[
      ((∃ index i, ∀ j, PaddedMixedWidthRequestSharedLookup.tuples enc dummy config domain capacity radius outcome.1 index i ≠ config.tables index j) ∧
        outcome.2.2.1.2.accepted = true) ∨ CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (c + row) + PaddedMixedWidthStagedSharedLookup.pcsError (d := d) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
          (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))) := by
  dsimp only
  have bounded := PaddedMixedWidthStagedSharedLookupSoundness.bad_prefix_or_bad_bound analysisBasis enc dummy
    (PaddedMixedWidthRequestSharedLookup.toParameters config) p small domain enough capacity radius fallback behavior sourceCommit
    (fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)) distance
  dsimp only at bounded
  have paired := allPass_bound enc dummy config domain capacity radius pairEnough lookupSmall sourceCommit build
    (PaddedMixedWidthStagedSharedLookup.continuation enc (PaddedMixedWidthRequestSharedLookup.toParameters config) p small domain fallback behavior)
    (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
  refine (prEvent_mono _ _ _ ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add paired bounded))
  intro outcome event
  rcases event with accepted | bad
  · by_cases pass : PaddedMixedWidthStagedSharedLookup.AllPass enc dummy (PaddedMixedWidthRequestSharedLookup.toParameters config) domain capacity radius outcome.1 outcome.2.1
    · exact Or.inl ⟨accepted.1,pass⟩
    · exact Or.inr (Or.inl ⟨pass,accepted.2⟩)
  · exact Or.inr (Or.inr bad)
end
end FormalProof4FHE.HasteBoots.PaddedMixedWidthStagedPrivateSharedLookup
