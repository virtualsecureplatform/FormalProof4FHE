module
public import FormalProof4FHE.HasteBoots.RectangularPrivateSharedLookup
public import FormalProof4FHE.HasteBoots.RectangularOwnedRequestSources
@[expose] public section

/-! False original tuple acceptance for the original recorded source owners, the ideal private request
sampler, adaptive helpers, ordered EQ/common scalar batch, computed terminal
guard and original grouped PCS. Each request keeps its own table and actual
repetition count. One complete-run hash charge also covers terminal Bad. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.RectangularOwnedPrivateSharedLookup
noncomputable section
variable {F K Message Memory Cfg Input Digest Response SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg} {g : Geometry c row count (∑ i, repetitions i)} {symbolWidth : Root count (∑ i, repetitions i) → ℕ}
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [Fintype Digest]   [Fintype F]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → F)]

/-- Acceptance of a false tuple from any matching original recorded owner
family, or terminal history Bad, has the same bound and one hash charge. -/
theorem false_acceptance_or_bad_bound [∀ root : Root count (∑ i, repetitions i), NeZero (symbolWidth root)] [∀ root, NeZero (layout g root).m]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : RectangularRequestLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
      d padding c row count requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) (∑ i, repetitions i))
    (behavior : RectangularStagedSharedLookup.Emission count (∑ i, repetitions i) Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection F K Memory (d + padding) count (∑ i, repetitions i) (c + row) →
      (root : Root count (∑ i, repetitions i)) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distanceLarge : ∀ root, radius root < Fintype.card F)
    (distance : ∀ root, 3*radius root < Code.minDist (BlockCode.code (domain root) (g.m root) (symbolWidth root) :
      Set (Fin (2^heights (tag root)) → Fin (symbolWidth root) → F))) :
    let helperCommit := fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)
    let next := RectangularStagedSharedLookup.continuation (helperPadding := helperPadding) enc (RectangularRequestLookup.toParameters config) p small domain fallback behavior
    let experiment := StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests tag (List.finRange count))
      (RectangularStagedOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))
    Pr{let outcome ← experiment}[
      (RectangularOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome ∧
        outcome.2.2.1.2.accepted = true) ∨ CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (c + row) + RectangularStagedSharedLookup.pcsError (d := d) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain radius) +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (RectangularStagedOpening.sourceRequests tag (List.finRange count))
          (RectangularStagedOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg)))) := by
  dsimp only
  have bound := RectangularPrivateSharedLookup.false_acceptance_or_bad_bound (helperPadding := helperPadding) enc dummy config p small
    domain enough capacity radius fallback behavior sourceCommit pairEnough lookupSmall build distanceLarge distance
  dsimp only at bound
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) bound
  intro outcome supported event
  rcases event with accepted | failed
  · rcases RectangularOwnedRequestSources.original_false_reduction enc dummy config domain capacity radius sourceCommit
      (fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first))
      (RectangularStagedSharedLookup.continuation (helperPadding := helperPadding) enc (RectangularRequestLookup.toParameters config) p small domain fallback behavior)
      outcome supported accepted.1 with fresh | bad
    · exact Or.inl ⟨fresh,accepted.2⟩
    · exact Or.inr bad
  · exact Or.inr failed

end
end FormalProof4FHE.HasteBoots.RectangularOwnedPrivateSharedLookup
