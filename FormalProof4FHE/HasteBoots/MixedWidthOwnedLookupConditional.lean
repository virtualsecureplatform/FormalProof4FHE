module
public import FormalProof4FHE.HasteBoots.MixedWidthPrivateLookupConditional
public import FormalProof4FHE.HasteBoots.MixedWidthOwnedRequestConditional
@[expose] public section

/-! Original request-specific comparison tuples on an arbitrary audited
incoming history, with all original source/helper widths and heights retained.
The enclosing PBS program owns the single final collision charge. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
open FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.MixedWidthOwnedLookupConditional
noncomputable section
variable {F K Message Memory Cfg Input Digest Response SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root count (∑ i, repetitions i) → Cfg} {g : Geometry c row count (∑ i, repetitions i)}
  {L : Root count (∑ i, repetitions i) → Type}
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra F (L root)] [Fintype F] [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → L root)]

/-- Original tuple failures selected after the actual run are bounded by
private pair, common algebra and grouped original-root PCS errors. -/
theorem false_acceptance_safe_bound [∀ root : Root count (∑ i, repetitions i), NeZero (packedWidth (d + padding) (d + helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (d + padding) (d + helperPadding) root)) F (L root))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : MixedWidthRequestSharedLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
      d padding c row count requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (d + padding) (d + helperPadding) root) (radius : Root count (∑ i, repetitions i) → ℕ)
    (fallback : Packet F K (d + padding) count (c + row) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission count (∑ i, repetitions i) Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection F K Memory (d + padding) count (∑ i, repetitions i) (c + row) →
      (root : Root count (∑ i, repetitions i)) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) heights tag (layout g) root)
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission count Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) initial) :
    let helperCommit := fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)
    let next := MixedWidthStagedSharedLookup.continuation enc (MixedWidthRequestSharedLookup.toParameters config) p small domain fallback behavior
    let experiment := StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (StagedVariableWidthBatchOpening.sourceRequests tag (List.finRange count))
      (StagedVariableWidthBatchOpening.helperRequests tag (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      initial
    Pr{let outcome ← experiment}[
      (MixedWidthOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome ∧
        outcome.2.2.1.2.accepted = true) ∧ ¬CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (c + row) + MixedWidthStagedSharedLookup.pcsError (d := d) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius)) := by
  dsimp only
  have bound := MixedWidthPrivateLookupConditional.false_acceptance_safe_bound analysisBasis enc dummy config p small
    domain enough capacity radius fallback behavior sourceCommit pairEnough lookupSmall build distance initial audited
  dsimp only at bound
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) bound
  intro outcome supported event
  obtain ⟨accepted,safe⟩ := event
  rcases MixedWidthOwnedRequestConditional.original_false_reduction enc dummy config domain capacity radius sourceCommit
      (fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first))
      (MixedWidthStagedSharedLookup.continuation enc (MixedWidthRequestSharedLookup.toParameters config) p small domain fallback behavior)
      initial audited outcome supported accepted.1 with fresh | bad
  · exact ⟨⟨fresh,accepted.2⟩,safe⟩
  · exact False.elim (safe bad)

end
end FormalProof4FHE.HasteBoots.MixedWidthOwnedLookupConditional
