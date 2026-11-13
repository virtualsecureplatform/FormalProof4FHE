module
public import FormalProof4FHE.HasteBoots.RectangularOwnedLookupConditional
public import FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup
@[expose] public section

/-! Original request-specific comparison tuples on an arbitrary audited
incoming history, with all original source/helper widths and ConstructedGoldSourceDescriptor.heights retained.
The enclosing PBS program owns the single final collision charge. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional
noncomputable section
theorem radius_large {F Position : Type} [Field F] [DecidableEq F] [Fintype F]
    [Fintype Position] [Nonempty Position] (domain : Position ↪ F) (m symbols radius : ℕ) [NeZero symbols]
    (positive : 0 < m)
    (distance : 3*radius < Code.minDist (BlockCode.code domain m symbols : Set (Position → Fin symbols → F))) :
    radius < Fintype.card F := by
  rw [BlockCode.minDist domain m symbols positive] at distance
  have fits := Fintype.card_le_of_injective domain domain.injective
  have sizePositive : 0 < Fintype.card Position := Fintype.card_pos
  omega

theorem radius_large_of_distance {row count jobs : ℕ}
    (ctx : ConstructedGoldLookupProtocol.Context row count jobs) (root : Root count jobs) (radius : ℕ)
    (distance : 3*radius < Code.minDist
      (BlockCode.code (ConstructedGoldLookupProtocol.domain ctx root)
        (ConstructedGoldStagedLookup.layout ctx root).m 4).carrier) :
    radius < Fintype.card NativeFields.Goldilocks :=
  radius_large (ConstructedGoldLookupProtocol.domain ctx root) (ConstructedGoldStagedLookup.layout ctx root).m 4 radius
    (ConstructedGoldStagedLookup.degree_positive ctx root) distance

variable {K Message Memory Input Digest Response SourceMemory HelperMemory : Type}
  [Field K] [Algebra NativeFields.Goldilocks K] [DecidableEq Input] [DecidableEq Digest]
  {row count requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  (ctx : ConstructedGoldLookupProtocol.Context row count (∑ i, repetitions i))
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (2 + row) → K)]
  [∀ root, SampleableType (TestMatrix NativeFields.Goldilocks (2 ^ (layout (ConstructedGoldLookupProtocol.geometry ctx) root).front) (packedWidth (3 + 1) (3 + 0) root))]
  [∀ root, SampleableType (Fin (layout (ConstructedGoldLookupProtocol.geometry ctx) root).queries → Fin (2 ^ ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)))]

  [∀ root, SampleableType ((Fin (2 ^ (layout (ConstructedGoldLookupProtocol.geometry ctx) root).front) × Fin (packedWidth (3 + 1) (3 + 0) root)) → NativeFields.Goldilocks)]

/-- Original tuple failures selected after the actual run are bounded by
private pair, common algebra and grouped original-root PCS errors. -/
theorem false_acceptance_safe_bound
    (enc : MerkleOracle.Encoding Input Digest (List NativeFields.Goldilocks)) (dummy : Digest)
    (config : RectangularRequestLookup.Parameters NativeFields.Goldilocks K Message Memory ConstructedGoldSourceDescriptor.Configuration Input Digest SourceMemory HelperMemory
      3 1 2 row count requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (radius : Root count (∑ i, repetitions i) → ℕ)
    (fallback : Packet NativeFields.Goldilocks K (3 + 1) count (2 + row) (∑ i, repetitions i))
    (behavior : RectangularStagedSharedLookup.Emission count (∑ i, repetitions i) Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection NativeFields.Goldilocks K Memory (3 + 1) count (∑ i, repetitions i) (2 + row) →
      (root : Root count (∑ i, repetitions i)) → Protocol NativeFields.Goldilocks Input Digest ConstructedGoldSourceDescriptor.Configuration Response Memory (packedWidth (3 + 1) (3 + 0)) (fun _ => 4) ConstructedGoldSourceDescriptor.heights (ConstructedGoldLookupProtocol.tag ctx) (layout (ConstructedGoldLookupProtocol.geometry ctx)) root)
    (sourceCommit : OracleComp (SharedSequence.Shared ConstructedGoldSourceDescriptor.Configuration Input Digest) (RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory))
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : RectangularStagedSharedLookup.SourceEmission count Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared ConstructedGoldSourceDescriptor.Configuration Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, 3*radius root < Code.minDist ((BlockCode.code ((ConstructedGoldLookupProtocol.domain ctx) root) ((ConstructedGoldLookupProtocol.geometry ctx).m root) ((fun _ => 4) root)).carrier :
      Set (Fin (2^ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)) → Fin ((fun _ => 4) root) → NativeFields.Goldilocks)))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg)) initial) :
    let helperCommit := fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)
    let next := RectangularStagedSharedLookup.continuation (d := 3) (padding := 1) (helperPadding := 0) (c := 2)
      (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
      (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4) enc (RectangularRequestLookup.toParameters config) p small (ConstructedGoldLookupProtocol.domain ctx) fallback behavior
    let experiment := StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg))
      (RectangularStagedOpening.sourceRequests (ConstructedGoldLookupProtocol.tag ctx) (List.finRange count))
      (RectangularStagedOpening.helperRequests (ConstructedGoldLookupProtocol.tag ctx) (List.finRange (∑ i, repetitions i))) sourceCommit helperCommit next
      initial
    Pr{let outcome ← experiment}[
      (RectangularOwnedRequestSources.OriginalFalse enc dummy config (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldLookupProtocol.capacity ctx) radius outcome ∧
        outcome.2.2.1.2.accepted = true) ∧ ¬CheckpointCollision.Bad (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg)) outcome.2.2.2] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (2 + row) + RectangularStagedSharedLookup.pcsError (d := 3) (padding := 1) (helperPadding := 0) (g := (ConstructedGoldLookupProtocol.geometry ctx)) (symbolWidth := (fun _ => 4)) (ConstructedGoldLookupProtocol.domain ctx) radius)) := by
  let : ∀ root : Root count (∑ i, repetitions i), NeZero (layout (ConstructedGoldLookupProtocol.geometry ctx) root).m :=
    fun root => ⟨Nat.ne_of_gt (ConstructedGoldStagedLookup.degree_positive ctx root)⟩
  have large : ∀ root, radius root < Fintype.card NativeFields.Goldilocks :=
    fun root => radius_large_of_distance ctx root (radius root) (distance root)
  exact RectangularOwnedLookupConditional.false_acceptance_safe_bound
    (d := 3) (padding := 1) (helperPadding := 0) (c := 2)
    (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
    (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4)
    enc dummy config p small (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldStagedLookup.enough ctx)
    (ConstructedGoldLookupProtocol.capacity ctx) radius fallback behavior sourceCommit pairEnough lookupSmall build
    large distance initial audited

end
end FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional
