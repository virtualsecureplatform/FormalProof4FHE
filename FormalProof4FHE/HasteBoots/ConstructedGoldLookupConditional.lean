module
public import FormalProof4FHE.HasteBoots.RectangularLookupConditionalSoundness
public import FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup
public import FormalProof4FHE.HasteBoots.StagedPrefixSafeBound
@[expose] public section

/-! Heterogeneous shared comparison algebra and original-root PCS errors at
an arbitrary audited incoming history, outside its final collision event. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
open FormalProof4FHE.HasteBoots.RectangularStagedSharedLookup
namespace FormalProof4FHE.HasteBoots.ConstructedGoldLookupConditional
noncomputable section
variable {K Message Memory Input Digest Response SourceMemory HelperMemory : Type}
  [Field K] [Algebra NativeFields.Goldilocks K] [DecidableEq Input] [DecidableEq Digest]
  {row count jobs : ℕ} {columns sizes : Fin jobs → ℕ} {mode : Mode}
  (ctx : ConstructedGoldLookupProtocol.Context row count jobs)
  [SampleableType Digest] [SampleableType (Fin 1 → K)] [SampleableType (Fin (2 + row) → K)]
  [∀ root, SampleableType (TestMatrix NativeFields.Goldilocks (2 ^ (layout (ConstructedGoldLookupProtocol.geometry ctx) root).front) (packedWidth (3 + 1) (3 + 0) root))]
  [∀ root, SampleableType (Fin (layout (ConstructedGoldLookupProtocol.geometry ctx) root).queries → Fin (2 ^ ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)))]
  [Fintype K] [DecidableEq K] [SampleableType K]

  [∀ root, SampleableType ((Fin (2 ^ (layout (ConstructedGoldLookupProtocol.geometry ctx) root).front) × Fin (packedWidth (3 + 1) (3 + 0) root)) → NativeFields.Goldilocks)]

theorem bad_prefix_safe_bound
    (enc : MerkleOracle.Encoding Input Digest (List NativeFields.Goldilocks)) (dummy : Digest)
    (config : Parameters NativeFields.Goldilocks K Message Memory ConstructedGoldSourceDescriptor.Configuration Input Digest SourceMemory HelperMemory 3 1 2 row count jobs columns sizes mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (radius : Root count jobs → ℕ)
    (fallback : Packet NativeFields.Goldilocks K (3 + 1) count (2 + row) jobs)
    (behavior : Emission count jobs Digest SourceMemory HelperMemory → RectangularSharedLookupPCS.Selection NativeFields.Goldilocks K Memory (3 + 1) count jobs (2 + row) →
      (root : Root count jobs) → Protocol NativeFields.Goldilocks Input Digest ConstructedGoldSourceDescriptor.Configuration Response Memory (packedWidth (3 + 1) (3 + 0)) (fun _ => 4) ConstructedGoldSourceDescriptor.heights (ConstructedGoldLookupProtocol.tag ctx) (layout (ConstructedGoldLookupProtocol.geometry ctx)) root)
    (sourceCommit : OracleComp (SharedSequence.Shared ConstructedGoldSourceDescriptor.Configuration Input Digest) (SourceEmission count Digest SourceMemory))
    (helperCommit : SourceEmission count Digest SourceMemory →
      OracleComp (SharedSequence.Shared ConstructedGoldSourceDescriptor.Configuration Input Digest) (HelperEmission jobs Digest HelperMemory))
    (distanceLarge : ∀ root, radius root < Fintype.card NativeFields.Goldilocks)
    (distance : ∀ root, 3*radius root < Code.minDist ((BlockCode.code ((ConstructedGoldLookupProtocol.domain ctx) root) ((ConstructedGoldLookupProtocol.geometry ctx).m root) ((fun _ => 4) root)).carrier :
      Set (Fin (2^ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)) → Fin ((fun _ => 4) root) → NativeFields.Goldilocks)))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg)) initial) :
    let next := RectangularStagedSharedLookup.continuation (d := 3) (padding := 1) (helperPadding := 0) (c := 2)
      (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
      (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4) enc config p small (ConstructedGoldLookupProtocol.domain ctx) fallback behavior
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg))
      (RectangularStagedOpening.sourceRequests (ConstructedGoldLookupProtocol.tag ctx) (List.finRange count))
      (RectangularStagedOpening.helperRequests (ConstructedGoldLookupProtocol.tag ctx) (List.finRange jobs)) sourceCommit helperCommit next
      initial)}[
        (¬AllPass (helperPadding := 0) enc dummy config (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldLookupProtocol.capacity ctx) radius outcome.1 outcome.2.1 ∧ outcome.2.2.1.2.accepted = true) ∧
        ¬CheckpointCollision.Bad (fun cfg => Skeleton.perfect (ConstructedGoldSourceDescriptor.heights cfg)) outcome.2.2.2] ≤
      (error K mode (2 + row) + pcsError (d := 3) (padding := 1) (helperPadding := 0) (g := (ConstructedGoldLookupProtocol.geometry ctx)) (symbolWidth := (fun _ => 4)) (ConstructedGoldLookupProtocol.domain ctx) radius) := by
  let : ∀ root : Root count jobs, NeZero (layout (ConstructedGoldLookupProtocol.geometry ctx) root).m :=
    fun root => ⟨Nat.ne_of_gt (ConstructedGoldStagedLookup.degree_positive ctx root)⟩
  exact RectangularLookupConditionalSoundness.bad_prefix_safe_bound
    (d := 3) (padding := 1) (helperPadding := 0) (c := 2)
    (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
    (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4)
    enc dummy config p small (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldStagedLookup.enough ctx)
    (ConstructedGoldLookupProtocol.capacity ctx) radius fallback behavior sourceCommit helperCommit
    distanceLarge distance initial audited

end
end FormalProof4FHE.HasteBoots.ConstructedGoldLookupConditional
