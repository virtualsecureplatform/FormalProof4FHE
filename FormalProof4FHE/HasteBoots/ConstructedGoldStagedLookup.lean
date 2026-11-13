module
public import FormalProof4FHE.HasteBoots.ConstructedGoldLookupProtocol
public import FormalProof4FHE.HasteBoots.RectangularStagedOpening
@[expose] public section

/-! Native-constructed Gold source/helper protocols in one actual staged
execution. Sources are recorded before the adaptive helper phase; each root
retains its own height, split and query count, with independent symbol width.
One complete-run availability charge covers every recorded root and worker. -/
open OracleSpec OracleComp BinaryTree
namespace FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup
open NativeFields (Goldilocks)
open ConstructedGoldSourceDescriptor (Configuration heights)
open ConstructedGoldLookupProtocol (Context geometry tag domain capacity Behavior)
open PaddedMixedWidthLookupOpeningFamily (Root packedWidth)
noncomputable section
variable {row count repetitions : ℕ}

def layout (ctx : Context row count repetitions) := PaddedMixedWidthLookupOpeningFamily.layout (geometry ctx)

theorem degree_positive (ctx : Context row count repetitions) (root : Root count repetitions) :
    0 < (layout ctx root).m :=
  (ConstructedGoldSourceDescriptor.degree_bounds
    (ClassicalGoldRoleBundle.entry ctx.bundle (ClassicalGoldRoleBundle.roleIndex
      (ConstructedGoldLookupGeometry.stage ctx.sources ctx.helpers root)))
    (ClassicalGoldRoleBundle.entry_good ctx.bundle (ClassicalGoldRoleBundle.roleIndex
      (ConstructedGoldLookupGeometry.stage ctx.sources ctx.helpers root)))).1

theorem enough (ctx : Context row count repetitions) (root : Root count repetitions) :
    (layout ctx root).m ≤ Fintype.card (Fin (2^heights (tag ctx root))) := by
  rw [Fintype.card_fin]
  exact Nat.le_of_lt (ConstructedGoldSourceDescriptor.degree_bounds
    (ClassicalGoldRoleBundle.entry ctx.bundle (ClassicalGoldRoleBundle.roleIndex
      (ConstructedGoldLookupGeometry.stage ctx.sources ctx.helpers root)))
    (ClassicalGoldRoleBundle.entry_good ctx.bundle (ClassicalGoldRoleBundle.roleIndex
      (ConstructedGoldLookupGeometry.stage ctx.sources ctx.helpers root)))).2

abbrev Emission (Digest SourceMemory HelperMemory : Type) (count repetitions : ℕ) :=
  ((Root count repetitions) → Digest) ×
    RectangularStagedOpening.CommitMemory (Fin count) (Fin repetitions) Digest SourceMemory HelperMemory
abbrev Packet (K : Type) (row count repetitions : ℕ) :=
  PaddedMixedWidthLookupOpeningFamily.Packet Goldilocks K 4 count (2+row) repetitions

variable {K Input Digest Response Memory SourceMemory HelperMemory : Type}
  [Field K] [Algebra Goldilocks K]

def build (ctx : Context row count repetitions) (basis : Module.Basis (Fin 3) Goldilocks K)
    (enc : MerkleOracle.Encoding Input Digest (List Goldilocks))
    (behavior : Emission Digest SourceMemory HelperMemory count repetitions → Packet K row count repetitions →
      (root : Root count repetitions) → Behavior Input Digest Response Memory ctx root)
    (emission : Emission Digest SourceMemory HelperMemory count repetitions) (packet : Packet K row count repetitions)
    (root : Root count repetitions) :=
  ConstructedGoldLookupProtocol.protocol ctx basis packet enc emission.1 root (behavior emission packet root)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] [Fintype Digest]

/-- All capacity and degree premises come from the native constructors. The
remaining radius conditions concern the public rectangular PCS error analysis. -/
theorem soundness_from_empty (ctx : Context row count repetitions)
    [∀ root, SampleableType (InteractiveAuthenticatedOpening.TestMatrix Goldilocks (2^(layout ctx root).front) (packedWidth 4 3 root))]
    [∀ root, SampleableType (Fin (layout ctx root).queries → Fin (2^heights (tag ctx root)))]
    [∀ root, SampleableType ((Fin (2^(layout ctx root).front) × Fin (packedWidth 4 3 root)) → Goldilocks)]
    (basis : Module.Basis (Fin 3) Goldilocks K)
    (enc : MerkleOracle.Encoding Input Digest (List Goldilocks)) (dummy : Digest)
    (radius : Root count repetitions → ℕ)
    (behavior : Emission Digest SourceMemory HelperMemory count repetitions → Packet K row count repetitions →
      (root : Root count repetitions) → Behavior Input Digest Response Memory ctx root)
    (sourceCommit : OracleComp (SharedSequence.Shared Configuration Input Digest)
      (RectangularStagedOpening.SourceEmission (Fin count) Digest SourceMemory))
    (helperCommit : RectangularStagedOpening.SourceEmission (Fin count) Digest SourceMemory →
      OracleComp (SharedSequence.Shared Configuration Input Digest)
        (RectangularStagedOpening.HelperEmission (Fin repetitions) Digest HelperMemory))
    (selectQuery : Emission Digest SourceMemory HelperMemory count repetitions →
      OracleComp (SharedSequence.Shared Configuration Input Digest) (Packet K row count repetitions))
    (enabled : Emission Digest SourceMemory HelperMemory count repetitions → Packet K row count repetitions → Bool)
    (start : Emission Digest SourceMemory HelperMemory count repetitions → Packet K row count repetitions → Memory)
    (large : ∀ root, radius root < Fintype.card Goldilocks)
    (small : ∀ root, 3*radius root < Code.minDist ((BlockCode.code (domain ctx root) (layout ctx root).m 4).carrier :
      Set (Fin (2^heights (tag ctx root)) → Fin 4 → Goldilocks))) :
    let next := RectangularStagedOpening.continuation (width := packedWidth 4 3) (symbolWidth := fun _ => 4) (heights := heights) (tag := tag ctx) (layout := layout ctx)
      enc (domain ctx) (build ctx basis enc behavior) selectQuery enabled start (List.finRange count) (List.finRange repetitions)
    Pr{let outcome ← (StagedCommitmentPrefix.witness enc dummy (fun cfg => Skeleton.perfect (heights cfg))
      (RectangularStagedOpening.sourceRequests (tag ctx) (List.finRange count))
      (RectangularStagedOpening.helperRequests (tag ctx) (List.finRange repetitions)) sourceCommit helperCommit next
      (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))))}[
        RectangularRecordedOpening.Wrong enc dummy (domain ctx) (capacity ctx) radius (build ctx basis enc behavior)
          (RectangularStagedOpening.emission outcome.1.1 outcome.2.1.1)
          (RectangularStagedOpening.snapshots heights (tag ctx) outcome.1 outcome.2.1) outcome.2.2] ≤
      ((RectangularStagedOpening.factors (List.finRange count) (List.finRange repetitions)).map fun root =>
        RectangularVariableWidthOpening.error (domain ctx root) (layout ctx root).m 4 (packedWidth 4 3 root)
          (layout ctx root).queries (radius root)).sum +
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (StagedCommitmentPrefix.program
          (RectangularStagedOpening.sourceRequests (tag ctx) (List.finRange count))
          (RectangularStagedOpening.helperRequests (tag ctx) (List.finRange repetitions)) sourceCommit helperCommit next)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  let : ∀ root : Root count repetitions, NeZero (layout ctx root).m :=
    fun root => ⟨Nat.ne_of_gt (degree_positive ctx root)⟩
  exact RectangularStagedOpening.soundness_from_empty
    (width := packedWidth 4 3) (symbolWidth := fun _ => 4) (heights := heights) (tag := tag ctx) (layout := layout ctx) enc dummy (List.finRange count) (List.finRange repetitions)
    (fun root => List.mem_finRange root) (fun root => List.mem_finRange root)
    (domain ctx) (enough ctx) (capacity ctx) radius (build ctx basis enc behavior) sourceCommit helperCommit
    selectQuery enabled start large small

end
end FormalProof4FHE.HasteBoots.ConstructedGoldStagedLookup
