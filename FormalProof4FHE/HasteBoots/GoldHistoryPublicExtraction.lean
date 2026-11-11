module
public import FormalProof4FHE.HasteBoots.GoldHistorySourceTable
public import FormalProof4FHE.HasteBoots.NativeGoldPublicSource
public import FormalProof4FHE.HasteBoots.CacheBackedCodeOrigin
@[expose] public section

/-! The existing executable public extractor, selected by the immutable
complete-history source owner, computes the common analysis cube. Original
constructor provenance and the existing lifetime radius condition discharge
backend validity and unique decoding; physical work remains separate. -/
namespace FormalProof4FHE.HasteBoots.GoldHistoryPublicExtraction
open NativeGoldBatchPcsProgram (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
open GoldCommonSourceTable (Capacity)
noncomputable section

def rectangular (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : Capacity ctx.parameters) :=
  NativeGoldPublicSource.table dummy root ctx (SourceHistoryOwnerLog.selected history context root) radius capacity

/-- This entry point reads public history and retained dimensions, and has no
world, opening query, claimed value, response or scheduler argument. -/
def cube (ctx : Context) (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (capacity : Capacity ctx.parameters) (geometry : GoldHistorySourceTable.Geometry ctx.parameters) :=
  QueryReindex.source geometry.1 (QueryRectangularNativeMeaning.source ctx.parameters
    (ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val) geometry.2
    (rectangular ctx dummy context root history radius capacity))

/-- The executable entry point reads only retained parameters from call
records. Changing queries, values, responses, parent or fuel cannot select a
different table, even before invoking the analysis compatibility theorem. -/
theorem cube_congr (first second : Context) (parameters : first.parameters = second.parameters)
    (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (firstCapacity : Capacity first.parameters) (secondCapacity : Capacity second.parameters)
    (firstGeometry : GoldHistorySourceTable.Geometry first.parameters)
    (secondGeometry : GoldHistorySourceTable.Geometry second.parameters) :
    HEq (cube first dummy context root history radius firstCapacity firstGeometry)
      (cube second dummy context root history radius secondCapacity secondGeometry) := by
  cases first
  cases second
  cases parameters
  rfl

theorem rectangular_eq_analysis (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) :
    rectangular ctx dummy context root history radius (origin.capacityAt ctx rfl) =
      GoldCommonSourceTable.rectangular ctx.parameters (origin.primitiveAt ctx rfl) (origin.capacityAt ctx rfl)
        dummy context root (SourceHistoryOwnerLog.selected history context root) radius := by
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block
    origin.request.blowup ctx.parameters.code (origin.constructedAt ctx rfl)).2
  have uniqueRadius : 2*radius < 2^(NativeGoldBlockCode.logSize ctx.parameters.code)-ctx.parameters.code.messageBlocks.val+1 := by
    rw [← blocks]
    omega
  funext left right channel
  exact NativeGoldPublicSource.extract_eq_analysis dummy context root ctx _ origin.tables origin.request.message origin.request.block
    origin.request.blowup (origin.constructedAt ctx rfl) (origin.primitiveAt ctx rfl) radius uniqueRadius
    (origin.capacityAt ctx rfl) left right channel

theorem cube_eq_analysis (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (dummy context root : Digest) (history : List Observation) (radius : ℕ)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1)
    (geometry : GoldHistorySourceTable.Geometry ctx.parameters) :
    cube ctx dummy context root history radius (origin.capacityAt ctx rfl) geometry =
      GoldHistorySourceTable.table ctx.parameters (origin.primitiveAt ctx rfl) (origin.capacityAt ctx rfl)
        dummy context root history radius geometry := by
  unfold cube GoldHistorySourceTable.table GoldCommonSourceTable.table GoldCommonSourceTable.cube
  rw [rectangular_eq_analysis ctx origin dummy context root history radius small]

/-- An actual original batch opening uses the complete-history executable
public cube. Digest/root association and exact snapshot selection are derived
from preparation, parsing and recovery, not provided as equalities. -/
theorem batch_source_eq_public (dummy : Digest) (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (world : InputIndexedOracle.World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (OracleProgram.run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (framed : NativeGoldBatchSourceRisk.Framed ctx)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (history : List Observation) (sourceLog : Log)
    (recovered : NativeGoldBatchFirstFieldSource.recover dummy history decoded.field = some sourceLog)
    (radius : ℕ) (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1) :
    BatchOpeningNativeObligation.source dummy ctx (origin.primitiveAt ctx rfl) (origin.capacityAt ctx rfl)
        world work prepared decoded radius sourceLog =
      cube ctx dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.parameters)) ctx.root history radius
        (origin.capacityAt ctx rfl) (BatchOpeningNativeObligation.dimensions ctx world work prepared) := by
  exact (GoldHistorySourceTable.batch_table dummy ctx _ _ world work prepared framed responseFits decoded parsed
    history sourceLog recovered radius).trans
    (cube_eq_analysis ctx origin dummy _ _ history radius small _).symm

/-- The executable cube also remains fixed after the source key is recorded;
later hashes cannot silently switch to a newer public extraction snapshot. -/
theorem cube_append (ctx : Context) (origin : CacheBackedCodeOrigin.Origin ctx)
    (dummy context root : Digest) (before after : List Observation) (radius : ℕ)
    (small : 3*radius < ctx.parameters.code.blocks.val-ctx.parameters.code.messageBlocks.val+1)
    (geometry : GoldHistorySourceTable.Geometry ctx.parameters)
    (height : NativeMerkleShapeFamily.Height) (sourceLog : Log)
    (present : ⟨(context,height),⟨root,sourceLog⟩⟩ ∈
      (NativeGoldBatchFamilyAvailability.reconstructed dummy before).checkpoints.checkpoints) :
    cube ctx dummy context root (before++after) radius (origin.capacityAt ctx rfl) geometry =
      cube ctx dummy context root before radius (origin.capacityAt ctx rfl) geometry := by
  rw [cube_eq_analysis ctx origin dummy context root (before++after) radius small geometry,
    cube_eq_analysis ctx origin dummy context root before radius small geometry]
  exact GoldHistorySourceTable.table_append ctx.parameters _ _ dummy context root before after radius geometry height sourceLog present

end
end FormalProof4FHE.HasteBoots.GoldHistoryPublicExtraction
