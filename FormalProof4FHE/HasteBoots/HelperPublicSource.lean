module
public import FormalProof4FHE.HasteBoots.AllocatedHelperContext
public import FormalProof4FHE.HasteBoots.AllocatedCodeOrigin
public import FormalProof4FHE.HasteBoots.GoldHistoryPublicExtraction
@[expose] public section

/-! Original allocated helper parameters and original proof root determine
one executable public cube. The batch context is an extraction adapter only;
its empty call payload is never run as a batch verification. -/
namespace FormalProof4FHE.HasteBoots.HelperPublicSource
open NativeGoldParameterStore (Entry)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeRootFamilySourceSelection (Log)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def context {B : Type} (ctx : NativeGoldHelperVerification.Context B) (entry : Entry) (root : Digest) :
    NativeGoldBatchPcsProgram.Context :=
  ⟨ctx.tables,entry.initialized.parameters,ctx.parent,root,⟨[],by decide⟩,⟨[],by decide⟩,
    ⟨⟨[],by decide⟩,⟨[],by decide⟩,⟨[],by decide⟩⟩,ctx.fieldFuel⟩

def origin {B : Type} (ctx : NativeGoldHelperVerification.Context B) (entry : Entry)
    (good : NativeGoldParameterStore.GoodEntry entry) (root : Digest) : CacheBackedCodeOrigin.Origin (context ctx entry root) :=
  AllocatedCodeOrigin.ofInitialization entry.header entry.request entry.config good.1 entry.initialized good.2 (context ctx entry root) rfl

theorem origin_data {B : Type} (ctx : NativeGoldHelperVerification.Context B) (entry : Entry)
    (good : NativeGoldParameterStore.GoodEntry entry) (root : Digest) :
    (origin ctx entry good root).request = entry.request ∧ (origin ctx entry good root).config = entry.config := ⟨rfl,rfl⟩

theorem geometry (candidate : NativeGoldPcsExecution.Context) (reference : NativeGoldBatchPcsProgram.Context)
    (parameters : candidate.parameters = reference.parameters) (world : World) (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (run candidate.prefix world).run.1 = .prepared work) : GoldHistorySourceTable.Geometry reference.parameters :=
  parameters ▸ SingleOpeningExtractedTableMeaning.prepared_dimensions candidate world work prepared

def Compatible (candidate : NativeGoldPcsExecution.Context) (reference : NativeGoldBatchPcsProgram.Context)
    (candidateOrigin : CacheBackedSingleOpening.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (world : World) (work : NativeGoldPcsWorkers.Prepared)
    (prepared : (run candidate.prefix world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) (sizes : GoldHistorySourceTable.Geometry reference.parameters) : Prop :=
  ∀ (radius : ℕ), 3*radius < reference.parameters.code.blocks.val-reference.parameters.code.messageBlocks.val+1 →
    ∀ (_ : SingleOpeningAvailability.Framed candidate)
      (_ : (SingleOpeningColumnLaw.payload candidate.opening).length < TranscriptFrame.lengthLimit)
      (sample : NativeIndexRequest.Result) (sampler : SingleOpeningSamplingReceipt.Receipt candidate world work sample)
      (decoded : SingleOpeningChallengeLink.View),
      SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded →
      ∀ (sourceLog : Log), SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog →
        HEq (SingleOpeningNativeObligation.source dummy candidate candidateOrigin world work prepared decoded sourceLog radius)
          (GoldHistoryPublicExtraction.cube reference dummy
            (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters)) reference.root history radius
            (referenceOrigin.capacityAt reference rfl) sizes)

theorem compatible (candidate : NativeGoldPcsExecution.Context) (reference : NativeGoldBatchPcsProgram.Context)
    (candidateOrigin : CacheBackedSingleOpening.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (parameters : candidate.parameters = reference.parameters) (root : candidate.root = reference.root)
    (world : World) (work : NativeGoldPcsWorkers.Prepared) (prepared : (run candidate.prefix world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) :
    Compatible candidate reference candidateOrigin referenceOrigin world work prepared dummy history
      (geometry candidate reference parameters world work prepared) := by
  intro radius small framed responseFits sample sampler decoded parsed sourceLog recovered
  have native := GoldHistorySourceTable.single_table dummy candidateOrigin sampler prepared framed responseFits decoded parsed history sourceLog recovered radius
  apply HEq.trans (heq_of_eq native)
  have referenceTable := GoldHistoryPublicExtraction.cube_eq_analysis reference referenceOrigin dummy
    (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters)) reference.root history radius small
    (geometry candidate reference parameters world work prepared)
  rw [referenceTable]
  unfold GoldHistorySourceTable.table
  have digest := congrArg (fun p => InputIndexedOracle.sha512 world (GoldContextInput.bytes p)) parameters
  rw [digest,root]
  exact GoldCommonSourceTable.table_congr parameters candidateOrigin.primitive (referenceOrigin.primitiveAt reference rfl)
    candidateOrigin.capacity (referenceOrigin.capacityAt reference rfl) dummy _ _ _ radius _ _

end
end FormalProof4FHE.HasteBoots.HelperPublicSource
