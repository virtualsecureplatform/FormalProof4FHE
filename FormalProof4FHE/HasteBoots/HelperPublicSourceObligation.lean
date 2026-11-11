module
public import FormalProof4FHE.HasteBoots.HelperPublicSource
public import FormalProof4FHE.HasteBoots.RegistryPublicSourceObligation
@[expose] public section

/-! Wrong helper sum coefficients on the original allocated public cube
produce the native single-opening falsity obligation. The helper packing
width remains independent of the source/lookup guard width. -/
namespace FormalProof4FHE.HasteBoots.HelperPublicSourceObligation
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def coefficients (parameters : Parameters Stored) (value : NativeFieldWire.GoldExtension) :=
  NativeHelperPacking.coefficients NativeExtensionFields.goldilocksBasis parameters.width.val (NativeFieldWire.goldExtensionValue value)

theorem coefficients_heq {first second : Parameters Stored} (parameters : first = second)
    (value : NativeFieldWire.GoldExtension) : HEq (coefficients first value) (coefficients second value) := by
  cases parameters
  rfl

theorem query_read (candidate : Context) (reference : NativeGoldBatchPcsProgram.Context)
    (parameters : candidate.parameters = reference.parameters) (world : World) (work : Prepared)
    (prepared : (run candidate.prefix world).run.1 = .prepared work) (raw : NativeGoldPcsWire.Query) (same : candidate.query = raw) :
    NativeGoldCoefficientsQuery.interpret reference.parameters.width.val reference.parameters.numVariables.val ⟨raw.models,none⟩ =
      some (RegistryPublicSourceObligation.query parameters (SingleOpeningNativeObligation.query candidate world work prepared)) := by
  have read := SingleOpeningNativeObligation.query_read candidate world work prepared
  rw [same] at read
  exact RegistryPublicSourceObligation.read_transport parameters _ _ read

theorem wrong (candidate : Context) (reference : NativeGoldBatchPcsProgram.Context)
    (candidateOrigin : CacheBackedSingleOpening.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (parameters : candidate.parameters = reference.parameters) (world : World) (work : Prepared)
    (prepared : (run candidate.prefix world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) (sizes : GoldHistorySourceTable.Geometry reference.parameters)
    (compatible : HelperPublicSource.Compatible candidate reference candidateOrigin referenceOrigin world work prepared dummy history sizes)
    (radius : ℕ) (small : 3*radius < reference.parameters.code.blocks.val-reference.parameters.code.messageBlocks.val+1)
    (framed : SingleOpeningAvailability.Framed candidate)
    (responseFits : (SingleOpeningColumnLaw.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (sample : NativeIndexRequest.Result) (sampler : SingleOpeningSamplingReceipt.Receipt candidate world work sample)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded)
    (value : NativeFieldWire.GoldExtension)
    (mismatch : coefficients reference.parameters value ≠
      (RegistryPublicSourceObligation.query parameters (SingleOpeningNativeObligation.query candidate world work prepared)).query.fold
        (GoldHistoryPublicExtraction.cube reference dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters))
          reference.root history radius (referenceOrigin.capacityAt reference rfl) sizes)) :
    SingleOpeningNativeObligation.Wrong dummy candidate candidateOrigin world work prepared decoded history radius (coefficients candidate.parameters value) := by
  intro sourceLog recovered
  exact RegistryPublicSourceObligation.fold_mismatch parameters _ _ _ _ _ _ (RegistryPublicSourceObligation.query_heq parameters _)
    (compatible radius small framed responseFits sample sampler decoded parsed sourceLog recovered) (coefficients_heq parameters value) mismatch

/-- The checked-helper receipt supplies the encoded coefficients. This theorem
converts the public-cube mismatch to the exact native causal false claim. -/
theorem false_claim (candidate : Context) (reference : NativeGoldBatchPcsProgram.Context)
    (candidateOrigin : CacheBackedSingleOpening.Origin candidate) (referenceOrigin : CacheBackedCodeOrigin.Origin reference)
    (parameters : candidate.parameters = reference.parameters) (world : World) (work : Prepared)
    (prepared : (run candidate.prefix world).run.1 = .prepared work)
    (dummy : Digest) (history : List Observation) (sizes : GoldHistorySourceTable.Geometry reference.parameters)
    (compatible : HelperPublicSource.Compatible candidate reference candidateOrigin referenceOrigin world work prepared dummy history sizes)
    (radius : ℕ) (small : 3*radius < reference.parameters.code.blocks.val-reference.parameters.code.messageBlocks.val+1)
    (framed : SingleOpeningAvailability.Framed candidate)
    (responseFits : (SingleOpeningColumnLaw.payload candidate.opening).length < TranscriptFrame.lengthLimit)
    (sample : NativeIndexRequest.Result) (sampler : SingleOpeningSamplingReceipt.Receipt candidate world work sample)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input sampler world) = some decoded)
    (value : NativeFieldWire.GoldExtension)
    (encoded : candidate.claimed.val.map NativeFieldRepresentation.goldValue = List.ofFn (coefficients candidate.parameters value))
    (mismatch : coefficients reference.parameters value ≠
      (RegistryPublicSourceObligation.query parameters (SingleOpeningNativeObligation.query candidate world work prepared)).query.fold
        (GoldHistoryPublicExtraction.cube reference dummy (InputIndexedOracle.sha512 world (GoldContextInput.bytes reference.parameters))
          reference.root history radius (referenceOrigin.capacityAt reference rfl) sizes)) :
    SingleOpeningCausalCoverage.FalseClaim dummy candidate candidateOrigin decoded history radius := by
  apply (SingleOpeningNativeObligation.false_claim_iff sampler prepared framed responseFits dummy candidateOrigin decoded parsed history radius _ encoded).mpr
  exact wrong candidate reference candidateOrigin referenceOrigin parameters world work prepared dummy history sizes compatible radius small
    framed responseFits sample sampler decoded parsed value mismatch

end
end FormalProof4FHE.HasteBoots.HelperPublicSourceObligation
