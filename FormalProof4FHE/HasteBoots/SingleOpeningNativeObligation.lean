module
public import FormalProof4FHE.HasteBoots.QueryNativeInterpretationComplete
public import FormalProof4FHE.HasteBoots.SingleOpeningExtractedTableMeaning
@[expose] public section

/-! A false abstract obligation on the same extracted source is exactly the
actual parsed native false claim. Query interpretation, public dimensions and
nonce/claim association are all derived from the original prepared call. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningNativeObligation
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeRootMessage (Digest)
open NativeFields (Goldilocks)
open SingleOpeningChallengeLink (View)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

/-- The unique successful deterministic interpretation of the original query. -/
def query (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :=
  Classical.choose (QueryNativeInterpretationComplete.prepared ctx world work prepared)

theorem query_read (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) :
    NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val ⟨ctx.query.models,none⟩ =
      some (query ctx world work prepared) :=
  Classical.choose_spec (QueryNativeInterpretationComplete.prepared ctx world work prepared)

theorem query_unique (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (value : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val ctx.parameters.numVariables.val)
    (read : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val ⟨ctx.query.models,none⟩ = some value) :
    query ctx world work prepared = value := Option.some.inj ((query_read ctx world work prepared).symm.trans read)

/-- Reindexes the same common-source extractor table, using dimensions derived
from actual preparation. No new source, decoder or opening query is selected. -/
def source (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (world : World) (work : Prepared) (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (decoded : View) (sourceLog : SingleOpeningExtractedTableMeaning.Log) (radius : ℕ) :=
  let dimensions := SingleOpeningExtractedTableMeaning.prepared_dimensions ctx world work prepared
  QueryReindex.source dimensions.1 (SingleOpeningExtractedTableMeaning.cube dummy ctx origin decoded sourceLog radius
    (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) dimensions.2)

def Wrong (dummy : Digest) (ctx : Context) (origin : CacheBackedSingleOpening.Origin ctx)
    (world : World) (work : Prepared) (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (decoded : View) (history : List NativeTranscript.Observation) (radius : ℕ)
    (expected : Fin ctx.parameters.width.val → Goldilocks) : Prop :=
  ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy history decoded.field = some sourceLog →
    expected ≠ (query ctx world work prepared).query.fold (source dummy ctx origin world work prepared decoded sourceLog radius)

theorem false_claim_iff {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (framed : SingleOpeningAvailability.Framed ctx)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (dummy : Digest) (origin : CacheBackedSingleOpening.Origin ctx) (decoded : View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (history : List NativeTranscript.Observation) (radius : ℕ) (expected : Fin ctx.parameters.width.val → Goldilocks)
    (encoded : ctx.claimed.val.map NativeFieldRepresentation.goldValue = List.ofFn expected) :
    SingleOpeningCausalCoverage.FalseClaim dummy ctx origin decoded history radius ↔
      Wrong dummy ctx origin world work prepared decoded history radius expected := by
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨_,_,_,_,_,_,_,queryEq,claimEq,_,_,_,_⟩ := SingleOpeningPreparedChallenge.parsed_origin
    receipt prepared before parent valid fits responseFits decoded parsed
  have actualRead : NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val
      ⟨decoded.field.data.query.models,none⟩ = some (query ctx world work prepared) := by
    rw [queryEq]
    exact query_read ctx world work prepared
  have actualClaim : SingleOpeningFixedResponseData.claimed ctx decoded.field.data.claimed = expected := by
    rw [claimEq]
    exact SingleOpeningExtractedTableMeaning.claimed_of_encoded ctx ctx.claimed expected encoded
  have equivalent := SingleOpeningExtractedTableMeaning.prepared_false_claim_iff dummy ctx origin world work prepared
    decoded history radius (query ctx world work prepared) actualRead
  simpa only [actualClaim,Wrong,source] using equivalent

end
end FormalProof4FHE.HasteBoots.SingleOpeningNativeObligation
