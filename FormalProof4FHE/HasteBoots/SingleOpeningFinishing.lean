module
public import FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
public import FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks
public import FormalProof4FHE.HasteBoots.NativeGoldSuffixFinishing
@[expose] public section

/-! Finishing of the actual single-opening PCS call. The original response and
its computed encoding are recovered from the checked prefix. Packing width and
code-symbol width are independent. This does not replace a single call with a
batch call or establish the production Fiat--Shamir probability bound. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFinishing
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (Tables Stored encoding logSize description)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

/-- Original raw response encodings and query facts derived from preparation.
This record is analysis output, not a verifier argument. -/
structure Encoding (ctx : Context) (work : Prepared) where
  planRoot : NativeGoldSolinas.Word
  test : NativeGoldRowEncoding.encodeResponses (encoding ctx.parameters.code planRoot)
    ctx.parameters.width.val ctx.opening.test.val = some work.test
  evaluation : NativeGoldRowEncoding.encodeResponses (encoding ctx.parameters.code planRoot)
    ctx.parameters.width.val ctx.opening.evaluation.val = some work.evaluation
  size : ctx.query.models.length = ctx.parameters.numVariables.val
  shape : (encoding ctx.parameters.code planRoot).messageLength =
    2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)
  valid : NativeGoldMatrixWeights.QueryValid ctx.parameters.width.val ctx.query.models

/-- Every field is recovered from the original prepared execution. -/
theorem prepared_encoding (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) : Nonempty (Encoding ctx work) := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
      ctx.opening ctx.fieldFuel world work prepared
  have original := NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry state weights sample planRoot test evaluation encoded
  obtain ⟨next,prior,_,_,_⟩ := NativeGoldPcsColumns.columns_origin description ctx.parameters ctx.transcript ctx.root ctx.query
    ctx.claimed ctx.opening ctx.fieldFuel world geometry state weights sample original.1
  obtain ⟨built,_,bound,boundRead,_⟩ := NativeGoldPcsPrelude.sampling_origin description ctx.parameters ctx.transcript ctx.root
    ctx.query ctx.claimed ctx.opening ctx.fieldFuel world geometry (.finished state next) prior
  have checked := NativeGoldPcsBinding.bound_check description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed world bound boundRead
  have models := NativeGoldPcsColumnsShape.binding_models ctx.parameters ctx.query ctx.claimed checked
  exact ⟨⟨planRoot,original.2.2.1,original.2.2.2,models.1,
    (NativeBrakedownParameters.build_spec description ctx.parameters geometry built).code.1,models.2⟩⟩

/-- Finishing is expressed in the domain of the retained original code, using
its padded message capacity and the actual computed evaluation response. -/
def FinishesAs (ctx : Context) (work : Prepared)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (capacity : ctx.parameters.code.messageLength.val ≤
      ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (values : List NativeFields.Goldilocks) : Prop :=
  ∃ data : Encoding ctx work,
    values = List.ofFn (RectangularMatrixResponse.finishEncoded
      (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) primitive)
      capacity (NativeGoldSuffixFinishing.encodedRight ctx.parameters ctx.query
        (encoding ctx.parameters.code data.planRoot) data.size data.shape)
      (fun lane => NativeGoldResponseMeaning.laneWord (encoding ctx.parameters.code data.planRoot) work.evaluation lane.val))

/-- The original received claim is retained in the native call. -/
abbrev Finishes (ctx : Context) (work : Prepared)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (capacity : ctx.parameters.code.messageLength.val ≤
      ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val) : Prop :=
  FinishesAs ctx work primitive capacity (ctx.claimed.val.map goldValue)

/-- Transport only the field interpretation of the claim. Original packet
words, root, query and transcript are unchanged. -/
theorem finishes_as (ctx : Context) (work : Prepared)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (capacity : ctx.parameters.code.messageLength.val ≤
      ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (finished : Finishes ctx work primitive capacity) (values : List NativeFields.Goldilocks)
    (same : values = ctx.claimed.val.map goldValue) : FinishesAs ctx work primitive capacity values := by
  obtain ⟨data,claimed⟩ := finished
  exact ⟨data,same.trans claimed⟩

/-- Computed native acceptance enforces finishing; no query-shape, encoding or
claim-success certificate is supplied separately. -/
theorem accepted_finishes {Memory : Type} (ctx : Context) (choose : NativeGoldPcsProgram.Scheduler Memory)
    (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (constructorTables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1))) :
    Finishes ctx work primitive
      (NativeGoldBlockCodeMeaning.constructor_dimensions constructorTables message block blowup ctx.parameters.code constructed).2.2.1 := by
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨data⟩ := prepared_encoding ctx world work prepared
  have checked := (NativeGoldPcsProgram.accepted_flags ctx choose fuel memory world work completion executed parent accepted).2.1
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions constructorTables message block blowup ctx.parameters.code constructed
  exact ⟨data,NativeGoldSuffixFinishing.claim_encoded ctx.parameters ctx.query ctx.opening.evaluation.val work.evaluation ctx.claimed
    data.valid checked (encoding ctx.parameters.code data.planRoot) ctx.parameters.code.messageBlocks.val data.evaluation
    (Nat.le_of_lt dimensions.2.1) dimensions.2.2.1 primitive data.size data.shape⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningFinishing
