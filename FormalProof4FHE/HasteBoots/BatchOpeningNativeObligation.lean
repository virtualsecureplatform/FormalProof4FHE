module
public import FormalProof4FHE.HasteBoots.QueryNativeInterpretationComplete
public import FormalProof4FHE.HasteBoots.SingleOpeningExtractedTableMeaning
public import FormalProof4FHE.HasteBoots.NativeGoldBatchCausalCoverage
@[expose] public section

/-! Original batch queries fold one common extracted cube. Query decoding,
split dimensions and parsed binding association come from actual preparation.
The original query index is retained even when left-response groups coincide. -/
namespace FormalProof4FHE.HasteBoots.BatchOpeningNativeObligation
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchRectangularData (Query)
open NativeRootMessage (Digest)
open NativeFields (Goldilocks)
open NativeGoldBatchChallengeLink (View)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem query_exists (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (index : Query work) :
    ∃ value : ExtensionQuery.Broadcast Goldilocks ctx.parameters.width.val ctx.parameters.numVariables.val,
      NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val
        ⟨(work.binding.queries.val.get index).models,none⟩ = some value :=
  QueryNativeInterpretationComplete.query _ _ _ (NativeGoldBatchPcsProgram.prepared_query_valid ctx world work prepared index)
    (NativeGoldBatchFinishingMeaning.prepared_query_length ctx world work prepared index)

def query (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (index : Query work) :=
  Classical.choose (query_exists ctx world work prepared index)

theorem query_read (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) (index : Query work) :
    NativeGoldCoefficientsQuery.interpret ctx.parameters.width.val ctx.parameters.numVariables.val
      ⟨(work.binding.queries.val.get index).models,none⟩ = some (query ctx world work prepared index) :=
  Classical.choose_spec (query_exists ctx world work prepared index)

theorem dimensions (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ctx.parameters.numVariables.val = ctx.parameters.leftVariables.val + (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) ∧
    ctx.parameters.code.messageLength.val = 2^(ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) := by
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  exact ⟨by have bound := geometry.basic.2.1; omega,geometry.code.1⟩

variable (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (decoded : View) (history : List NativeTranscript.Observation) (radius : ℕ)

def rectangular (sourceLog : NativeRootFamilySourceSelection.Log) :=
  RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius
    (NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog)

def source (sourceLog : NativeRootFamilySourceSelection.Log) :=
  let sizes := dimensions ctx world work prepared
  QueryReindex.source sizes.1 (QueryRectangularNativeMeaning.source ctx.parameters
    (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) sizes.2 (rectangular dummy ctx primitive capacity decoded radius sourceLog))

def Wrong : Prop :=
  ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy history decoded.field = some sourceLog →
    ∃ index : Query work,
      (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed work.binding.values index.val lane.val) ≠
        (query ctx world work prepared index).query.fold (source dummy ctx primitive capacity world work prepared decoded radius sourceLog)

def WrongAt (index : Query work) (expected : Fin ctx.parameters.width.val → Goldilocks) : Prop :=
  ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy history decoded.field = some sourceLog →
    expected ≠ (query ctx world work prepared index).query.fold (source dummy ctx primitive capacity world work prepared decoded radius sourceLog)

theorem fold_source (sourceLog : NativeRootFamilySourceSelection.Log) (index : Query work) :
    (query ctx world work prepared index).query.fold (source dummy ctx primitive capacity world work prepared decoded radius sourceLog) =
      matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters work.binding.queries index.val)
        (NativeGoldBatchFixedResponseData.rightAt ctx.parameters work.binding.queries index.val)
        (rectangular dummy ctx primitive capacity decoded radius sourceLog) := by
  let sizes := dimensions ctx world work prepared
  have transport := QueryRectangularNativeMeaning.fold_source_arity ctx.parameters (work.binding.queries.val.get index)
    (ctx.parameters.numVariables.val - ctx.parameters.leftVariables.val) (query ctx world work prepared index)
    (query_read ctx world work prepared index) sizes.2 sizes.1 (rectangular dummy ctx primitive capacity decoded radius sourceLog)
  have leftSame : SingleOpeningFixedResponseData.left ctx.parameters (work.binding.queries.val.get index) =
      NativeGoldBatchFixedResponseData.left ctx.parameters (work.binding.queries.val.get index) := by rfl
  have rightSame : SingleOpeningFixedResponseData.right ctx.parameters (work.binding.queries.val.get index) =
      NativeGoldBatchFixedResponseData.right ctx.parameters (work.binding.queries.val.get index) := by rfl
  rw [leftSame,rightSame] at transport
  simpa only [source,NativeGoldBatchFixedResponseData.leftAt,NativeGoldBatchFixedResponseData.rightAt,
    NativeGoldBatchFixedResponseData.queryAt_get] using transport

theorem false_claim_iff
    (framed : NativeGoldBatchSourceRisk.Framed ctx)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    NativeGoldBatchCausalCoverage.FalseClaim dummy ctx primitive work decoded history capacity radius ↔
      Wrong dummy ctx primitive capacity world work prepared decoded history radius := by
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨_,_,_,_,_,_,_,queries,values,_,_,_,_⟩ := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared
    before parent valid fits responseFits decoded parsed
  have binding := NativeGoldBatchPcsProgram.prepared_binding ctx world work prepared
  have queriesEq := queries.trans binding.2.2.1.symm
  have valuesEq := values.trans binding.2.2.2.symm
  unfold NativeGoldBatchCausalCoverage.FalseClaim Wrong
  rw [queriesEq,valuesEq]
  apply forall_congr'
  intro sourceLog
  apply forall_congr'
  intro recovered
  apply exists_congr
  intro index
  rw [fold_source dummy ctx primitive capacity world work prepared decoded radius sourceLog index]
  rfl

end
noncomputable section

/-- The indexed original raw row has the established field-vector meaning,
without canonicalizing its bytes or changing its batch position. -/
theorem claimed_of_encoded (width : ℕ) (values : NativePrefixCodec.Vector NativeLookupRequestWire.Row)
    (index : ℕ) (row : NativeLookupRequestWire.Row) (found : values.val[index]? = some row)
    (expected : Fin width → Goldilocks) (encoded : row.val.map NativeFieldRepresentation.goldValue = List.ofFn expected) :
    (fun lane : Fin width => NativeGoldBatchFixedResponseData.claimed values index lane.val) = expected := by
  funext lane
  have atLane := congrArg (fun words : List Goldilocks => (words[lane.val]?).getD (NativeFieldRepresentation.goldValue 0)) encoded
  simpa [NativeGoldBatchFixedResponseData.claimed,found,List.getElem?_map,Option.getD_map] using atLane

theorem wrong_of_at (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(NativeGoldBlockCode.logSize ctx.parameters.code+1)))
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (decoded : View) (history : List NativeTranscript.Observation) (radius : ℕ)
    (index : Query work) (row : NativeLookupRequestWire.Row) (found : work.binding.values.val[index.val]? = some row)
    (expected : Fin ctx.parameters.width.val → Goldilocks)
    (encoded : row.val.map NativeFieldRepresentation.goldValue = List.ofFn expected)
    (wrong : WrongAt dummy ctx primitive capacity world work prepared decoded history radius index expected) :
    Wrong dummy ctx primitive capacity world work prepared decoded history radius := by
  intro sourceLog recovered
  refine ⟨index,?_⟩
  rw [claimed_of_encoded ctx.parameters.width.val work.binding.values index.val row found expected encoded]
  exact wrong sourceLog recovered

/-- A successful native alias comparison transports field meaning only;
the actual inserted row and the received alias keep their original bytes. -/
theorem alias_encoded (width : ℕ) (row aliasRow : NativeLookupRequestWire.Row)
    (matched : NativeGoldPcsClaim.equal row.val aliasRow.val = true)
    (expected : Fin width → Goldilocks)
    (encoded : aliasRow.val.map NativeFieldRepresentation.goldValue = List.ofFn expected) :
    row.val.map NativeFieldRepresentation.goldValue = List.ofFn expected :=
  ((NativeGoldPcsClaim.equal_iff row.val aliasRow.val).mp matched).trans encoded

end
end FormalProof4FHE.HasteBoots.BatchOpeningNativeObligation
