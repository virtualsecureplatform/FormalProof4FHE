module
public import FormalProof4FHE.HasteBoots.ObservedGoldFieldExtraction
@[expose] public section

/-! The strict raw field parser identifies the complete field emitted by an
actual prepared native batch: context, root, original ordered queries/values,
and derived count. Full receipt dispatch and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldNativeFieldAssociation
open InputIndexedOracle (Input Byte World)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context Prepared)
open OracleProgram (run)
noncomputable section

theorem extraction_parsed_view (history : List Observation) (input : Input) (dummy : Vector Byte 64)
    (ctx : Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history input dummy ctx radius).value = some output)
    (field : NativeGoldBatchFieldInputView.View) (parsed : NativeGoldBatchFieldInputView.parse input = some field) :
    StoredGoldBatchFieldInputCost.view output.1 = field := by
  obtain ⟨checked,result,_,recovered,same,_,_⟩ := ObservedGoldFieldExtraction.run_sound history input dummy ctx radius output accepted
  have raw := StoredGoldFieldSourceRecovery.run_parsed history input result recovered
  rw [same] at raw
  have semantic := StoredGoldBatchFieldInputCost.parse_value input
  rw [raw,Option.map_some,parsed] at semantic
  exact Option.some.inj semantic

theorem prepared_random_positive (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    0 < work.geometry.randomCount.val := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_⟩ := NativeGoldBatchColumns.columns_log NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨built,_,_,_⟩ := NativeGoldBatchPrelude.sampling_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude
  have spec := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters geometry built
  rw [spec.computed]
  change 0 < 2^ctx.parameters.leftVariables.val * ctx.parameters.width.val * ctx.parameters.width.val
  have widthPositive : 0 < ctx.parameters.width.val := Nat.pos_of_ne_zero spec.basic.1
  exact Nat.mul_pos (Nat.mul_pos (by positivity) widthPositive) widthPositive

theorem prepared_field (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List TranscriptFrame.Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit) :
    ∃ context : NativeRootMessage.Digest,
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      NativeGoldBatchFieldInputView.parse (NativeGoldBatchReadExposure.phase ctx work).pending.input =
        some ⟨before,⟨context,ctx.root,ctx.queries,ctx.values⟩,work.geometry.randomCount⟩ := by
  obtain ⟨context,hashed,binding,_⟩ := NativeGoldBatchReadExposure.prepared_read ctx world work executed
  obtain ⟨other,otherHash,framed,_⟩ := NativeGoldBatchReadExposure.prepared_exposure ctx world work executed before parent valid fits
  have same := Option.some.inj (otherHash.symm.trans hashed)
  subst other
  have bound := NativeGoldBatchPcsProgram.prepared_binding ctx world work executed
  rw [bound.1,bound.2.2.1,bound.2.2.2] at framed
  let field : NativeGoldBatchFieldInputView.View := ⟨before,⟨context,ctx.root,ctx.queries,ctx.values⟩,work.geometry.randomCount⟩
  refine ⟨context,hashed,?_⟩
  rw [NativeGoldBatchReadExposure.phase_input ctx work context before parent binding]
  change NativeGoldBatchFieldInputView.parse (TranscriptFrame.encodeMany field.frames) = some field
  rw [← NativeGoldBatchFieldInputView.phase_input field ctx.parent.profile]
  exact NativeGoldBatchFieldInputView.parse_native field ctx.parent.profile
    (prepared_random_positive ctx world work executed) framed

theorem extraction_prepared_field (native : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram native) world).run.1 = .prepared work)
    (before : List TranscriptFrame.Frame) (parent : native.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode native.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode native.values).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history (NativeGoldBatchReadExposure.phase native work).pending.input dummy ctx radius).value = some output) :
    ∃ context : NativeRootMessage.Digest,
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row native.parameters) world).run.1 = some context ∧
      output.1.data.source.1.get = context ∧ output.1.data.source.2.get = native.root ∧
      output.1.data.queries = native.queries ∧ output.1.data.values = native.values ∧
      output.1.count = work.geometry.randomCount := by
  obtain ⟨context,hashed,parsed⟩ := prepared_field native world work executed before parent valid fits
  have same := extraction_parsed_view history _ dummy ctx radius output accepted _ parsed
  refine ⟨context,hashed,?_,?_,?_,?_,?_⟩
  · exact congrArg (fun field => field.data.context) same
  · exact congrArg (fun field => field.data.root) same
  · exact congrArg (fun field => field.data.queries) same
  · exact congrArg (fun field => field.data.values) same
  · exact congrArg NativeGoldBatchFieldInputView.View.count same

/-- A dispatcher-provided native context/root relation determines the stored
field key; callers do not supply equality of the parsed raw key. -/
theorem extraction_prepared_key (native : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram native) world).run.1 = .prepared work)
    (before : List TranscriptFrame.Frame) (parent : native.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode native.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode native.values).length < TranscriptFrame.lengthLimit)
    (history : List Observation) (dummy : Vector Byte 64) (ctx : Context) (radius : ℕ) (output)
    (accepted : (ObservedGoldFieldExtraction.run history (NativeGoldBatchReadExposure.phase native work).pending.input dummy ctx radius).value = some output)
    (source : StoredSourceVectorReadCost.Source)
    (contextReturned : (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row native.parameters) world).run.1 = some source.1.get)
    (root : native.root = source.2.get) : output.1.data.source = source := by
  obtain ⟨context,hashed,contextEq,rootEq,_,_,_⟩ := extraction_prepared_field native world work executed before parent valid fits
    history dummy ctx radius output accepted
  apply StoredMetadataCost.sourceView_injective
  apply Prod.ext
  · exact contextEq.trans (Option.some.inj (hashed.symm.trans contextReturned))
  · exact rootEq.trans root

end
end FormalProof4FHE.HasteBoots.StoredGoldNativeFieldAssociation
