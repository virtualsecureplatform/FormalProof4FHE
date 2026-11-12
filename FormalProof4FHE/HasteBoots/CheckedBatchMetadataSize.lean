module
public import FormalProof4FHE.HasteBoots.SourceClaimGroupCardinality
@[expose] public section

/-! Actual checked singleton batches have bounded metadata on admitted
Goldilocks widths. The singleton condition is later supplied by the source
collector's canonical-group invariant, not an adversarial count cutoff. -/
namespace FormalProof4FHE.HasteBoots.CheckedBatchMetadataSize
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativePrefixCodec (Vector)
open NativeBrakedownContext (Parameters)
open OracleProgram (run)
open InputIndexedOracle (World)

theorem bodies_length {C : Type} (parameters : Parameters C) (queries : List Query) (values : List Row)
    (width : parameters.width.val ≤ 4) (numVars : parameters.numVariables.val < 64)
    (checked : List.Forall₂ (fun query value => NativeGoldPcsBinding.check parameters query value = true) queries values) :
    (queries.flatMap NativeGoldPcsWire.queryCodec.encode).length ≤ 20421*queries.length ∧
      (values.flatMap NativeLookupRequestWire.rowCodec.encode).length ≤ 45*values.length := by
  induction checked with
  | nil => exact ⟨by simp,by simp⟩
  | @cons query value queries values first tail ih =>
    obtain ⟨count,size,matrices⟩ := (NativeGoldPcsBinding.check_iff parameters query value).mp first
    have querySize := CheckedPcsMetadataSize.query_length query parameters.width.val width matrices
    have valueSize := CheckedPcsMetadataSize.row_length value
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
    constructor <;> omega

theorem metadata_length {C : Type} (parameters : Parameters C) (queries : Vector Query) (values : Vector Row)
    (width : parameters.width.val ≤ 4) (numVars : parameters.numVariables.val < 64)
    (singleton : queries.val.length ≤ 1) (checked : NativeGoldBatchBinding.check parameters queries values = true) :
    128+(NativeGoldBatchBinding.queriesCodec.encode queries).length+
      (NativeGoldBatchBinding.valuesCodec.encode values).length ≤ 20612 := by
  obtain ⟨_,count,paired⟩ := (NativeGoldBatchBinding.check_iff parameters queries values).mp checked
  have bodies := bodies_length parameters queries.val values.val width numVars paired
  have queryHeader := NativeUsizeMessage.encode_length (⟨queries.val.length,queries.property⟩ : NativeUsizeMessage.Usize)
  have valueHeader := NativeUsizeMessage.encode_length (⟨values.val.length,values.property⟩ : NativeUsizeMessage.Usize)
  change 128+(NativeUsizeMessage.encode ⟨queries.val.length,queries.property⟩ ++ queries.val.flatMap NativeGoldPcsWire.queryCodec.encode).length+
    (NativeUsizeMessage.encode ⟨values.val.length,values.property⟩ ++ values.val.flatMap NativeLookupRequestWire.rowCodec.encode).length ≤ _
  simp only [List.length_append]
  omega

theorem completed_checks {Memory : Type} (ctx : NativeGoldBatchPcsProgram.Context)
    (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : NativeGoldBatchPcsProgram.Prepared) (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion) :
    ctx.parameters.numVariables.val < 64 ∧ NativeGoldBatchBinding.check ctx.parameters ctx.queries ctx.values = true := by
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨geometry,binding,state,weights,sample,_,_,_,_,prior,_,_,_,_,_⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work prepared
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨built,bound,_,_⟩ := NativeGoldBatchPrelude.sampling_origin NativeGoldBlockCode.description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude
  exact ⟨(NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters geometry built).basic.2.2.1,
    (NativeGoldBatchBinding.bound_origin NativeGoldBlockCode.description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound).1⟩

theorem completed_fits {Memory : Type} (ctx : NativeGoldBatchPcsProgram.Context)
    (choose : NativeGoldBatchPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : NativeGoldBatchPcsProgram.Prepared) (completion : NativeGoldBatchPcsProgram.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (width : ctx.parameters.width.val ≤ 4) (singleton : ctx.queries.val.length ≤ 1) :
    128+(NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length+
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit := by
  have checked := completed_checks ctx choose fuel memory world work completion executed
  exact lt_of_le_of_lt (metadata_length ctx.parameters ctx.queries ctx.values width checked.1 singleton checked.2)
    (by decide +kernel : 20612 < TranscriptFrame.lengthLimit)

end FormalProof4FHE.HasteBoots.CheckedBatchMetadataSize
