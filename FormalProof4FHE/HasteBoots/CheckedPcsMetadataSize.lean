module
public import FormalProof4FHE.HasteBoots.ReceiptDerivedIdentityWork
public import FormalProof4FHE.HasteBoots.RowEncodingCost
@[expose] public section

/-! Successful native single-opening prefixes check their variable count
and literal matrices. Goldilocks admitted widths then give a fixed metadata
size bound, independent of root contents and received response sizes. -/
namespace FormalProof4FHE.HasteBoots.CheckedPcsMetadataSize
open NativeGoldPcsWire (Matrix Pair Query)
open NativeLookupRequestWire (Row)
open NativeBrakedownContext (Parameters)
open OracleProgram (run)
open InputIndexedOracle (World)

theorem row_length (row : Row) : (NativeLookupRequestWire.rowCodec.encode row).length ≤ 9*(row.val.length+1) := by
  simpa only [RowEncodingCost.encode_value] using RowEncodingCost.encode_length row

theorem flatMap_length_le {A : Type} (encode : A → InputIndexedOracle.Input) (values : List A) (budget : ℕ)
    (bounds : ∀ value ∈ values, (encode value).length ≤ budget) :
    (values.flatMap encode).length ≤ budget*values.length := by
  revert bounds
  induction values with
  | nil => intro _; simp
  | cons head tail ih =>
    intro bounds
    have first := bounds head (by simp)
    have later := ih (fun value member => bounds value (List.mem_cons_of_mem head member))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
    omega

theorem matrix_length (matrix : Matrix) (width : ℕ) (small : width ≤ 4)
    (checked : NativeGoldMatrix.validate matrix.model width = true) :
    (NativeGoldPcsWire.matrixCodec.encode matrix).length ≤ 162 := by
  have shape := (NativeGoldMatrix.validate_iff matrix.model width).mp checked
  have square : width*width ≤ 16 := Nat.mul_le_mul small small
  have row := row_length matrix.values
  have header := NativeUsizeMessage.encode_length matrix.width
  change (NativeUsizeMessage.encode matrix.width ++ NativeLookupRequestWire.rowCodec.encode matrix.values).length ≤ _
  rw [List.length_append]
  have dimensions : matrix.values.val.length = width*width := shape.2.2.2
  omega

theorem query_length (query : Query) (width : ℕ) (small : width ≤ 4)
    (checked : ∀ pair ∈ query.val, NativeGoldMatrix.validate pair.1.model width = true ∧
      NativeGoldMatrix.validate pair.2.model width = true) :
    (NativeGoldPcsWire.queryCodec.encode query).length ≤ 9+324*query.val.length := by
  have body := flatMap_length_le NativeGoldPcsWire.pairCodec.encode query.val 324 (by
    intro pair member
    have left := matrix_length pair.1 width small (checked pair member).1
    have right := matrix_length pair.2 width small (checked pair member).2
    change (NativeGoldPcsWire.matrixCodec.encode pair.1 ++ NativeGoldPcsWire.matrixCodec.encode pair.2).length ≤ _
    rw [List.length_append]
    omega)
  have header := NativeUsizeMessage.encode_length (⟨query.val.length,query.property⟩ : NativeUsizeMessage.Usize)
  change (NativeUsizeMessage.encode ⟨query.val.length,query.property⟩ ++ query.val.flatMap NativeGoldPcsWire.pairCodec.encode).length ≤ _
  rw [List.length_append]
  omega

theorem opening_length {C : Type} (parameters : Parameters C) (root : NativeRootMessage.Digest) (query : Query) (values : Row)
    (width : parameters.width.val ≤ 4) (numVars : parameters.numVariables.val < 64)
    (checked : NativeGoldPcsBinding.check parameters query values = true) :
    (NativeGoldPcsWire.opening root query values).length ≤ 20530 := by
  obtain ⟨count,claimed,matrices⟩ := (NativeGoldPcsBinding.check_iff parameters query values).mp checked
  have querySize := query_length query parameters.width.val width matrices
  have valueSize := row_length values
  rw [NativeGoldPcsWire.opening_encode]
  simp only [List.length_append,List.length_ofFn]
  omega

/-- These are checked prefix outputs, not caller-supplied query dimensions. -/
theorem completed_checks {Memory : Type} (ctx : NativeGoldPcsExecution.Context)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : NativeGoldPcsWorkers.Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion) :
    ctx.parameters.numVariables.val < 64 ∧ NativeGoldPcsBinding.check ctx.parameters ctx.query ctx.claimed = true := by
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,_,encoded,_,_⟩ := NativeGoldPcsWorkers.prepared_origin
    ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world work prepared
  have columns := (NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening
    ctx.fieldFuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,sampling,_,_,_⟩ := NativeGoldPcsColumns.columns_origin NativeGoldBlockCode.description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry state weights sample columns
  obtain ⟨built,_,bound,accepted,_⟩ := NativeGoldPcsPrelude.sampling_origin NativeGoldBlockCode.description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geometry (.finished state next) sampling
  exact ⟨(NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters geometry built).basic.2.2.1,
    NativeGoldPcsBinding.bound_check NativeGoldBlockCode.description.row ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed world bound accepted⟩

theorem completed_fits {Memory : Type} (ctx : NativeGoldPcsExecution.Context)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : NativeGoldPcsWorkers.Prepared) (completion : NativeGoldPcsAcceptance.Completion Memory work.jobs.length)
    (executed : (run (NativeGoldPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (width : ctx.parameters.width.val ≤ 4) :
    (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit := by
  have checked := completed_checks ctx choose fuel memory world work completion executed
  exact lt_of_le_of_lt (opening_length ctx.parameters ctx.root ctx.query ctx.claimed width checked.1 checked.2)
    (by decide +kernel : 20530 < TranscriptFrame.lengthLimit)

end FormalProof4FHE.HasteBoots.CheckedPcsMetadataSize
