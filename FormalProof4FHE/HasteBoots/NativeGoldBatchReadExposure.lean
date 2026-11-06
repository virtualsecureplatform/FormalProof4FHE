module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyExposure
public import FormalProof4FHE.HasteBoots.NativePrimeReadExposure
import all Init.Data.String.Defs
@[expose] public section

/-! The actual prepared native batch supplies its context hash and positive random-test read. Native parent framing and the encoded batch message allocation bound remain explicit. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (description)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input World bytes)
open NativeTranscript (Transcript Observation utf8)
open OracleProgram (run)
open NativeMerkleShapeFamily (Height)
noncomputable section

def phase (_ctx : Context) (work : Prepared) := NativePrimeRequest.phase NativeFields.goldilocksModulus
  work.binding.parent .vector NativeGoldBatchPrelude.randomLabel work.geometry.randomCount

theorem prepared_read (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ∃ context : Digest,
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      work.binding.parent = NativeGoldBatchBinding.appendBound ctx.parent context ctx.root ctx.queries ctx.values ∧
      .output (phase ctx work).pending.input 0 (bytes world (phase ctx work).pending.input 0 8) ∈
        (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,loaded,encodedTest,encodedValues,attached,rfl⟩ :=
    NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,columnsLog⟩ := NativeGoldBatchColumns.columns_log description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨built,bound,_,sampled⟩ := NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values
    ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude
  obtain ⟨_,context,hashed,same,_⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  have spec := NativeBrakedownParameters.build_spec description ctx.parameters geometry built
  have positive : geometry.randomCount.val ≠ 0 := by
    rw [spec.computed]
    change 2^ctx.parameters.leftVariables.val * ctx.parameters.width.val * ctx.parameters.width.val ≠ 0
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (by positivity) spec.basic.1) spec.basic.1
  have read := NativePrimeReadExposure.finished_read NativeFields.goldilocksModulus ctx.fieldFuel binding.parent .vector
    NativeGoldBatchPrelude.randomLabel geometry.randomCount positive world state next sampled
  have width : CanonicalByteSampler.byteCount NativeFields.goldilocksModulus = 8 := by decide +kernel
  rw [width] at read
  refine ⟨context,hashed,congrArg NativeGoldBatchBinding.Bound.parent same,?_⟩
  rw [NativeGoldBatchPcsProgram.run_prepareProgram,columnsLog,
    NativeGoldBatchPrelude.sampling_log description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude]
  exact List.mem_append_left _ (List.mem_append_right _ read)
def suffix (count : NativeUsizeMessage.Usize) : List TranscriptFrame.Frame :=
  [⟨1,utf8 "typed request kind",TypedFieldRequest.kindBytes .vector⟩,
   ⟨1,utf8 "field challenge kind",utf8 "prime vector"⟩,
   ⟨4,NativeGoldBatchPrelude.randomLabel,TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus ++
     TranscriptFrame.littleEndian 8 count.val⟩]

theorem suffix_valid (count : NativeUsizeMessage.Usize) : ∀ frame ∈ suffix count, TranscriptFrame.Valid frame := by
  intro frame member
  simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · unfold TranscriptFrame.Valid
    decide +kernel
  · unfold TranscriptFrame.Valid
    decide +kernel
  · constructor
    · change NativeGoldBatchPrelude.randomLabel.length < TranscriptFrame.lengthLimit
      decide +kernel
    · simp only [List.length_append,TranscriptFrame.littleEndian_length]
      decide +kernel

private theorem encodeMany_append (first last : List TranscriptFrame.Frame) :
    TranscriptFrame.encodeMany (first++last) = TranscriptFrame.encodeMany first ++ TranscriptFrame.encodeMany last := by
  induction first with
  | nil => rfl
  | cons frame rest ih => simp only [List.cons_append,TranscriptFrame.encodeMany,ih,List.append_assoc]

theorem phase_input (ctx : Context) (work : Prepared) (context : Digest) (before : List TranscriptFrame.Frame)
    (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (binding : work.binding.parent = NativeGoldBatchBinding.appendBound ctx.parent context ctx.root ctx.queries ctx.values) :
    (phase ctx work).pending.input = NativeGoldBatchExposure.input before (suffix work.geometry.randomCount)
      ⟨context,ctx.root,ctx.queries,ctx.values⟩ := by
  change (NativePrimeRequest.prepare work.binding.parent .vector).input ++ TranscriptFrame.encode
    ⟨4,NativeGoldBatchPrelude.randomLabel,TranscriptFrame.littleEndian 16 NativeFields.goldilocksModulus ++
      TranscriptFrame.littleEndian 8 work.geometry.randomCount.val⟩ = _
  rw [NativePrimeRequest.prepare_input,binding,NativeGoldBatchBinding.appendBound_input,parent]
  simp only [NativeGoldBatchExposure.input,encodeMany_append,NativeGoldBatchExposure.frame,suffix,
    TranscriptFrame.encodeMany,List.append_nil,List.append_assoc,NativeGoldBatchRootMentions.payload_encode]

theorem frame_valid (context root : Digest) (queries : NativePrefixCodec.Vector NativeGoldPcsWire.Query)
    (values : NativePrefixCodec.Vector NativeLookupRequestWire.Row)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode values).length < TranscriptFrame.lengthLimit) :
    TranscriptFrame.Valid (NativeGoldBatchExposure.frame ⟨context,root,queries,values⟩) := by
  constructor
  · change (utf8 "mw batched row-code v1").length < TranscriptFrame.lengthLimit
    decide +kernel
  · change (NativeGoldBatchMessage.codec.encode _).length < _
    rw [← NativeGoldBatchRootMentions.payload_encode]
    simpa only [NativeGoldBatchBinding.payload,List.length_append,List.length_ofFn] using fits

/-- The real successful prefix supplies the read, context digest, exact batch
frame and all frame bounds needed by the raw exposure monitor. -/
theorem prepared_exposure (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List TranscriptFrame.Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit) :
    ∃ context : Digest,
      (run (NativeBrakedownContext.context description.row ctx.parameters) world).run.1 = some context ∧
      (∀ entry ∈ before ++ NativeGoldBatchExposure.frame ⟨context,work.root,work.binding.queries,work.binding.values⟩ ::
        suffix work.geometry.randomCount, TranscriptFrame.Valid entry) ∧
      .output (NativeGoldBatchExposure.input before (suffix work.geometry.randomCount)
        ⟨context,work.root,work.binding.queries,work.binding.values⟩) 0
        (bytes world (NativeGoldBatchExposure.input before (suffix work.geometry.randomCount)
          ⟨context,work.root,work.binding.queries,work.binding.values⟩) 0 8) ∈
        (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.2 := by
  obtain ⟨context,hashed,binding,read⟩ := prepared_read ctx world work executed
  have bound := NativeGoldBatchPcsProgram.prepared_binding ctx world work executed
  rw [phase_input ctx work context before parent binding] at read
  refine ⟨context,hashed,?_,?_⟩
  · rw [bound.1,bound.2.2.1,bound.2.2.2]
    intro entry member
    rcases List.mem_append.mp member with old | added
    · exact valid entry old
    · rcases List.mem_cons.mp added with rfl | tail
      · exact frame_valid context ctx.root ctx.queries ctx.values fits
      · exact suffix_valid work.geometry.randomCount entry tail
  · simpa only [bound.1,bound.2.2.1,bound.2.2.2] using read

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
