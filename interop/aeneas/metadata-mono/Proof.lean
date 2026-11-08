/-! Actual specialized native row metadata, with exact value correspondence to
retained parameters. This does not prove constructor, heap or context hashing. -/
namespace HasteBootsExtractedMetadataMono
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedParametersDecode (word64 decodeCode decode_code_correct)
namespace Native
open formalproof4fhe_native_registry_fixture
abbrev Code := pcs.utils.code.block.BlockReedSolomonCode
abbrev width := pcs.utils.code.block.BlockReedSolomonCode.Insts.PcsUtilsCodeBlockRowCodeGoldilocks.block_width
abbrev blocks := pcs.utils.code.block.BlockReedSolomonCode.Insts.PcsUtilsCodeBlockRowCodeGoldilocks.codeword_blocks
abbrev domain := pcs.utils.code.block.BlockReedSolomonCode.Insts.PcsUtilsCodeBlockRowCodeGoldilocks.domain_separator
abbrev metadata := row_metadata
end Native

def specialize (source : HasteBootsExtractedParametersProof.Code) : Native.Code :=
  ⟨source.message_len,source.block_width,source.message_blocks,source.codeword_blocks,source.modulus,source.domain_root⟩

def retain (source : Native.Code) : HasteBootsExtractedParametersProof.Code :=
  ⟨source.message_len,source.block_width,source.message_blocks,source.codeword_blocks,source.modulus,source.domain_root⟩

theorem retain_specialize (source : HasteBootsExtractedParametersProof.Code) : retain (specialize source) = source := rfl

theorem specialize_retain (source : Native.Code) : specialize (retain source) = source := rfl

theorem width_exact (source : Native.Code) : Native.width source = .ok source.block_width := rfl

theorem blocks_exact (source : Native.Code) : Native.blocks source = .ok source.codeword_blocks := rfl

def bytes (source : Slice U8) : NativePrefixCodec.Vector InputIndexedOracle.Byte :=
  ⟨source.val.map (fun byte => ⟨byte.val,byte.hBounds⟩),by
    rw [List.length_map]
    exact HasteBootsExtractedParametersDecode.usize_fits64 (Slice.len source)⟩

def domain (source : Native.Code) : Result (NativePrefixCodec.Vector InputIndexedOracle.Byte) := do
  let raw ← Native.domain source
  .ok (bytes raw)

theorem domain_model (source : Native.Code) : domain source = .ok NativeGoldBlockCode.domain := rfl

def metadata (source : Native.Code) : Result (NativeUsizeMessage.Usize × NativeUsizeMessage.Usize ×
    NativePrefixCodec.Vector InputIndexedOracle.Byte) := do
  let (width,blocks,tag) ← Native.metadata source
  .ok (word64 width,word64 blocks,bytes tag)

theorem metadata_exact (source : Native.Code) :
    metadata source = .ok (word64 source.block_width,word64 source.codeword_blocks,NativeGoldBlockCode.domain) := rfl

theorem metadata_rep (source : Native.Code) (model : NativeGoldBlockCode.Stored)
    (represented : HasteBootsExtractedParametersBridge.CodeRep (retain source) model) :
    metadata source = .ok (model.blockWidth,model.blocks,NativeGoldBlockCode.domain) := by
  rw [metadata_exact]
  have width : word64 source.block_width = model.blockWidth := Fin.ext represented.width
  have blocks : word64 source.codeword_blocks = model.blocks := Fin.ext represented.blocks
  rw [width,blocks]

theorem metadata_decoded (source : Native.Code) (model : NativeGoldBlockCode.Stored)
    (decoded : decodeCode (retain source) = some model) :
    metadata source = .ok (model.blockWidth,model.blocks,NativeGoldBlockCode.domain) :=
  metadata_rep source model (decode_code_correct (retain source) model decoded)

theorem metadata_specialized (source : HasteBootsExtractedParametersProof.Code) (model : NativeGoldBlockCode.Stored)
    (decoded : decodeCode source = some model) :
    metadata (specialize source) = .ok (model.blockWidth,model.blocks,NativeGoldBlockCode.domain) :=
  metadata_decoded (specialize source) model decoded

theorem parameter_metadata (source : HasteBootsExtractedParametersProof.Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (decoded : HasteBootsExtractedParametersDecode.decodeParameters source = some model) :
    metadata (specialize source.code) = .ok (model.code.blockWidth,model.code.blocks,NativeGoldBlockCode.domain) :=
  metadata_rep (specialize source.code) model.code
    (HasteBootsExtractedParametersDecode.decode_parameters_correct source model decoded).code

/-- The same original native slot already selected by the causal receipt bridge
supplies the native row metadata of the accepted extraction parameters. -/
theorem original_read_metadata {Memory : Type}
    (source : Slice HasteBootsExtractedRegistryDecode.Source)
    (ctx : HasteBootsExtractedRegistryCausalLookup.Context)
    (receipt : NativeDeferredBatchVerification.Receipt Memory)
    (extractCtx : NativeGoldBatchPcsProgram.Context) (expectedRoot : NativeRootMessage.Digest)
    (origin : HasteBootsExtractedRegistryCausalLookup.OriginalRead source ctx receipt extractCtx expectedRoot) :
    ∃ (word : Usize) (entry : HasteBootsExtractedRegistryDecode.Source),
      word.val = receipt.call.slot ∧
      formalproof4fhe_native_registry_fixture.registry_get source word =
        .ok (some (entry.parameters,entry.commitment.root)) ∧
      metadata (specialize entry.parameters.code) =
        .ok (extractCtx.parameters.code.blockWidth,extractCtx.parameters.code.blocks,NativeGoldBlockCode.domain) := by
  obtain ⟨_,word,entry,_,slot,read,_,decoded,_⟩ := origin
  exact ⟨word,entry,slot,read,parameter_metadata entry.parameters extractCtx.parameters decoded⟩

end HasteBootsExtractedMetadataMono
