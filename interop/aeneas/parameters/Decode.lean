/-! Appended after the unchanged source accessors and ModelBridge.lean.
This checked decoder constructs the representation from actual stored fields.
It preserves raw roots and every UTF-8 byte; it does not validate a constructor,
field canonicality, target ABI arithmetic, heap state or physical costs. -/
namespace HasteBootsExtractedParametersDecode
open Aeneas Aeneas.Std
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedParametersProof (Code Params)
open HasteBootsExtractedParametersBridge

theorem usize_fits64 (word : Usize) : word.val < 2^64 := by
  have fits := word.hBounds
  change word.val < 2^(System.Platform.getNumBits ()).val at fits
  rcases (System.Platform.getNumBits ()).property with bits32 | bits64
  · rw [bits32] at fits
    omega
  · simpa only [bits64] using fits

def word64 (word : Usize) : NativeUsizeMessage.Usize :=
  ⟨word.val,usize_fits64 word⟩

def bytes (source : Code) : List InputIndexedOracle.Byte :=
  source.modulus.toUTF8.toList.map fun byte => ⟨byte.toNat,byte.toBitVec.isLt⟩

def packCode (source : Code) (fits : (bytes source).length < 2^64) : NativeGoldBlockCode.Stored :=
  ⟨word64 source.message_len,word64 source.block_width,word64 source.message_blocks,
    word64 source.codeword_blocks,⟨bytes source,fits⟩,⟨source.domain_root.val,source.domain_root.hBounds⟩⟩

def decodeCode (source : Code) : Option NativeGoldBlockCode.Stored :=
  if fits : (bytes source).length < 2^64 then some (packCode source fits) else none

theorem pack_code_rep (source : Code) (fits : (bytes source).length < 2^64) :
    CodeRep source (packCode source fits) := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl⟩
  change source.modulus.toUTF8.toList.map UInt8.toNat = (bytes source).map Fin.val
  rw [bytes,List.map_map]
  rfl

theorem decode_code_correct (source : Code) (model : NativeGoldBlockCode.Stored)
    (decoded : decodeCode source = some model) : CodeRep source model := by
  unfold decodeCode at decoded
  split at decoded
  · rename_i fits
    have same := Option.some.inj decoded
    exact same ▸ pack_code_rep source fits
  · contradiction

theorem decode_code_complete (source : Code) (model : NativeGoldBlockCode.Stored)
    (represented : CodeRep source model) : decodeCode source = some model := by
  have lengths := congrArg List.length represented.modulus
  simp only [List.length_map] at lengths
  have fits : (bytes source).length < 2^64 := by
    rw [bytes,List.length_map,lengths]
    exact model.modulus.property
  have same := code_model_unique source (packCode source fits) model (pack_code_rep source fits) represented
  unfold decodeCode
  rw [dite_eq_left fits,same]

theorem decode_code_iff (source : Code) (model : NativeGoldBlockCode.Stored) :
    decodeCode source = some model ↔ CodeRep source model :=
  ⟨decode_code_correct source model,decode_code_complete source model⟩

def packParameters (source : Params) (code : NativeGoldBlockCode.Stored) :
    NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored :=
  ⟨word64 source.num_vars,word64 source.width,word64 source.left_vars,word64 source.queries,code⟩

def decodeParameters (source : Params) :
    Option (NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) :=
  (decodeCode source.code).map (packParameters source)

theorem pack_parameters_rep (source : Params) (code : NativeGoldBlockCode.Stored)
    (represented : CodeRep source.code code) : ParametersRep source (packParameters source code) :=
  ⟨rfl,rfl,rfl,rfl,represented⟩

theorem decode_parameters_correct (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (decoded : decodeParameters source = some model) : ParametersRep source model := by
  unfold decodeParameters at decoded
  cases codeRun : decodeCode source.code with
  | none =>
    simp only [codeRun,Option.map_none] at decoded
    cases decoded
  | some code =>
    simp only [codeRun,Option.map_some] at decoded
    have same := Option.some.inj decoded
    exact same ▸ pack_parameters_rep source code (decode_code_correct source.code code codeRun)

theorem decode_parameters_complete (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (represented : ParametersRep source model) : decodeParameters source = some model := by
  unfold decodeParameters
  rw [decode_code_complete source.code model.code represented.code,Option.map_some]
  have same := parameters_model_unique source (packParameters source model.code) model
    (pack_parameters_rep source model.code represented.code) represented
  exact congrArg some same

theorem decode_parameters_iff (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) :
    decodeParameters source = some model ↔ ParametersRep source model :=
  ⟨decode_parameters_correct source model,decode_parameters_complete source model⟩

theorem decoded_header (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (decoded : decodeParameters source = some model) :
    observeHeader source = .ok (model.numVariables.val,model.width.val,model.leftVariables.val,model.queries.val) :=
  header_correspondence source model (decode_parameters_correct source model decoded)

theorem decoded_code (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (decoded : decodeParameters source = some model) :
    observeCode source = .ok (model.code.messageLength.val,model.code.blockWidth.val,model.code.messageBlocks.val,
      model.code.blocks.val,model.code.modulus.val.map Fin.val,model.code.domainRoot.val) :=
  code_correspondence source model (decode_parameters_correct source model decoded)

theorem decode_code_exists_iff (source : Code) :
    (∃ model, decodeCode source = some model) ↔ source.modulus.toUTF8.toList.length < 2^64 := by
  have lengths : (bytes source).length = source.modulus.toUTF8.toList.length := by
    rw [bytes,List.length_map]
  rw [← lengths]
  unfold decodeCode
  split
  · rename_i fits
    exact ⟨fun _ => fits,fun _ => ⟨_,rfl⟩⟩
  · rename_i tooLong
    constructor
    · rintro ⟨_,impossible⟩
      cases impossible
    · intro fits
      exact False.elim (tooLong fits)

theorem decode_parameters_exists_iff (source : Params) :
    (∃ model, decodeParameters source = some model) ↔ source.code.modulus.toUTF8.toList.length < 2^64 := by
  rw [← decode_code_exists_iff source.code]
  constructor
  · rintro ⟨model,decoded⟩
    exact ⟨model.code,decode_code_complete source.code model.code
      (decode_parameters_correct source model decoded).code⟩
  · rintro ⟨code,decoded⟩
    exact ⟨packParameters source code,by unfold decodeParameters; rw [decoded]; rfl⟩

theorem retained_decode (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (decoded : decodeParameters source = some model) :
    (do let returned ← formalproof4fhe_native_ntt_cache_fixture.retained_code source
        pure (decodeCode returned)) = (Result.ok (some model.code)) := by
  change Result.ok (decodeCode source.code) = _
  rw [decode_code_complete source.code model.code (decode_parameters_correct source model decoded).code]

end HasteBootsExtractedParametersDecode
