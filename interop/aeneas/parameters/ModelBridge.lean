/-! Appended after the unchanged generated accessor terms and Proof.lean.
Exact representation relations connect extracted source reads to the word model.
These relations must still be established by constructor/source refinement;
these theorems do not assume or prove that every native object is represented. -/
namespace HasteBootsExtractedParametersBridge
open Aeneas Aeneas.Std
open formalproof4fhe_native_ntt_cache_fixture
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedParametersProof (Code Params)

structure CodeRep (source : Code) (model : NativeGoldBlockCode.Stored) : Prop where
  message : source.message_len.val = model.messageLength.val
  width : source.block_width.val = model.blockWidth.val
  padded : source.message_blocks.val = model.messageBlocks.val
  blocks : source.codeword_blocks.val = model.blocks.val
  modulus : source.modulus.toUTF8.toList.map UInt8.toNat = model.modulus.val.map Fin.val
  root : source.domain_root.val = model.domainRoot.val

structure ParametersRep (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) : Prop where
  numVariables : source.num_vars.val = model.numVariables.val
  width : source.width.val = model.width.val
  left : source.left_vars.val = model.leftVariables.val
  queries : source.queries.val = model.queries.val
  code : CodeRep source.code model.code

theorem code_model_unique (source : Code) (first second : NativeGoldBlockCode.Stored)
    (left : CodeRep source first) (right : CodeRep source second) : first = second := by
  have modulus : first.modulus = second.modulus := by
    apply Subtype.ext
    exact (List.map_injective_iff.mpr Fin.val_injective) (left.modulus.symm.trans right.modulus)
  apply NativeGoldBlockCode.fields.injective
  change (first.messageLength,first.blockWidth,first.messageBlocks,first.blocks,first.modulus,first.domainRoot) =
    (second.messageLength,second.blockWidth,second.messageBlocks,second.blocks,second.modulus,second.domainRoot)
  exact Prod.ext (Fin.ext (left.message.symm.trans right.message))
    (Prod.ext (Fin.ext (left.width.symm.trans right.width))
      (Prod.ext (Fin.ext (left.padded.symm.trans right.padded))
        (Prod.ext (Fin.ext (left.blocks.symm.trans right.blocks))
          (Prod.ext modulus (Fin.ext (left.root.symm.trans right.root))))))

theorem parameters_model_unique (source : Params)
    (first second : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (left : ParametersRep source first) (right : ParametersRep source second) : first = second := by
  have vars := Fin.ext (left.numVariables.symm.trans right.numVariables)
  have width := Fin.ext (left.width.symm.trans right.width)
  have splitVars := Fin.ext (left.left.symm.trans right.left)
  have queries := Fin.ext (left.queries.symm.trans right.queries)
  have code := code_model_unique source.code first.code second.code left.code right.code
  cases first
  cases second
  congr

def observeHeader (source : Params) : Result (Nat × Nat × Nat × Nat) := do
  let dimensions ← header source
  pure (dimensions.1.val,dimensions.2.1.val,dimensions.2.2.1.val,dimensions.2.2.2.val)

def observeCode (source : Params) : Result (Nat × Nat × Nat × Nat × List Nat × Nat) := do
  let code ← retained_code source
  pure (code.message_len.val,code.block_width.val,code.message_blocks.val,code.codeword_blocks.val,
    code.modulus.toUTF8.toList.map UInt8.toNat,code.domain_root.val)

theorem header_correspondence (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (represented : ParametersRep source model) :
    observeHeader source = .ok (model.numVariables.val,model.width.val,model.leftVariables.val,model.queries.val) := by
  change Result.ok (source.num_vars.val,source.width.val,source.left_vars.val,source.queries.val) = _
  rw [represented.numVariables,represented.width,represented.left,represented.queries]

theorem code_correspondence (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (represented : ParametersRep source model) :
    observeCode source = .ok (model.code.messageLength.val,model.code.blockWidth.val,model.code.messageBlocks.val,
      model.code.blocks.val,model.code.modulus.val.map Fin.val,model.code.domainRoot.val) := by
  change Result.ok (source.code.message_len.val,source.code.block_width.val,source.code.message_blocks.val,
    source.code.codeword_blocks.val,source.code.modulus.toUTF8.toList.map UInt8.toNat,source.code.domain_root.val) = _
  rw [represented.code.message,represented.code.width,represented.code.padded,represented.code.blocks,
    represented.code.modulus,represented.code.root]

theorem returned_representation (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (represented : ParametersRep source model) (returned : Code)
    (executed : retained_code source = .ok returned) : CodeRep returned model.code := by
  have same : source.code = returned := Result.ok.inj executed
  rw [← same]
  exact represented.code

theorem read_root_meaning (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (represented : ParametersRep source model) (returned : Code)
    (executed : retained_code source = .ok returned)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue model.code.domainRoot)
      (2^(NativeGoldBlockCode.logSize model.code+1))) :
    IsPrimitiveRoot (returned.domain_root.val : NativeFields.Goldilocks)
      (2^(NativeGoldBlockCode.logSize model.code+1)) := by
  rw [(returned_representation source model represented returned executed).root]
  exact primitive

theorem constructed_read_root (source : Params) (request : NativeGoldBlockCodeProgram.Request)
    (headerInput : NativeGoldEncodedParameters.Header) (config : NativeGoldBlockCodeProgram.Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (initialized : NativeGoldEncodedParameters.Initialized)
    (finished : NativeGoldParameterInitialization.finish headerInput config = some (.ok initialized))
    (represented : ParametersRep source initialized.parameters) (returned : Code)
    (executed : retained_code source = .ok returned) :
    IsPrimitiveRoot (returned.domain_root.val : NativeFields.Goldilocks)
      (2^(NativeGoldBlockCode.logSize initialized.parameters.code+1)) :=
  read_root_meaning source initialized.parameters represented returned executed
    (NativeGoldParameterInitialization.code_primitive headerInput request config reachable initialized finished)

theorem constructed_read_root_canonical (source : Params) (request : NativeGoldBlockCodeProgram.Request)
    (headerInput : NativeGoldEncodedParameters.Header) (config : NativeGoldBlockCodeProgram.Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (initialized : NativeGoldEncodedParameters.Initialized)
    (finished : NativeGoldParameterInitialization.finish headerInput config = some (.ok initialized))
    (represented : ParametersRep source initialized.parameters) (returned : Code)
    (executed : retained_code source = .ok returned) :
    returned.domain_root.val < NativeFields.goldilocksModulus := by
  obtain ⟨root,_,_,same⟩ := NativeGoldParameterInitialization.encoding_available
    headerInput request config reachable initialized finished
  rw [(returned_representation source initialized.parameters represented returned executed).root,← same]
  exact root.isLt

theorem constructed_read_modulus (source : Params) (request : NativeGoldBlockCodeProgram.Request)
    (headerInput : NativeGoldEncodedParameters.Header) (config : NativeGoldBlockCodeProgram.Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config)
    (initialized : NativeGoldEncodedParameters.Initialized)
    (finished : NativeGoldParameterInitialization.finish headerInput config = some (.ok initialized))
    (represented : ParametersRep source initialized.parameters) (returned : Code)
    (executed : retained_code source = .ok returned) :
    returned.modulus.toUTF8.toList.map UInt8.toNat = NativeBrakedownContext.modulus.val.map Fin.val := by
  obtain ⟨result,phase,built⟩ := NativeGoldParameterInitialization.finish_origin headerInput config initialized finished
  have retained := NativeGoldEncodedParameters.retained_code headerInput result.code initialized built
  have spec := NativeGoldBlockCode.build_spec _ request.message request.block request.blowup result.code
    (NativeGoldBlockCodeBackend.completed_build request config reachable result phase)
  rw [(returned_representation source initialized.parameters represented returned executed).modulus,retained,spec.modulus]

end HasteBootsExtractedParametersBridge
