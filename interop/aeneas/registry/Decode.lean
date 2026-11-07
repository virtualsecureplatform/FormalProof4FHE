/-! Value-level decoding of the actual native verifier carrier. Parameter reads
use the checked retained-parameter decoder and every raw SHA-512 byte is kept.
This does not identify heap addresses or establish constructor/hash refinement. -/
namespace HasteBootsExtractedRegistryDecode
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedRegistryProof (Oracle Digest root_length)
open HasteBootsExtractedParametersDecode (decodeParameters)
open formalproof4fhe_native_registry_fixture (fields root_bytes)

abbrev Source := Oracle Digest HasteBootsExtractedParametersProof.Params
abbrev Model := NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored

def root (source : Digest) : NativeRootMessage.Digest := fun index =>
  let byte := source.val[index.val]'(by rw [root_length]; exact index.isLt)
  ⟨byte.val,byte.hBounds⟩

theorem root_value (source : Digest) (index : Fin 64) :
    (root source index).val =
      (source.val[index.val]'(by rw [root_length]; exact index.isLt)).val := rfl

theorem root_injective : Function.Injective root := by
  intro left right same
  apply Subtype.ext
  apply List.ext_getElem (by rw [root_length,root_length])
  intro index leftBound rightBound
  have bound : index < 64 := by simpa only [root_length] using leftBound
  have bytesEq := congrArg (fun digest : NativeRootMessage.Digest => (digest ⟨index,bound⟩).val) same
  exact UScalar.eq_of_val_eq bytesEq

def decode (source : Source) : Option Model :=
  (decodeParameters source.parameters).map (fun parameters => ⟨parameters,root source.commitment.root⟩)

theorem decode_fields (source : Source) (model : Model) (decoded : decode source = some model) :
    decodeParameters source.parameters = some model.parameters ∧ model.root = root source.commitment.root := by
  unfold decode at decoded
  cases parametersRun : decodeParameters source.parameters with
  | none =>
    simp only [parametersRun,Option.map_none] at decoded
    cases decoded
  | some parameters =>
    simp only [parametersRun,Option.map_some] at decoded
    cases Option.some.inj decoded
    exact ⟨rfl,rfl⟩

theorem decode_injective (left right : Source) (model : Model)
    (first : decode left = some model) (second : decode right = some model) : left = right := by
  have firstFields := decode_fields left model first
  have secondFields := decode_fields right model second
  have parametersEq := HasteBootsExtractedParametersBinding.decode_parameters_injective
    left.parameters right.parameters model.parameters firstFields.1 secondFields.1
  have rootEq := root_injective (firstFields.2.symm.trans secondFields.2)
  cases left with
  | mk leftParameters leftCommitment =>
    cases right with
    | mk rightParameters rightCommitment =>
      cases leftCommitment
      cases rightCommitment
      cases parametersEq
      cases rootEq
      rfl

def readDecoded (source : Source) : Result (Option Model) := do
  let (parameters,rawRoot) ← fields source
  pure ((decodeParameters parameters).map (fun model => ⟨model,root rawRoot⟩))

theorem read_decoded_exact (source : Source) : readDecoded source = .ok (decode source) := rfl

theorem read_root_exact (source : Source) :
    (do let rawRoot ← root_bytes source; pure (root rawRoot)) =
      Result.ok (root source.commitment.root) := rfl

theorem decode_exists_iff (source : Source) :
    (∃ model, decode source = some model) ↔ source.parameters.code.modulus.toUTF8.toList.length < 2^64 := by
  rw [← HasteBootsExtractedParametersDecode.decode_parameters_exists_iff source.parameters]
  constructor
  · rintro ⟨model,decoded⟩
    exact ⟨model.parameters,(decode_fields source model decoded).1⟩
  · rintro ⟨parameters,decoded⟩
    exact ⟨⟨parameters,root source.commitment.root⟩,by unfold decode; rw [decoded]; rfl⟩

end HasteBootsExtractedRegistryDecode
