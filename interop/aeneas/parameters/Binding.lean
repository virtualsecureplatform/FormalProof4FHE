/-! Structural binding of checked retained-source values through the existing
model wire codecs. These are byte-input results, not a Rust Serde refinement,
hash collision-resistance theorem, heap identity theorem or cost claim. -/
namespace HasteBootsExtractedParametersBinding
open Aeneas Aeneas.Std
open FormalProof4FHE.HasteBoots
open HasteBootsExtractedParametersProof (Code Params)
open HasteBootsExtractedParametersBridge
open HasteBootsExtractedParametersDecode
open InputIndexedOracle (Input)

theorem byte_list_data (array : ByteArray) : array.toList = array.data.toList := by
  cases array with
  | mk data =>
    have loop : ∀ (i : Nat) (acc : List UInt8),
        ByteArray.toList.loop ⟨data⟩ i acc = acc.reverse ++ data.toList.drop i := by
      intro i acc
      fun_induction ByteArray.toList.loop ⟨data⟩ i acc with
      | case1 i acc h ih =>
        change i < data.size at h
        have bound : i < data.toList.length := by simpa only [Array.length_toList] using h
        have byteSame : ByteArray.get! ⟨data⟩ i = data.toList[i]'bound := by
          simp only [ByteArray.get!,getElem!_pos data i h,Array.getElem_toList]
        rw [ih,List.reverse_cons,List.append_assoc,List.drop_eq_getElem_cons bound,byteSame]
        rfl
      | case2 i acc h =>
        change ¬i < data.size at h
        have past : data.toList.length ≤ i := by
          simpa only [Array.length_toList] using Nat.le_of_not_gt h
        rw [List.drop_eq_nil_iff.mpr past,List.append_nil]
    exact (loop 0 [])

theorem utf8_values_injective (left right : String)
    (same : left.toUTF8.toList.map UInt8.toNat = right.toUTF8.toList.map UInt8.toNat) : left = right := by
  have listEq : left.toUTF8.toList = right.toUTF8.toList :=
    (List.map_injective_iff.mpr (fun _ _ equality => UInt8.toNat_inj.mp equality)) same
  apply String.toByteArray_inj.mp
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [String.toUTF8_eq_toByteArray,byte_list_data] using listEq

theorem code_source_unique (left right : Code) (model : NativeGoldBlockCode.Stored)
    (first : CodeRep left model) (second : CodeRep right model) : left = right := by
  have message := UScalar.eq_of_val_eq (first.message.trans second.message.symm)
  have width := UScalar.eq_of_val_eq (first.width.trans second.width.symm)
  have padded := UScalar.eq_of_val_eq (first.padded.trans second.padded.symm)
  have blocks := UScalar.eq_of_val_eq (first.blocks.trans second.blocks.symm)
  have modulus := utf8_values_injective left.modulus right.modulus (first.modulus.trans second.modulus.symm)
  have root := UScalar.eq_of_val_eq (first.root.trans second.root.symm)
  cases left
  cases right
  cases message
  cases width
  cases padded
  cases blocks
  cases modulus
  cases root
  rfl

theorem parameters_source_unique (left right : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (first : ParametersRep left model) (second : ParametersRep right model) : left = right := by
  have variablesEq := UScalar.eq_of_val_eq (first.numVariables.trans second.numVariables.symm)
  have width := UScalar.eq_of_val_eq (first.width.trans second.width.symm)
  have splitEq := UScalar.eq_of_val_eq (first.left.trans second.left.symm)
  have queries := UScalar.eq_of_val_eq (first.queries.trans second.queries.symm)
  have code := code_source_unique left.code right.code model.code first.code second.code
  cases left
  cases right
  cases variablesEq
  cases width
  cases splitEq
  cases queries
  cases code
  rfl

theorem decode_code_injective (left right : Code) (model : NativeGoldBlockCode.Stored)
    (first : decodeCode left = some model) (second : decodeCode right = some model) : left = right :=
  code_source_unique left right model (decode_code_correct left model first) (decode_code_correct right model second)

theorem decode_parameters_injective (left right : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (first : decodeParameters left = some model) (second : decodeParameters right = some model) : left = right :=
  parameters_source_unique left right model
    (decode_parameters_correct left model first) (decode_parameters_correct right model second)

def codeWire (source : Code) : Option Input :=
  (decodeCode source).map NativeGoldBlockCode.codec.encode

def contextWire (source : Params) : Option Input :=
  (decodeParameters source).bind (NativeBrakedownContext.input NativeGoldBlockCode.description.row)

theorem code_wire_computed (source : Code) (model : NativeGoldBlockCode.Stored)
    (decoded : decodeCode source = some model) :
    codeWire source = some (NativeGoldBlockCode.codec.encode model) := by
  unfold codeWire
  rw [decoded,Option.map_some]

theorem code_wire_success_injective (left right : Code) (wire : Input)
    (first : codeWire left = some wire) (second : codeWire right = some wire) : left = right := by
  unfold codeWire at first second
  cases leftRun : decodeCode left with
  | none =>
    simp only [leftRun,Option.map_none] at first
    cases first
  | some leftModel =>
    cases rightRun : decodeCode right with
    | none =>
      simp only [rightRun,Option.map_none] at second
      cases second
    | some rightModel =>
      simp only [leftRun,Option.map_some] at first
      simp only [rightRun,Option.map_some] at second
      have same := NativeGoldBlockCode.serialize_injective
        ((Option.some.inj first).trans (Option.some.inj second).symm)
      cases same
      exact decode_code_injective left right leftModel leftRun rightRun

theorem context_wire_computed (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (decoded : decodeParameters source = some model) :
    contextWire source = some (NativeBrakedownContext.domain ++
      NativeGoldBlockCodeContext.contextCodec.encode (NativeGoldBlockCodeContext.contextFields model)) := by
  unfold contextWire
  rw [decoded,Option.bind_some,NativeGoldBlockCodeContext.input_computed]

theorem context_wire_success_injective (left right : Params) (wire : Input)
    (first : contextWire left = some wire) (second : contextWire right = some wire) : left = right := by
  unfold contextWire at first second
  cases leftRun : decodeParameters left with
  | none =>
    simp only [leftRun,Option.bind_none] at first
    cases first
  | some leftModel =>
    cases rightRun : decodeParameters right with
    | none =>
      simp only [rightRun,Option.bind_none] at second
      cases second
    | some rightModel =>
      simp only [leftRun,Option.bind_some] at first
      simp only [rightRun,Option.bind_some] at second
      have same := NativeGoldBlockCodeContext.input_injective (first.trans second.symm)
      cases same
      exact decode_parameters_injective left right leftModel leftRun rightRun

theorem code_wire_prefix (source : Code) (model : NativeGoldBlockCode.Stored) (wire suffix : Input)
    (decoded : decodeCode source = some model) (serialized : codeWire source = some wire) :
    NativeGoldBlockCode.codec.read (wire ++ suffix) = some (model,suffix) := by
  have same := Option.some.inj ((code_wire_computed source model decoded).symm.trans serialized)
  rw [← same]
  exact NativeGoldBlockCode.serialize_prefix model suffix

theorem context_wire_prefix (source : Params)
    (model : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored) (wire suffix : Input)
    (decoded : decodeParameters source = some model) (serialized : contextWire source = some wire) :
    NativeGoldBlockCodeContext.contextCodec.read
      (wire.drop NativeBrakedownContext.domain.length ++ suffix) =
      some (NativeGoldBlockCodeContext.contextFields model,suffix) := by
  have same := Option.some.inj ((context_wire_computed source model decoded).symm.trans serialized)
  rw [← same,List.drop_left]
  exact NativeGoldBlockCodeContext.metadata_prefix model suffix

theorem code_wire_prefix_injective (left right : Code) (firstModel secondModel : NativeGoldBlockCode.Stored)
    (firstWire secondWire firstTail secondTail : Input)
    (firstDecoded : decodeCode left = some firstModel) (secondDecoded : decodeCode right = some secondModel)
    (firstSerialized : codeWire left = some firstWire) (secondSerialized : codeWire right = some secondWire)
    (joined : firstWire ++ firstTail = secondWire ++ secondTail) :
    left = right ∧ firstTail = secondTail := by
  have parsed := congrArg NativeGoldBlockCode.codec.read joined
  rw [code_wire_prefix left firstModel firstWire firstTail firstDecoded firstSerialized,
      code_wire_prefix right secondModel secondWire secondTail secondDecoded secondSerialized] at parsed
  have parts := Prod.mk.inj (Option.some.inj parsed)
  have same := parts.1
  cases same
  exact ⟨decode_code_injective left right firstModel firstDecoded secondDecoded,parts.2⟩

theorem context_wire_prefix_injective (left right : Params)
    (firstModel secondModel : NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored)
    (firstWire secondWire firstTail secondTail : Input)
    (firstDecoded : decodeParameters left = some firstModel)
    (secondDecoded : decodeParameters right = some secondModel)
    (firstSerialized : contextWire left = some firstWire) (secondSerialized : contextWire right = some secondWire)
    (joined : firstWire ++ firstTail = secondWire ++ secondTail) :
    left = right ∧ firstTail = secondTail := by
  have firstBytes := Option.some.inj ((context_wire_computed left firstModel firstDecoded).symm.trans firstSerialized)
  have secondBytes := Option.some.inj ((context_wire_computed right secondModel secondDecoded).symm.trans secondSerialized)
  rw [← firstBytes,← secondBytes] at joined
  have metadataSame :
      NativeGoldBlockCodeContext.contextCodec.encode (NativeGoldBlockCodeContext.contextFields firstModel) ++ firstTail =
      NativeGoldBlockCodeContext.contextCodec.encode (NativeGoldBlockCodeContext.contextFields secondModel) ++ secondTail :=
    List.append_cancel_left (by simpa only [List.append_assoc] using joined)
  have parts := NativeGoldBlockCodeContext.contextCodec.prefix_injective
    (NativeGoldBlockCodeContext.contextFields firstModel) (NativeGoldBlockCodeContext.contextFields secondModel)
    firstTail secondTail metadataSame
  have same := NativeGoldBlockCodeContext.contextFields_injective parts.1
  cases same
  exact ⟨decode_parameters_injective left right firstModel firstDecoded secondDecoded,parts.2⟩

end HasteBootsExtractedParametersBinding
