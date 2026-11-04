module

public import FormalProof4FHE.HasteBoots.NativeFieldRepresentation
public import FormalProof4FHE.HasteBoots.NativeIntegerPrefix
public import FormalProof4FHE.HasteBoots.NativeExtensionFields
public import FormalProof4FHE.HasteBoots.NativeTranscript

@[expose] public section

/-!
# Raw field objects in native transcript serialization

Goldilocks writes its u64 newtype without canonicalization. BabyBear writes
its canonical raw Montgomery u32 newtype; its standard varint spelling is
the same as u64 in that range. Each native binomial extension uses a serde
sequence, including its degree header. These encoders retain raw storage;
field arithmetic, full packet/proof decoding and Rust refinement are open.
-/

namespace FormalProof4FHE.HasteBoots.NativeFieldWire

open InputIndexedOracle (Input)
open NativeFieldRepresentation

abbrev GoldExtension := Fin 3 → GoldWord
abbrev BabyExtension := Fin 6 → BabyWord

def babyU64 (word : BabyWord) : NativeUsizeMessage.Usize :=
  ⟨word.val, by have bound := word.isLt; unfold NativeFields.babyBearModulus at bound; norm_num; omega⟩

def gold (word : GoldWord) : Input := NativeUsizeMessage.encode word
def baby (word : BabyWord) : Input := NativeUsizeMessage.encode (babyU64 word)

theorem gold_injective : Function.Injective gold := NativeUsizeMessage.encode_injective

theorem baby_injective : Function.Injective baby := by
  intro left right same
  have words := NativeUsizeMessage.encode_injective same
  have values := congrArg (fun word : NativeUsizeMessage.Usize => word.val) words
  exact Fin.ext values

def goldExtension (value : GoldExtension) : Input :=
  NativeIntegerPrefix.encodeVector (List.ofFn value) (by simp)

def babyExtension (value : BabyExtension) : Input :=
  NativeIntegerPrefix.encodeVector (List.ofFn (fun i => babyU64 (value i))) (by simp)

theorem goldExtension_injective : Function.Injective goldExtension := by
  intro left right same
  have words := NativeIntegerPrefix.encodeVector_injective _ _ _ _ same
  exact List.ofFn_injective words

theorem babyExtension_injective : Function.Injective babyExtension := by
  intro left right same
  have words := NativeIntegerPrefix.encodeVector_injective _ _ _ _ same
  have functions := List.ofFn_injective words
  funext index
  exact Fin.ext (congrArg (fun values => (values index).val) functions)

/-- Native base-field slices, as used by encoded Merkle columns. -/
def goldColumn (values : List GoldWord) (fits : values.length < 2 ^ 64) : Input :=
  NativeIntegerPrefix.encodeVector values fits

def babyColumn (values : List BabyWord) (fits : values.length < 2 ^ 64) : Input :=
  NativeIntegerPrefix.encodeVector (values.map babyU64) (by simpa only [List.length_map] using fits)

theorem goldColumn_injective (left right : List GoldWord) (leftFits : left.length < 2 ^ 64)
    (rightFits : right.length < 2 ^ 64) (same : goldColumn left leftFits = goldColumn right rightFits) : left = right :=
  NativeIntegerPrefix.encodeVector_injective left right leftFits rightFits same

theorem babyColumn_injective (left right : List BabyWord) (leftFits : left.length < 2 ^ 64)
    (rightFits : right.length < 2 ^ 64) (same : babyColumn left leftFits = babyColumn right rightFits) : left = right := by
  have words := NativeIntegerPrefix.encodeVector_injective _ _ _ _ same
  apply List.map_injective_iff.mpr ?_ words
  intro first last equal
  exact Fin.ext (congrArg (fun word : NativeUsizeMessage.Usize => word.val) equal)

def columnDomain : Input := NativeTranscript.utf8 "HasteBoots/mw-column/v1"

def goldColumnInput (values : List GoldWord) (fits : values.length < 2 ^ 64) : Input :=
  columnDomain ++ goldColumn values fits

def babyColumnInput (values : List BabyWord) (fits : values.length < 2 ^ 64) : Input :=
  columnDomain ++ babyColumn values fits

theorem goldColumnInput_injective (left right : List GoldWord) (leftFits : left.length < 2 ^ 64)
    (rightFits : right.length < 2 ^ 64) (same : goldColumnInput left leftFits = goldColumnInput right rightFits) : left = right :=
  goldColumn_injective left right leftFits rightFits (List.append_cancel_left same)

theorem babyColumnInput_injective (left right : List BabyWord) (leftFits : left.length < 2 ^ 64)
    (rightFits : right.length < 2 ^ 64) (same : babyColumnInput left leftFits = babyColumnInput right rightFits) : left = right :=
  babyColumn_injective left right leftFits rightFits (List.append_cancel_left same)

noncomputable def goldExtensionValue (value : GoldExtension) : NativeExtensionFields.Goldilocks3 :=
  NativeExtensionFields.goldilocksBasis.equivFun.symm (fun i => goldValue (value i))

noncomputable def babyExtensionValue (value : BabyExtension) : NativeExtensionFields.BabyBear6 :=
  NativeExtensionFields.babyBearBasis.equivFun.symm (fun i => babyValue (value i))

theorem goldExtension_coordinate (value : GoldExtension) (index : Fin 3) :
    NativeExtensionFields.goldilocksBasis.equivFun (goldExtensionValue value) index = goldValue (value index) := by
  simp only [goldExtensionValue, LinearEquiv.apply_symm_apply]

theorem babyExtension_coordinate (value : BabyExtension) (index : Fin 6) :
    NativeExtensionFields.babyBearBasis.equivFun (babyExtensionValue value) index = babyValue (value index) := by
  simp only [babyExtensionValue, LinearEquiv.apply_symm_apply]

/-- BabyBear's representation invariant gives a unique raw spelling of
a field value; no corresponding assertion is valid for lazy Goldilocks. -/
theorem babyExtensionValue_injective : Function.Injective babyExtensionValue := by
  intro left right same
  funext index
  apply babyValue_injective
  have coordinates := congrArg (fun value => NativeExtensionFields.babyBearBasis.equivFun value index) same
  simpa only [babyExtension_coordinate] using coordinates

end FormalProof4FHE.HasteBoots.NativeFieldWire
