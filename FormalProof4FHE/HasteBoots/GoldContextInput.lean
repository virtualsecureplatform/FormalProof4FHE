module
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCode
@[expose] public section

/-! The original Goldilocks context input uniquely encodes the entire retained
parameter record, including query quota and serialized row code. This is a
byte-format identity, not an assumed collision-free hash or Rust refinement. -/
namespace FormalProof4FHE.HasteBoots.GoldContextInput
open NativeBrakedownContext (Parameters)
open NativeGoldBlockCode (Stored)
open NativePrefixCodec (Codec product usize)
open InputIndexedOracle (Input)
noncomputable section

abbrev Fields := NativeUsizeMessage.Usize × NativeUsizeMessage.Usize × NativeUsizeMessage.Usize ×
  NativeUsizeMessage.Usize × NativeUsizeMessage.Usize × NativeUsizeMessage.Usize ×
    NativePrefixCodec.Vector InputIndexedOracle.Byte × Stored

def codec : Codec Fields := product usize (product usize (product usize (product usize (product usize (product usize
  (product NativeByteCodec.bytes NativeGoldBlockCode.codec))))))

def fields (parameters : Parameters Stored) : Fields :=
  (parameters.numVariables,parameters.width,parameters.leftVariables,parameters.queries,
    parameters.code.blockWidth,parameters.code.blocks,NativeGoldBlockCode.domain,parameters.code)

def bytes (parameters : Parameters Stored) : Input :=
  NativeBrakedownContext.domain ++ (NativeByteCodec.bytes.encode NativeBrakedownContext.modulus ++ codec.encode (fields parameters))

theorem input_eq (parameters : Parameters Stored) :
    NativeBrakedownContext.input NativeGoldBlockCode.description.row parameters = some (bytes parameters) := by
  simp only [NativeBrakedownContext.input,NativeBrakedownContext.metadata,NativeGoldBlockCode.description,
    Option.map_some,bytes,fields,codec,NativePrefixCodec.product,NativePrefixCodec.usize,List.append_assoc]

theorem fields_injective : Function.Injective fields := by
  intro left right same
  cases left with
  | mk ln lw ll lq lc =>
    cases right with
    | mk rn rw rl rq rc =>
      simp only [fields,Prod.mk.injEq] at same
      obtain ⟨rfl,rfl,rfl,rfl,_,_,_,rfl⟩ := same
      rfl

theorem bytes_injective : Function.Injective bytes := by
  intro left right same
  unfold bytes at same
  have metadata := List.append_cancel_left same
  have encoded := List.append_cancel_left metadata
  exact fields_injective (codec.encode_injective encoded)

end
end FormalProof4FHE.HasteBoots.GoldContextInput
