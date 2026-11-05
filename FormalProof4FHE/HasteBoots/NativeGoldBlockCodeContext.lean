module

public import FormalProof4FHE.HasteBoots.NativeGoldBlockCode

@[expose] public section

/-! The native parameter context includes the complete retained code object.
Structural injectivity concerns hash inputs, not collision resistance or a
refinement of the native adversarial byte decoder. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext

open NativeGoldBlockCode
open NativeUsizeMessage (Usize)
open NativeBrakedownContext (Parameters)
open InputIndexedOracle (Byte Input)

abbrev ContextFields := NativePrefixCodec.Vector Byte × Usize × Usize × Usize × Usize ×
  Usize × Usize × NativePrefixCodec.Vector Byte × Stored

def contextCodec : NativePrefixCodec.Codec ContextFields :=
  NativePrefixCodec.product NativeByteCodec.bytes
    (NativePrefixCodec.product NativePrefixCodec.usize
      (NativePrefixCodec.product NativePrefixCodec.usize
        (NativePrefixCodec.product NativePrefixCodec.usize
          (NativePrefixCodec.product NativePrefixCodec.usize
            (NativePrefixCodec.product NativePrefixCodec.usize
              (NativePrefixCodec.product NativePrefixCodec.usize
                (NativePrefixCodec.product NativeByteCodec.bytes codec)))))))

def contextFields (parameters : Parameters Stored) : ContextFields :=
  (NativeBrakedownContext.modulus,parameters.numVariables,parameters.width,parameters.leftVariables,
    parameters.queries,parameters.code.blockWidth,parameters.code.blocks,domain,parameters.code)

theorem metadata_computed (parameters : Parameters Stored) :
    NativeBrakedownContext.metadata description.row parameters = some (contextCodec.encode (contextFields parameters)) := by
  simp only [NativeBrakedownContext.metadata,description,Option.map_some,contextCodec,contextFields,
    NativePrefixCodec.product,NativePrefixCodec.usize,List.append_assoc]

theorem input_computed (parameters : Parameters Stored) :
    NativeBrakedownContext.input description.row parameters =
      some (NativeBrakedownContext.domain ++ contextCodec.encode (contextFields parameters)) := by
  rw [NativeBrakedownContext.input,metadata_computed,Option.map_some]

/-- Constructed context bytes can never omit the retained modulus, padded
coefficient count or raw domain root, even when those fields share accessors. -/
theorem contextFields_injective : Function.Injective contextFields := by
  intro left right same
  have variableEq := congrArg (fun value : ContextFields => value.2.1) same
  have width := congrArg (fun value : ContextFields => value.2.2.1) same
  have splitEq := congrArg (fun value : ContextFields => value.2.2.2.1) same
  have queries := congrArg (fun value : ContextFields => value.2.2.2.2.1) same
  have code := congrArg (fun value : ContextFields => value.2.2.2.2.2.2.2.2) same
  cases left
  cases right
  simp only [contextFields] at variableEq width splitEq queries code
  cases variableEq
  cases width
  cases splitEq
  cases queries
  cases code
  rfl

theorem input_injective : Function.Injective (NativeBrakedownContext.input description.row) := by
  intro left right same
  rw [input_computed,input_computed] at same
  have bytes := List.append_cancel_left (Option.some.inj same)
  exact contextFields_injective (contextCodec.encode_injective bytes)

/-- A whole constructed metadata record has a structural prefix inverse,
including any following proof bytes. -/
theorem metadata_prefix (parameters : Parameters Stored) (suffix : Input) :
    contextCodec.read (contextCodec.encode (contextFields parameters) ++ suffix) =
      some (contextFields parameters,suffix) := contextCodec.read_encode _ _

end FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext
