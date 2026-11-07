module
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeBackend
@[expose] public section

/-! Literal Goldilocks new_encoded checks and retained parameter fields. The
code is moved into the returned record; no caller code-identity or validity
certificate is an input. Geometry is a ghost observation of the checked sizes.
Rust/checked arithmetic/heap and physical refinement remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldEncodedParameters
open NativeUsizeMessage (Usize)
open NativeGoldBlockCode (Stored description)
open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Geometry)

structure Header where
  numVariables : Usize
  width : Usize
  leftVariables : Usize
  queries : Usize
  deriving DecidableEq

def retain (header : Header) (code : Stored) : Parameters Stored :=
  ⟨header.numVariables,header.width,header.leftVariables,header.queries,code⟩

inductive Error where
  | dimensions | codeShape | tableOverflow | encodedOverflow | linearOverflow | merkleOverflow
  deriving DecidableEq

structure Initialized where
  parameters : Parameters Stored
  geometry : Geometry

def build (header : Header) (code : Stored) : Except Error Initialized :=
  let parameters := retain header code
  if _basic : NativeBrakedownParameters.basic parameters = true then
    if _shape : NativeBrakedownParameters.codeShape description parameters = true then
      let rows := 2^header.leftVariables.val*header.width.val
      if table : 2^header.numVariables.val*header.width.val < 2^64 then
        if encoded : rows < 2^64 ∧ rows*code.blocks.val < 2^64 ∧ rows*code.blocks.val*code.blockWidth.val < 2^64 then
          if linear : rows < 2^64 ∧ rows*header.width.val < 2^64 then
            if tree : 2^(NativeBrakedownParameters.height code.blocks.val) < 2^64 ∧
                2^(NativeBrakedownParameters.height code.blocks.val)*2 < 2^64 then
              have fits : NativeBrakedownParameters.allocations description parameters :=
                ⟨table,encoded.1,encoded.2.1,encoded.2.2,linear.2,tree.1,tree.2⟩
              .ok ⟨parameters,NativeBrakedownParameters.geometry description parameters fits⟩
            else .error .merkleOverflow
          else .error .linearOverflow
        else .error .encodedOverflow
      else .error .tableOverflow
    else .error .codeShape
  else .error .dimensions

structure Spec (header : Header) (code : Stored) (initialized : Initialized) : Prop where
  retained : initialized.parameters = retain header code
  basic : NativeBrakedownParameters.basic initialized.parameters = true
  shape : NativeBrakedownParameters.codeShape description initialized.parameters = true
  fits : NativeBrakedownParameters.allocations description initialized.parameters
  geometry : initialized.geometry = NativeBrakedownParameters.geometry description initialized.parameters fits

theorem build_spec (header : Header) (code : Stored) (initialized : Initialized)
    (executed : build header code = .ok initialized) : Spec header code initialized := by
  unfold build at executed
  dsimp only at executed
  split at executed
  · rename_i basic
    split at executed
    · rename_i shape
      split at executed
      · rename_i table
        split at executed
        · rename_i encoded
          split at executed
          · rename_i linear
            split at executed
            · rename_i tree
              cases executed
              have fits : NativeBrakedownParameters.allocations description (retain header code) :=
                ⟨table,encoded.1,encoded.2.1,encoded.2.2,linear.2,tree.1,tree.2⟩
              exact ⟨rfl,basic,shape,fits,rfl⟩
            · cases executed
          · cases executed
        · cases executed
      · cases executed
    · cases executed
  · cases executed

theorem retained_code (header : Header) (code : Stored) (initialized : Initialized)
    (executed : build header code = .ok initialized) : initialized.parameters.code = code := by
  rw [(build_spec header code initialized executed).retained]
  rfl

theorem legacy_build (header : Header) (code : Stored) (initialized : Initialized)
    (executed : build header code = .ok initialized) :
    NativeBrakedownParameters.build description initialized.parameters = some initialized.geometry := by
  have spec := build_spec header code initialized executed
  rw [spec.geometry]
  exact NativeBrakedownParameters.build_complete description initialized.parameters spec.basic spec.shape spec.fits

theorem message_matches (header : Header) (code : Stored) (initialized : Initialized)
    (executed : build header code = .ok initialized) :
    code.messageLength.val = 2^(initialized.parameters.numVariables.val-initialized.parameters.leftVariables.val) := by
  have shape := (NativeBrakedownParameters.build_spec description initialized.parameters initialized.geometry
    (legacy_build header code initialized executed)).code.1
  rw [retained_code header code initialized executed] at shape
  exact shape

theorem header_fields (header : Header) (code : Stored) (initialized : Initialized)
    (executed : build header code = .ok initialized) :
    initialized.parameters.numVariables = header.numVariables ∧ initialized.parameters.width = header.width ∧
      initialized.parameters.leftVariables = header.leftVariables ∧ initialized.parameters.queries = header.queries := by
  rw [(build_spec header code initialized executed).retained]
  exact ⟨rfl,rfl,rfl,rfl⟩

end FormalProof4FHE.HasteBoots.NativeGoldEncodedParameters
