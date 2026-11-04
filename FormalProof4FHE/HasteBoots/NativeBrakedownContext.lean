module

public import FormalProof4FHE.HasteBoots.NativeByteCodec
public import FormalProof4FHE.HasteBoots.NativeLookupBindGeometry
public import FormalProof4FHE.HasteBoots.OracleProgram
import all Init.Data.String.Defs

@[expose] public section

/-!
# Native Goldilocks Brakedown parameter-context computation

Trusted row-code accessors and serialization are explicit inputs. The same
parameter object supplies numeric geometry and context metadata. The digest
is computed by the common hash oracle, never supplied as a certificate.
Row-code serialization/Rust refinement and parameter validity remain open.
-/
namespace FormalProof4FHE.HasteBoots.NativeBrakedownContext

open InputIndexedOracle (Input Byte World)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open OracleProgram (Program)

structure RowDescription (Code : Type) where
  blockWidth : Code → Usize
  blocks : Code → Usize
  domain : Code → NativePrefixCodec.Vector Byte
  serialize : Code → Option Input

structure Parameters (Code : Type) where
  numVariables : Usize
  width : Usize
  leftVariables : Usize
  queries : Usize
  code : Code

def Parameters.geometry {C : Type} (parameters : Parameters C) : NativeLookupBindGeometry.Parameters :=
  ⟨parameters.numVariables,parameters.width⟩

def modulus : NativePrefixCodec.Vector Byte :=
  ⟨NativeTranscript.utf8 "18446744069414584321",by decide +kernel⟩

def domain : Input := NativeTranscript.utf8 "HasteBoots/mw-parameters/v2"

/-- Serde tuple concatenation: decimal field modulus, six usize fields,
row-code domain bytes, then the complete serialized code, with no extra
wrapper around that final code. -/
def metadata {C : Type} (row : RowDescription C) (parameters : Parameters C) : Option Input :=
  (row.serialize parameters.code).map (fun code =>
    NativeByteCodec.bytes.encode modulus ++
    NativeUsizeMessage.encode parameters.numVariables ++ NativeUsizeMessage.encode parameters.width ++
    NativeUsizeMessage.encode parameters.leftVariables ++ NativeUsizeMessage.encode parameters.queries ++
    NativeUsizeMessage.encode (row.blockWidth parameters.code) ++ NativeUsizeMessage.encode (row.blocks parameters.code) ++
    NativeByteCodec.bytes.encode (row.domain parameters.code) ++ code)

def input {C : Type} (row : RowDescription C) (parameters : Parameters C) : Option Input :=
  (metadata row parameters).map (fun bytes => domain ++ bytes)

def context {C : Type} (row : RowDescription C) (parameters : Parameters C) : Program (Option Digest) :=
  match input row parameters with
  | none => .pure none
  | some bytes => .hash bytes (fun digest => .pure (some digest))

theorem context_success {C : Type} (row : RowDescription C) (parameters : Parameters C) (bytes : Input)
    (serialized : input row parameters = some bytes) (world : World) :
    (OracleProgram.run (context row parameters) world).run =
      (some (InputIndexedOracle.sha512 world bytes),[NativeTranscript.Observation.hash bytes (List.ofFn (InputIndexedOracle.sha512 world bytes))]) := by
  simp only [context,serialized,OracleProgram.run,ObservationReplay.hash]
  rfl

theorem context_failure {C : Type} (row : RowDescription C) (parameters : Parameters C)
    (rejected : input row parameters = none) (world : World) :
    (OracleProgram.run (context row parameters) world).run = (none,[]) := by
  simp only [context,rejected,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

end FormalProof4FHE.HasteBoots.NativeBrakedownContext
