module

public import FormalProof4FHE.HasteBoots.NativePrefixCodec
public import FormalProof4FHE.HasteBoots.NativeFieldWire
import all Init.Data.String.Defs

@[expose] public section

/-!
# Exact Goldilocks scalar-batch statement and round-message payloads

Bincode's tuple/struct fields concatenate in declaration order. Each Vec or
slice has its own usize count; each Goldilocks extension has its degree-three
sequence prefix and three raw u64 words. These payload encoders do not
replace the native preflight or implement the full proof-byte decoder.
-/

namespace FormalProof4FHE.HasteBoots.NativeScalarBatchWire

open NativePrefixCodec NativeFieldWire
open NativeUsizeMessage (Usize)
open InputIndexedOracle (Input)

structure Info where
  maxMultiplicands : Usize
  numVariables : Usize
  deriving DecidableEq

structure Message where
  evaluations : Vector GoldExtension
  deriving DecidableEq

structure Statement where
  infos : Vector Info
  claims : Vector GoldExtension
  deriving DecidableEq

structure RoundPacket where
  round : Usize
  messages : Vector Message
  deriving DecidableEq

def infoEquiv : (Usize × Usize) ≃ Info where
  toFun := fun pair => ⟨pair.1, pair.2⟩
  invFun := fun info => (info.maxMultiplicands, info.numVariables)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def messageEquiv : Vector GoldExtension ≃ Message where
  toFun := Message.mk
  invFun := Message.evaluations
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def statementEquiv : (Vector Info × Vector GoldExtension) ≃ Statement where
  toFun := fun pair => ⟨pair.1, pair.2⟩
  invFun := fun statement => (statement.infos, statement.claims)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def roundEquiv : (Usize × Vector Message) ≃ RoundPacket where
  toFun := fun pair => ⟨pair.1, pair.2⟩
  invFun := fun packet => (packet.round, packet.messages)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def goldCodec : Codec GoldExtension := fixed usize 3 (by decide)
def infoCodec : Codec Info := transport (product usize usize) infoEquiv
def messageCodec : Codec Message := transport (vector goldCodec) messageEquiv
def statementCodec : Codec Statement :=
  transport (product (vector infoCodec) (vector goldCodec)) statementEquiv
def roundCodec : Codec RoundPacket := transport (product usize (vector messageCodec)) roundEquiv

theorem gold_encode (value : GoldExtension) : goldCodec.encode value = NativeFieldWire.goldExtension value := rfl

theorem info_encode (value : Info) : infoCodec.encode value =
    NativeUsizeMessage.encode value.maxMultiplicands ++ NativeUsizeMessage.encode value.numVariables := rfl

theorem statement_encode (value : Statement) : statementCodec.encode value =
    usize.encode ⟨value.infos.val.length, value.infos.property⟩ ++ value.infos.val.flatMap infoCodec.encode ++
      (usize.encode ⟨value.claims.val.length, value.claims.property⟩ ++
        value.claims.val.flatMap NativeFieldWire.goldExtension) := rfl

theorem message_encode (value : Message) : messageCodec.encode value =
    usize.encode ⟨value.evaluations.val.length, value.evaluations.property⟩ ++
      value.evaluations.val.flatMap NativeFieldWire.goldExtension := rfl

theorem round_encode (value : RoundPacket) : roundCodec.encode value =
    NativeUsizeMessage.encode value.round ++
      (usize.encode ⟨value.messages.val.length, value.messages.property⟩ ++
        value.messages.val.flatMap messageCodec.encode) := rfl

theorem statement_roundtrip (value : Statement) (suffix : Input) :
    statementCodec.read (statementCodec.encode value ++ suffix) = some (value, suffix) :=
  statementCodec.read_encode value suffix

theorem round_roundtrip (value : RoundPacket) (suffix : Input) :
    roundCodec.read (roundCodec.encode value ++ suffix) = some (value, suffix) :=
  roundCodec.read_encode value suffix

theorem statement_injective : Function.Injective statementCodec.encode := statementCodec.encode_injective

theorem round_injective : Function.Injective roundCodec.encode := roundCodec.encode_injective

def statementLabel : Input := NativeTranscript.utf8 "independent scalar sumcheck batch v1"
def roundLabel : Input := NativeTranscript.utf8 "scalar batch round messages"
def challengeLabel : Input := NativeTranscript.utf8 "scalar batch common challenge"

def bindStatement (transcript : NativeTranscript.Transcript) (value : Statement) : NativeTranscript.Transcript :=
  NativeTranscript.appendBytes transcript statementLabel (statementCodec.encode value)

def bindRound (transcript : NativeTranscript.Transcript) (value : RoundPacket) : NativeTranscript.Transcript :=
  NativeTranscript.appendBytes transcript roundLabel (roundCodec.encode value)

/-- Well-sized statement payloads bind injectively in the actual framed
input. No collision-freedom assertion about oracle outputs is used. -/
theorem bindStatement_injective (transcript : NativeTranscript.Transcript) (left right : Statement)
    (leftFits : (statementCodec.encode left).length < TranscriptFrame.lengthLimit)
    (rightFits : (statementCodec.encode right).length < TranscriptFrame.lengthLimit)
    (same : (bindStatement transcript left).input = (bindStatement transcript right).input) : left = right := by
  change transcript.input ++ TranscriptFrame.encode ⟨1, statementLabel, statementCodec.encode left⟩ =
    transcript.input ++ TranscriptFrame.encode ⟨1, statementLabel, statementCodec.encode right⟩ at same
  have bytes := List.append_cancel_left same
  have labelFits : statementLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have frame := TranscriptFrame.encode_injective _ _ ⟨labelFits, leftFits⟩ ⟨labelFits, rightFits⟩ bytes
  exact statement_injective (congrArg TranscriptFrame.Frame.message frame)

theorem bindRound_injective (transcript : NativeTranscript.Transcript) (left right : RoundPacket)
    (leftFits : (roundCodec.encode left).length < TranscriptFrame.lengthLimit)
    (rightFits : (roundCodec.encode right).length < TranscriptFrame.lengthLimit)
    (same : (bindRound transcript left).input = (bindRound transcript right).input) : left = right := by
  change transcript.input ++ TranscriptFrame.encode ⟨1, roundLabel, roundCodec.encode left⟩ =
    transcript.input ++ TranscriptFrame.encode ⟨1, roundLabel, roundCodec.encode right⟩ at same
  have bytes := List.append_cancel_left same
  have labelFits : roundLabel.length < TranscriptFrame.lengthLimit := by decide +kernel
  have frame := TranscriptFrame.encode_injective _ _ ⟨labelFits, leftFits⟩ ⟨labelFits, rightFits⟩ bytes
  exact round_injective (congrArg TranscriptFrame.Frame.message frame)

end FormalProof4FHE.HasteBoots.NativeScalarBatchWire
