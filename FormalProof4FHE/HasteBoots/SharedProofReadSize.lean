module
public import FormalProof4FHE.HasteBoots.PrefixCodecReadSize
public import FormalProof4FHE.HasteBoots.SerializedIdentityWork
@[expose] public section

/-! Every successful structural shared-proof read has a canonical encoding
no larger than its consumed input, including wider varint spellings.
This covers the specified reader; Rust decoder/error/resource refinement
remains separate. -/
namespace FormalProof4FHE.HasteBoots.SharedProofReadSize
open NativePrefixCodec (vector)
open PrefixCodecReadSize (Nonexpanding)
open SharedProofByteCodec (Proof codec)
open InputIndexedOracle (Input Byte)

theorem row : Nonexpanding NativeLookupRequestWire.rowCodec := by
  intro input value rest found
  rw [NativeLookupRequestWire.rowCodec_read_eq_reference] at found
  exact PrefixCodecReadSize.vector _ PrefixCodecReadSize.usize input value rest found

theorem gold : Nonexpanding NativeScalarBatchWire.goldCodec :=
  PrefixCodecReadSize.fixed _ PrefixCodecReadSize.usize 3 (by decide)

theorem message : Nonexpanding NativeScalarBatchWire.messageCodec :=
  PrefixCodecReadSize.transport _ _ (PrefixCodecReadSize.vector _ gold)

theorem scalar : Nonexpanding ScalarProofFraming.proofCodec :=
  PrefixCodecReadSize.vector _ (PrefixCodecReadSize.vector _ message)

theorem column : Nonexpanding NativeGoldColumnAuthentication.columnCodec :=
  PrefixCodecReadSize.transport _ _ (PrefixCodecReadSize.product _ _ row
    (PrefixCodecReadSize.vector _ (PrefixCodecReadSize.bytes_fixed 64)))

theorem single : Nonexpanding NativeGoldPcsOpening.codec :=
  PrefixCodecReadSize.transport _ _ (PrefixCodecReadSize.product _ _ row
    (PrefixCodecReadSize.product _ _ row (PrefixCodecReadSize.vector _ column)))

theorem batch : Nonexpanding NativeGoldBatchOpening.codec :=
  PrefixCodecReadSize.transport _ _ (PrefixCodecReadSize.product _ _ row
    (PrefixCodecReadSize.product _ _ (PrefixCodecReadSize.vector _ row) (PrefixCodecReadSize.vector _ column)))

theorem fields : Nonexpanding SharedProofByteCodec.fieldsCodec :=
  PrefixCodecReadSize.product _ _ (PrefixCodecReadSize.vector _ row)
    (PrefixCodecReadSize.product _ _ (PrefixCodecReadSize.vector _ (PrefixCodecReadSize.bytes_fixed 64))
      (PrefixCodecReadSize.product _ _ scalar (PrefixCodecReadSize.product _ _ (PrefixCodecReadSize.vector _ row)
        (PrefixCodecReadSize.product _ _ (PrefixCodecReadSize.vector _ gold)
          (PrefixCodecReadSize.product _ _ (PrefixCodecReadSize.vector _ batch) (PrefixCodecReadSize.vector _ single))))))

theorem proof : Nonexpanding codec := by
  intro input value rest found
  obtain ⟨⟨data,tail⟩,parsed,checked⟩ := Option.bind_eq_some_iff.mp found
  split at checked
  next fits =>
    have same := Option.some.inj checked
    cases same
    exact fields input data tail parsed
  next => contradiction

/-- The bound does not require canonical source bytes or an empty suffix. -/
theorem canonical_fits (source : NativePrefixCodec.Vector Byte) (value : Proof) (rest : Input)
    (parsed : codec.read source.val = some (value,rest)) :
    (codec.encode value).length < TranscriptFrame.lengthLimit := by
  have bound := proof source.val value rest parsed
  have fits := source.property
  change (codec.encode value).length < 2^64
  omega

theorem canonical_source (source : NativePrefixCodec.Vector Byte) (value : Proof) (rest : Input)
    (parsed : codec.read source.val = some (value,rest)) :
    ∃ canonical : NativePrefixCodec.Vector Byte, NativeExactCodec.read codec canonical.val = some value := by
  exact ⟨⟨codec.encode value,canonical_fits source value rest parsed⟩,SharedProofByteCodec.exact_read value⟩

/-- Consume a full structural packet without imposing canonical spelling. -/
def readAll (input : Input) : Option Proof :=
  (codec.read input).bind (fun result => if result.2 = [] then some result.1 else none)

theorem readAll_sound (input : Input) (value : Proof) (parsed : readAll input = some value) :
    codec.read input = some (value,[]) := by
  obtain ⟨⟨actual,rest⟩,found,checked⟩ := Option.bind_eq_some_iff.mp parsed
  split at checked
  next empty =>
    have same := Option.some.inj checked
    cases same
    have nil : rest = [] := empty
    rw [nil] at found
    exact found
  next => contradiction

theorem readAll_iff (input : Input) (value : Proof) :
    readAll input = some value ↔ codec.read input = some (value,[]) := by
  constructor
  · exact readAll_sound input value
  · intro parsed
    unfold readAll
    rw [parsed,Option.bind_some]
    rfl

theorem readAll_encode (value : Proof) : readAll (codec.encode value) = some value := by
  unfold readAll
  have parsed := codec.read_encode value []
  rw [List.append_nil] at parsed
  rw [parsed,Option.bind_some]
  rfl

end FormalProof4FHE.HasteBoots.SharedProofReadSize
