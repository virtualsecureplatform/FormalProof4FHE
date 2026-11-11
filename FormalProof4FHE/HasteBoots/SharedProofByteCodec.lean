module
public import FormalProof4FHE.HasteBoots.RecoveredParentIdentityWork
@[expose] public section

/-! Canonical analysis serialization of all seven fields of the native
Goldilocks shared lookup proof. The flat multiplicity allocation is checked
when reconstructing the typed proof. Rust/serde and resource refinement are
separate obligations; this reader is not that refinement. -/
namespace FormalProof4FHE.HasteBoots.SharedProofByteCodec
open NativePrefixCodec (Codec Vector product vector)
open NativeLookupRequestWire (Table tableCodec)
open NativeRootMessage (Digest)
open NativeFieldWire (GoldExtension)
open NativeGoldPcsOpening (Opening)
open InputIndexedOracle (Input)

abbrev Proof := NativeSharedLookupProofData.Proof Opening (Vector NativeGoldBatchOpening.Opening)
abbrev Fields := Table × Vector Digest × NativeScalarBatchPreflight.Proof × Table ×
  Vector GoldExtension × Vector NativeGoldBatchOpening.Opening × Vector Opening

def fieldsCodec : Codec Fields := product tableCodec (product (vector NativeByteCodec.digest)
  (product ScalarProofFraming.proofCodec (product tableCodec (product (vector NativeScalarBatchWire.goldCodec)
    (product (vector NativeGoldBatchOpening.codec) (vector NativeGoldPcsOpening.codec))))))

def fields (proof : Proof) : Fields :=
  (proof.multiplicities.groups,proof.roots,proof.algebra,proof.sources,proof.helpers,proof.sourceOpening,proof.helperOpenings)

def assemble (data : Fields) (fits : data.1.values.flatten.length < 2^64) : Proof :=
  ⟨⟨data.1,fits⟩,data.2.1,data.2.2.1,data.2.2.2.1,data.2.2.2.2.1,data.2.2.2.2.2.1,data.2.2.2.2.2.2⟩

def codec : Codec Proof where
  encode := fun proof => fieldsCodec.encode (fields proof)
  read := fun input => (fieldsCodec.read input).bind (fun result =>
    if fits : result.1.1.values.flatten.length < 2^64 then some (assemble result.1 fits,result.2) else none)
  read_encode := by
    intro proof suffix
    rw [fieldsCodec.read_encode,Option.bind_some]
    split
    · rfl
    · rename_i rejected
      exact False.elim (rejected proof.multiplicities.flatFits)

theorem encode (proof : Proof) : codec.encode proof =
    NativeLookupMultiplicityWire.grouped proof.multiplicities ++
      ((vector NativeByteCodec.digest).encode proof.roots ++
        (ScalarProofFraming.proofCodec.encode proof.algebra ++
          (tableCodec.encode proof.sources ++
            ((vector NativeScalarBatchWire.goldCodec).encode proof.helpers ++
              ((vector NativeGoldBatchOpening.codec).encode proof.sourceOpening ++
                (vector NativeGoldPcsOpening.codec).encode proof.helperOpenings))))) := rfl

theorem roots_encode (roots : Vector Digest) :
    (vector NativeByteCodec.digest).encode roots = NativeRootMessage.encode roots.val roots.property := rfl

theorem read_prefix (proof : Proof) (suffix : Input) :
    codec.read (codec.encode proof ++ suffix) = some (proof,suffix) := codec.read_encode _ _

theorem exact_read (proof : Proof) : NativeExactCodec.read codec (codec.encode proof) = some proof :=
  NativeExactCodec.read_encode codec proof

theorem injective : Function.Injective codec.encode := codec.encode_injective

/-- The source witness is exactly a bound on the full canonical encoding. -/
theorem bounded_source_iff (proof : Proof) :
    (∃ source : Vector InputIndexedOracle.Byte, NativeExactCodec.read codec source.val = some proof) ↔
      (codec.encode proof).length < 2^64 := by
  constructor
  · rintro ⟨source,parsed⟩
    rw [NativeExactCodec.read_sound codec source.val proof parsed]
    exact source.property
  · intro fits
    exact ⟨⟨codec.encode proof,fits⟩,exact_read proof⟩

end FormalProof4FHE.HasteBoots.SharedProofByteCodec
