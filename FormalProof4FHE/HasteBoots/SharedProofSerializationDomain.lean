module
public import FormalProof4FHE.HasteBoots.SharedProofByteCodec
@[expose] public section

/-! Full canonical proof bytes pay for the actual framed components,
including flattening's changed vector header. This establishes allocation
bounds within the model, not Rust deserializer or runtime correspondence. -/
namespace FormalProof4FHE.HasteBoots.SharedProofSerializationDomain
open SharedProofByteCodec (Proof codec)
open NativePrefixCodec (Codec Vector vector)
open NativeLookupRequestWire (Row)
open InputIndexedOracle (Byte)

/-- The payload words of all rows occupy no more space than their row encodings. -/
theorem row_bodies_le (rows : List Row) :
    (rows.flatMap (fun row => row.val.flatMap NativeUsizeMessage.encode)).length ≤
      (rows.flatMap NativeLookupRequestWire.rowCodec.encode).length := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons row tail ih =>
    simp only [List.flatMap_cons,List.length_append]
    change _ ≤ (NativeUsizeMessage.encode ⟨row.val.length,row.property⟩ ++
      row.val.flatMap NativeUsizeMessage.encode).length + _
    simp only [List.length_append]
    omega

/-- Flattening can change the outer count header; no equality of byte sizes is assumed. -/
theorem flattened_le_grouped (packet : NativeLookupMultiplicityWire.Packet) :
    (NativeLookupMultiplicityWire.flattened packet).length ≤
      (NativeLookupMultiplicityWire.grouped packet).length + 9 := by
  have bodies := row_bodies_le packet.groups.val
  have header := NativeUsizeMessage.encode_length
    (⟨packet.flat.val.length,packet.flat.property⟩ : NativeUsizeMessage.Usize)
  have words : packet.flat.val.flatMap NativeUsizeMessage.encode =
      packet.groups.val.flatMap (fun row => row.val.flatMap NativeUsizeMessage.encode) := by
    simp only [NativeLookupMultiplicityWire.Packet.flat,NativeLookupRequestWire.Table.values,
      List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,id_eq]
  change (NativeUsizeMessage.encode ⟨packet.flat.val.length,packet.flat.property⟩ ++
    packet.flat.val.flatMap NativeUsizeMessage.encode).length ≤ _
  rw [List.length_append,words]
  change _ ≤ (NativeUsizeMessage.encode ⟨packet.groups.val.length,packet.groups.property⟩ ++
    packet.groups.val.flatMap NativeLookupRequestWire.rowCodec.encode).length + 9
  simp only [List.length_append]
  omega

/-- A complete proof's other fields, including a real root, cover the header slack. -/
theorem flattened_le_proof (proof : Proof) (nonempty : proof.roots.val ≠ []) :
    (NativeLookupMultiplicityWire.flattened proof.multiplicities).length ≤ (codec.encode proof).length := by
  have flat := flattened_le_grouped proof.multiplicities
  have positive := List.length_pos_iff.mpr nonempty
  have roots := NativeRootMessage.encode_length proof.roots.val proof.roots.property
  rw [SharedProofByteCodec.encode]
  simp only [List.length_append,SharedProofByteCodec.roots_encode]
  omega

/-- Membership is charged to the entire original vector without replacing its index. -/
theorem vector_member_le {A : Type} (itemCodec : Codec A) (values : Vector A) (value : A)
    (member : value ∈ values.val) : (itemCodec.encode value).length ≤ ((vector itemCodec).encode values).length := by
  obtain ⟨before,after,same⟩ := List.mem_iff_append.mp member
  change _ ≤ (NativeUsizeMessage.encode ⟨values.val.length,values.property⟩ ++ values.val.flatMap itemCodec.encode).length
  rw [List.length_append]
  have payload : (itemCodec.encode value).length ≤ (values.val.flatMap itemCodec.encode).length := by
    rw [same]
    simp only [List.flatMap_append,List.flatMap_cons,List.length_append]
    omega
  omega

structure Domain (proof : Proof) : Prop where
  rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit
  algebraFits : (ScalarProofFraming.proofCodec.encode proof.algebra).length < TranscriptFrame.lengthLimit
  groupedFits : (NativeLookupMultiplicityWire.grouped proof.multiplicities).length < TranscriptFrame.lengthLimit
  flatFits : (NativeLookupMultiplicityWire.flattened proof.multiplicities).length < TranscriptFrame.lengthLimit
  terminalFits : (NativeSharedLookupProofData.terminal proof).length < TranscriptFrame.lengthLimit
  sourceResponses : ∀ opening ∈ proof.sourceOpening.val,
    (NativeGoldBatchResponseBinding.payload opening).length < TranscriptFrame.lengthLimit
  helperResponses : ∀ opening ∈ proof.helperOpenings.val,
    (SingleOpeningColumnLaw.payload opening).length < TranscriptFrame.lengthLimit

/-- All these allocation domains follow from one full canonical encoding. -/
theorem of_length (proof : Proof) (nonempty : proof.roots.val ≠ [])
    (fits : (codec.encode proof).length < TranscriptFrame.lengthLimit) : Domain proof := by
  have full := fits
  rw [SharedProofByteCodec.encode] at full
  simp only [List.length_append,SharedProofByteCodec.roots_encode] at full
  have sourceFits : ((vector NativeGoldBatchOpening.codec).encode proof.sourceOpening).length < TranscriptFrame.lengthLimit := by omega
  have helperFits : ((vector NativeGoldPcsOpening.codec).encode proof.helperOpenings).length < TranscriptFrame.lengthLimit := by omega
  refine ⟨by omega,by omega,by omega,lt_of_le_of_lt (flattened_le_proof proof nonempty) fits,?_,?_,?_⟩
  · change (NativeLookupRequestWire.tableCodec.encode proof.sources ++
      (vector NativeScalarBatchWire.goldCodec).encode proof.helpers).length < _
    simp only [List.length_append]
    omega
  · intro opening member
    have encoded := lt_of_le_of_lt (vector_member_le NativeGoldBatchOpening.codec proof.sourceOpening opening member) sourceFits
    change (NativeLookupRequestWire.rowCodec.encode opening.test ++
      (vector NativeLookupRequestWire.rowCodec).encode opening.evaluations).length < _
    rw [NativeGoldBatchOpening.encode] at encoded
    simp only [List.length_append] at encoded ⊢
    omega
  · intro opening member
    have encoded := lt_of_le_of_lt (vector_member_le NativeGoldPcsOpening.codec proof.helperOpenings opening member) helperFits
    change (NativeLookupRequestWire.rowCodec.encode opening.test ++
      NativeLookupRequestWire.rowCodec.encode opening.evaluation).length < _
    rw [NativeGoldPcsOpening.encode] at encoded
    simp only [List.length_append] at encoded ⊢
    omega

theorem of_bytes (proof : Proof) (nonempty : proof.roots.val ≠ []) (source : Vector Byte)
    (parsed : NativeExactCodec.read codec source.val = some proof) : Domain proof := by
  apply of_length proof nonempty
  rw [NativeExactCodec.read_sound codec source.val proof parsed]
  exact source.property

/-- Root nonemptiness is recovered from the actual prelude, not assumed by the byte bridge. -/
theorem job_roots_nonempty {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : InputIndexedOracle.World}
    (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world) : ctx.proof.roots.val ≠ [] := by
  have contract := NativeSharedLookupPrelude.protocol_contract ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.values.roots ctx.proof.roots.property
    7 ctx.lookupFuel ctx.equalityFuel _ world data.origin.ready data.origin.prepared
  have count := contract.rootCount
  change ctx.proof.roots.val.length = data.origin.ready.jobs.length at count
  intro empty
  rw [empty,List.length_nil] at count
  have inside := data.index.isLt
  omega

theorem job_domain {Memory A : Type} {ctx : NativeGoldHelperVerification.Context (Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A} {world : InputIndexedOracle.World}
    (data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world) (source : Vector Byte)
    (parsed : NativeExactCodec.read codec source.val = some ctx.proof) : Domain ctx.proof :=
  of_bytes ctx.proof (job_roots_nonempty data) source parsed

end FormalProof4FHE.HasteBoots.SharedProofSerializationDomain
