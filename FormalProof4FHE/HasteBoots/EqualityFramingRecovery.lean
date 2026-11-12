module
public import FormalProof4FHE.HasteBoots.CallerDerivedIdentityWork
@[expose] public section

/-! The native child initializer and executed lookup/equality prefix supply
scalar-input framing. No decoded future transcript is a caller premise. -/
namespace FormalProof4FHE.HasteBoots.EqualityFramingRecovery
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
noncomputable section

theorem start_framed (world : World) (parent : Transcript)
    (packet : NativeLookupMultiplicityWire.Packet) :
    Framed (NativeSharedLookupChild.startExecute world parent packet).1.2 := by
  obtain ⟨suffix,valid,bytes⟩ := NativeForkAncestry.start_header world parent packet
  exact ⟨_,bytes,valid⟩

theorem prelude_framed {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (n : NativeUsizeMessage.Usize)
    (packet : NativeLookupMultiplicityWire.Packet) (roots : NativePrefixCodec.Vector NativeRootMessage.Digest)
    (lookupFuel equalityFuel : ℕ) (parent : Transcript) (world : World)
    (ready : NativeSharedLookupPrelude.Ready n.val)
    (success : (OracleProgram.run (NativeSharedLookupPrelude.protocol fits requests n packet.groups.values
      roots.val roots.property 7 lookupFuel equalityFuel
      (NativeSharedLookupChild.startExecute world parent packet).1.2) world).run.1 = some ready)
    (rootsFit : (NativeRootMessage.encode roots.val roots.property).length < TranscriptFrame.lengthLimit) :
    Framed ready.equality.transcript := by
  have extended := NativeLookupTranscriptExtension.ready_extends fits requests n packet.groups.values
    roots.val roots.property 7 lookupFuel equalityFuel _ world ready success (by decide +kernel) rootsFit
  exact NativeTranscriptFraming.of_extension (start_framed world parent packet) extended

variable {Memory A : Type}
    {ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening)}
    {allocation : AllocatedFamilyFunctions.Allocation ctx} {program : OracleProgram.Program A}
    {world : World}

theorem ready_framed (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    Framed data.origin.ready.equality.transcript := by
  exact prelude_framed ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
    data.origin.geometry.geometry.1 ctx.proof.multiplicities ctx.proof.roots ctx.lookupFuel ctx.equalityFuel
    _ world data.origin.ready data.origin.prepared (CallerFramedAllocatedJob.domain data).rootsFit

theorem ready_decoded (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    ∃ frames, TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames := by
  obtain ⟨frames,bytes,valid⟩ := ready_framed data
  exact ⟨frames,by rw [bytes]; exact TranscriptFrame.decodeAll_encodeMany frames valid⟩

end
end FormalProof4FHE.HasteBoots.EqualityFramingRecovery
