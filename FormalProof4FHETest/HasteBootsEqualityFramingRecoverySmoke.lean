module
import all FormalProof4FHE.HasteBoots.ExecutionDerivedIdentityWork

namespace HasteBootsEqualityFramingRecoverySmoke
open FormalProof4FHE.HasteBoots
open NativePrefixCodec (Vector)
open OracleProgram (run)
noncomputable section

def world : InputIndexedOracle.World := fun _ => 0
def malformedParent : NativeTranscript.Transcript := ⟨[255],fun _ => 0⟩
def packet : NativeLookupMultiplicityWire.Packet := ⟨⟨[⟨[],by decide⟩],by decide⟩,by decide⟩
def child := (NativeSharedLookupChild.startExecute world malformedParent packet).1.2

theorem parent_rejected : TranscriptFrame.decodeAll malformedParent.input = none := by decide +kernel

theorem child_framed : NativeTranscriptFraming.Framed child :=
  EqualityFramingRecovery.start_framed world malformedParent packet

theorem child_decodes : (TranscriptFrame.decodeAll child.input).isSome = true :=
  (NativeTranscriptFraming.framed_iff_decode child).mp child_framed

def roots : Vector NativeRootMessage.Digest := ⟨[fun _ => 1,fun _ => 2],by decide⟩
def equality := (run (NativeLookupEquality.request NativeExtensionFields.goldilocksBasis 7 0 4
  child roots.val roots.property) world).run.1

theorem two_equality_points :
    (NativeGoldLookupEquality.finish equality).map (fun result => result.points.map List.length) = some [0,0] := by decide +kernel

theorem equality_framed : NativeTranscriptFraming.Framed equality.transcript := by
  have rootExtension := NativeLookupTranscriptExtension.bind_roots child roots.val roots.property (by decide +kernel)
  have preserved := NativeLookupTranscriptExtension.equality_request NativeExtensionFields.goldilocksBasis 7 0 4
    child roots.val roots.property world (by decide +kernel)
  exact NativeTranscriptFraming.of_extension child_framed (rootExtension.trans preserved.1)

def emptyPacket : NativeLookupMultiplicityWire.Packet := ⟨⟨[],by decide⟩,by decide⟩
def emptyChild := (NativeSharedLookupChild.startExecute world malformedParent emptyPacket).1.2

def preparation := (run (NativeSharedLookupPrelude.protocol (by decide : 0 ≤ 2^64)
  Fin.elim0 ⟨0,by decide⟩ [] [] (by decide) 7 1 0 emptyChild) world).run.1

theorem preparation_present : preparation.isSome = true := by decide +kernel

def ready := preparation.get preparation_present

theorem prepared : (run (NativeSharedLookupPrelude.protocol (by decide : 0 ≤ 2^64)
    Fin.elim0 ⟨0,by decide⟩ [] [] (by decide) 7 1 0 emptyChild) world).run.1 = some ready :=
  (Option.some_get preparation_present).symm

theorem executed_ready_framed : NativeTranscriptFraming.Framed ready.equality.transcript :=
  EqualityFramingRecovery.prelude_framed (by decide) Fin.elim0 ⟨0,by decide⟩
    emptyPacket ⟨[],by decide⟩ 1 0 malformedParent world ready prepared (by decide +kernel)

theorem executed_ready_decodes : (TranscriptFrame.decodeAll ready.equality.transcript.input).isSome = true :=
  (NativeTranscriptFraming.framed_iff_decode _).mp executed_ready_framed

theorem empty_statement_rejected : NativeScalarBatchPreflight.dimensions ready.statement = false := by decide +kernel

theorem missing_job_rejected :
    (run (NativeSharedLookupPrelude.protocol (by decide : 0 ≤ 2^64)
      Fin.elim0 ⟨0,by decide⟩ [] roots.val roots.property 7 1 0 emptyChild) world).run.1 = none := by decide +kernel

theorem insufficient_prefix :
    (run (NativeSharedLookupPrelude.protocol (by decide : 0 ≤ 2^64)
      Fin.elim0 ⟨0,by decide⟩ [] [] (by decide) 7 0 0 emptyChild) world).run.1 = none := by decide +kernel

end
end HasteBootsEqualityFramingRecoverySmoke
