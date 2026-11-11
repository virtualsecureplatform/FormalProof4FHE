module
public import FormalProof4FHE.HasteBoots.LookupBatchReceiptOrder
public import FormalProof4FHE.HasteBoots.EqualityReceiptOrder
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! The successful native shared-lookup prelude exposes exactly the original
completed lookup draw sequence followed by the original equality draw sequence.
No frame membership or receipt list is supplied by the caller. -/
namespace FormalProof4FHE.HasteBoots.LookupPreludeReceiptOrder
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open ReceiptFrameView (frames frame)
open OracleProgram (run)
noncomputable section

theorem protocol {count : ℕ} (fits : count ≤ 2^64) (requests : Fin count → NativeSharedLookupStatement.Request)
    (n : NativeUsizeMessage.Usize) (multiplicities : List (List NativeFieldRepresentation.GoldWord))
    (roots : List NativeRootMessage.Digest) (rootFits : roots.length < 2^64) (w lookupFuel equalityFuel : ℕ)
    (state : Transcript) (world : World) (ready : NativeSharedLookupPrelude.Ready n.val)
    (old : ReceiptSequence.Framed state)
    (descriptorFits : (NativeExtensionDescriptor.descriptor 3 w).length < TranscriptFrame.lengthLimit)
    (rootsFit : (NativeRootMessage.encode roots rootFits).length < TranscriptFrame.lengthLimit)
    (success : (run (NativeSharedLookupPrelude.protocol fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state) world).run.1 = some ready) :
    frames ready.equality.transcript.input = frames state.input ++
      (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis w lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) state) world).1.completed.flatMap
          (fun entry => entry.selection.draws.map (fun draw => frame world draw.coefficients.phase)) ++
      ready.machine.draws.map (fun draw => frame world draw.coefficients.phase) := by
  have batch := LookupBatchReceiptOrder.execute NativeExtensionFields.goldilocksBasis w lookupFuel _ world _ descriptorFits
    (LookupBatchReceiptOrder.initial (NativeLookupBatch.schedule fits (fun i => (requests i).sampling)) state world old)
  have contract := NativeSharedLookupPrelude.protocol_contract fits requests n multiplicities roots rootFits w lookupFuel equalityFuel state world ready success
  obtain ⟨transcript,finished,machine,_⟩ := contract.lookup
  have batchFramed := batch.1
  have batchSequence := batch.2.2
  simp only [LookupReceiptBatchLineage.current,finished] at batchFramed
  simp only [LookupReceiptBatchLineage.current,LookupBatchReceiptOrder.activeFrames,finished,List.append_nil] at batchSequence
  have bound := ReceiptSequence.absorb transcript 1 NativeLookupEquality.rootsLabel (NativeRootMessage.encode roots rootFits) batchFramed
    ⟨by change (NativeTranscript.utf8 "shared lookup helper roots").length < _; unfold NativeTranscript.utf8; decide +kernel,rootsFit⟩ (by decide)
  have equality := EqualityReceiptOrder.execute NativeExtensionFields.goldilocksBasis w equalityFuel _ world _ descriptorFits
    (EqualityReceiptOrder.initial n.val transcript roots rootFits world bound.1)
  have actual : EqualityReceiptOrder.Ordered world (frames (NativeLookupEquality.bindRoots transcript roots rootFits).input) ready.machine := by
    rw [machine,NativeLookupEquality.request,NativeLookupEquality.run_steps]
    exact equality
  have sequence := actual.2.2.2
  rw [← contract.child] at sequence
  rw [sequence]
  change frames (NativeTranscript.absorb transcript 1 NativeLookupEquality.rootsLabel (NativeRootMessage.encode roots rootFits)).input ++ _ = _
  rw [bound.2,batchSequence]
  rfl

end
end FormalProof4FHE.HasteBoots.LookupPreludeReceiptOrder
