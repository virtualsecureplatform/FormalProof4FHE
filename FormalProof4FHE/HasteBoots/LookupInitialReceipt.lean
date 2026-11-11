module
public import FormalProof4FHE.HasteBoots.ReceiptSequence
public import FormalProof4FHE.HasteBoots.NativeForkAncestry
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.NativeSharedLookupChild
@[expose] public section

/-! The original typed child starts with exactly one receipt: its native
zero-count extension identity. The count is independent of the oracle world. -/
namespace FormalProof4FHE.HasteBoots.LookupInitialReceipt
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript utf8)
open ReceiptFrameView (frames frame)
noncomputable section

theorem fork (world : World) (parent : Transcript) (label context : Input)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (contextFits : context.length < TranscriptFrame.lengthLimit) :
    ReceiptSequence.Framed (NativeTranscript.forkChild world parent label context).run.1.2 ∧
      frames (NativeTranscript.forkChild world parent label context).run.1.2.input = [] := by
  have bytes := NativeChildSeedView.forkChild_input world parent label context
  have valid := NativeChildSeedView.seededFrames_valid parent.profile label context
    (InputIndexedOracle.block world (NativeTranscript.requestInput (NativeTranscript.absorb parent 6 label context)
      (utf8 "classical child seed") 64) 0 64) labelFits contextFits
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  exact ⟨⟨_,decoded⟩,by simp [frames,decoded,NativeChildSeedView.seededFrames]⟩

theorem identity (p degree w : ℕ) (world : World) (child : Transcript) (old : ReceiptSequence.Framed child)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    ReceiptSequence.Framed (TypedTranscriptChild.identityExecute p degree w world child).1 ∧
      (frames (TypedTranscriptChild.identityExecute p degree w world child).1.input).length = (frames child.input).length + 1 := by
  have kind := ReceiptSequence.absorb child 1 (utf8 "field challenge kind") (utf8 "extension vector") old
    ⟨by unfold utf8; decide +kernel,by unfold utf8; decide +kernel⟩ (by decide)
  have basis := ReceiptSequence.absorb _ 1 (utf8 "extension basis") (NativeExtensionDescriptor.descriptor degree w) kind.1
    ⟨by change (utf8 "extension basis").length < _; unfold utf8; decide +kernel,descriptorFits⟩ (by decide)
  have requested := ReceiptSequence.begin_field (NativeExtensionRequest.prepare child degree w) (utf8 "typed extension identity") p 0 basis.1
    (by unfold utf8; decide +kernel)
  have finished := ReceiptSequence.finish (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
    (utf8 "typed extension identity") p 0).run.1 world requested.1 (by change (utf8 "typed extension identity").length < _; unfold utf8; decide +kernel)
  refine ⟨finished.1,?_⟩
  change (frames (NativeTranscript.finishField world (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
    (utf8 "typed extension identity") p 0).run.1).run.1.input).length = _
  have prepared : frames (NativeExtensionRequest.prepare child degree w).input = frames child.input := basis.2.trans kind.2
  rw [finished.2,requested.2,prepared,List.length_append,List.length_singleton]

theorem start (world : World) (parent : Transcript) (packet : NativeLookupMultiplicityWire.Packet) :
    ReceiptSequence.Framed (NativeSharedLookupChild.startExecute world parent packet).1.2 ∧
      (frames (NativeSharedLookupChild.startExecute world parent packet).1.2.input).length = 1 := by
  have seeded := fork world (NativeSharedLookupChild.prepare parent packet) NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
    (by change (utf8 "classical extension lookup child v1").length < _; unfold utf8; decide +kernel)
    (by change (utf8 "packed extension tuple lookup").length < _; unfold utf8; decide +kernel)
  have typed := identity NativeFields.goldilocksModulus 3 7 world _ seeded.1 (by decide +kernel)
  refine ⟨typed.1,?_⟩
  change (frames (TypedTranscriptChild.identityExecute NativeFields.goldilocksModulus 3 7 world
    (NativeTranscript.forkChild world (NativeSharedLookupChild.prepare parent packet) NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext).run.1.2).1.input).length = 1
  rw [typed.2,seeded.2]
  rfl

end
end FormalProof4FHE.HasteBoots.LookupInitialReceipt
