module
public import FormalProof4FHE.HasteBoots.LookupCompressionReceipt
public import FormalProof4FHE.HasteBoots.LookupJobReceiptPrefix
public import FormalProof4FHE.HasteBoots.LookupBatchReceiptLabels
public import FormalProof4FHE.HasteBoots.LookupInitialReceipt
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.NativeSharedLookupChild
import all Init.Data.String.Defs
@[expose] public section

/-! Compression receipt counts identify job boundaries without counting
rejected reciprocal trials. The original typed-child identity adds no marker. -/
namespace FormalProof4FHE.HasteBoots.LookupCompressionCount
open InputIndexedOracle (Input World)
open NativeTranscript (Transcript utf8)
open ReceiptFrameView (frames frame)
open NativeLookupChallenge (hashLabel reciprocalLabel)
noncomputable section

def count (entries : List TranscriptFrame.Frame) : ℕ :=
  (entries.filter (fun entry => entry.label = hashLabel)).length

def fromInput (input : Input) : ℕ := count (frames input)

theorem append (left right : List TranscriptFrame.Frame) : count (left ++ right) = count left + count right := by
  simp only [count,List.filter_append,List.length_append]

theorem group {K : Type} (world : World) (draws : List (NativeLookupChallenge.Draw K))
    (labels : LookupReceiptLabels.Group draws) :
    count (draws.map (fun draw => frame world draw.coefficients.phase)) = 1 := by
  obtain ⟨first,rest,rfl,head,tail⟩ := labels
  have filtered := LookupCompressionReceipt.tail_filter world rest tail
  have firstLabel : (frame world first.coefficients.phase).label = hashLabel := head
  simp only [count,List.map_cons,List.filter_cons,firstLabel,decide_true,ite_true,filtered,List.length_singleton]

theorem emitted {p : ℕ} {K : Type} (world : World) (entries : List (NativeLookupBatch.Completed p K))
    (labels : ∀ entry ∈ entries, LookupReceiptLabels.Group entry.selection.draws) :
    count (LookupJobReceiptPrefix.emitted world entries) = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rw [LookupJobReceiptPrefix.emitted,List.flatMap_cons,append,group world _ (labels entry (List.mem_cons_self))]
    have restCount := ih (fun entry present => labels entry (List.mem_cons_of_mem _ present))
    change 1 + count (LookupJobReceiptPrefix.emitted world rest) = rest.length+1
    rw [restCount]
    omega

theorem identity (p degree w : ℕ) (world : World) (child : Transcript) (old : ReceiptSequence.Framed child)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    count (frames (TypedTranscriptChild.identityExecute p degree w world child).1.input) = count (frames child.input) := by
  have kind := ReceiptSequence.absorb child 1 (utf8 "field challenge kind") (utf8 "extension vector") old
    ⟨by unfold utf8; decide +kernel,by unfold utf8; decide +kernel⟩ (by decide)
  have basis := ReceiptSequence.absorb _ 1 (utf8 "extension basis") (NativeExtensionDescriptor.descriptor degree w) kind.1
    ⟨by change (utf8 "extension basis").length < _; unfold utf8; decide +kernel,descriptorFits⟩ (by decide)
  have requested := ReceiptSequence.begin_field (NativeExtensionRequest.prepare child degree w) (utf8 "typed extension identity") p 0 basis.1
    (by unfold utf8; decide +kernel)
  have finished := ReceiptSequence.finish (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
    (utf8 "typed extension identity") p 0).run.1 world requested.1 (by change (utf8 "typed extension identity").length < _; unfold utf8; decide +kernel)
  have prepared : frames (NativeExtensionRequest.prepare child degree w).input = frames child.input := basis.2.trans kind.2
  change count (frames (NativeTranscript.finishField world (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
    (utf8 "typed extension identity") p 0).run.1).run.1.input) = _
  rw [finished.2,requested.2,prepared,append]
  have distinct : utf8 "typed extension identity" ≠ hashLabel := by unfold hashLabel utf8; decide +kernel
  have zero : count [frame world (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
      (utf8 "typed extension identity") p 0).run.1] = 0 := by
    have label : (frame world (NativeTranscript.beginField (NativeExtensionRequest.prepare child degree w)
        (utf8 "typed extension identity") p 0).run.1).label ≠ hashLabel := distinct
    simp only [count,List.filter_cons,label,decide_false,Bool.false_eq_true,ite_false,List.filter_nil,List.length_nil]
  rw [zero,Nat.add_zero]

theorem start (world : World) (parent : Transcript) (packet : NativeLookupMultiplicityWire.Packet) :
    fromInput (NativeSharedLookupChild.startExecute world parent packet).1.2.input = 0 := by
  have seeded := LookupInitialReceipt.fork world (NativeSharedLookupChild.prepare parent packet)
    NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
    (by change (utf8 "classical extension lookup child v1").length < _; unfold utf8; decide +kernel)
    (by change (utf8 "packed extension tuple lookup").length < _; unfold utf8; decide +kernel)
  have typed := identity NativeFields.goldilocksModulus 3 7 world _ seeded.1 (by decide +kernel)
  change count (frames (TypedTranscriptChild.identityExecute NativeFields.goldilocksModulus 3 7 world
    (NativeTranscript.forkChild world (NativeSharedLookupChild.prepare parent packet) NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext).run.1.2).1.input) = 0
  rw [typed,seeded.2]
  rfl

end
end FormalProof4FHE.HasteBoots.LookupCompressionCount
