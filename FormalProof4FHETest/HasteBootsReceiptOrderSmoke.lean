module
import all FormalProof4FHE.HasteBoots.OriginalLookupReceiptOrder
import all FormalProof4FHE.HasteBoots.OrderedReceiptMatching
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ReceiptOrderSmoke
open HasteBootsSamplerAncestrySmoke
open ReceiptFrameView (frames frame)
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

theorem child_framed : ReceiptSequence.Framed child := by
  have header := NativeChildSeedView.forkChild_header worldOne parent [] [] (by decide) (by decide)
  obtain ⟨suffix,valid,bytes⟩ := header
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  exact ⟨_,decoded⟩

theorem child_empty : frames child.input = [] := by
  unfold frames child
  decide +kernel

theorem selection_order : LookupReceiptOrder.Ordered worldZero [] selection := by
  have actual := LookupReceiptOrder.execute basis 1 4 10 [[0]] _ worldZero _ (by decide +kernel)
    (LookupReceiptOrder.initial 17 1 1 child worldZero child_framed (by decide +kernel))
  rw [child_empty] at actual
  exact actual

/-- The fifth retained draw is read at the fifth decoded receipt position;
the earlier rejected draws cannot be deduplicated or silently omitted. -/
example (draw : NativeLookupChallenge.Draw (ZMod 17)) (position : selection.draws[5]? = some draw) :
    (frames (LookupReceiptLineage.current selection).input)[5]? = some (frame worldZero draw.coefficients.phase) := by
  rw [selection_order.2.2,List.nil_append,List.getElem?_map,position,Option.map_some]

example : selection.draws.length = 10 ∧ selection.rejected = 9 := by decide +kernel

/-- Exact ordered concatenation covers both completed jobs. -/
theorem batch_order : LookupBatchReceiptOrder.Ordered worldOne [] batch := by
  have actual := LookupBatchReceiptOrder.execute basis 1 30 _ worldOne _ (by decide +kernel)
    (LookupBatchReceiptOrder.initial actions child worldOne child_framed)
  rw [child_empty] at actual
  exact actual

/-- Root binding adds no receipt, so equality receipt indices start at zero
for this fixture and preserve both point positions. -/
theorem equality_order : EqualityReceiptOrder.Ordered worldOne [] equality.1 := by
  have rootBinding := ReceiptSequence.absorb child 1 NativeLookupEquality.rootsLabel (NativeRootMessage.encode roots rootsFits) child_framed
    ⟨by change (NativeTranscript.utf8 "shared lookup helper roots").length < _; decide +kernel,by decide +kernel⟩ (by decide)
  have actual := EqualityReceiptOrder.execute basis 1 10 _ worldOne _ (by decide +kernel)
    (EqualityReceiptOrder.initial 2 child roots rootsFits worldOne rootBinding.1)
  have boundEmpty : frames (NativeLookupEquality.bindRoots child roots rootsFits).input = [] := rootBinding.2.trans child_empty
  rw [boundEmpty] at actual
  exact actual

example (draw : NativeLookupEquality.Draw 2 (ZMod 17)) (position : equality.1.draws[1]? = some draw) :
    (frames equality.1.transcript.input)[1]? = some (frame worldOne draw.coefficients.phase) := by
  rw [equality_order.2.2.2,List.nil_append,List.getElem?_map,position,Option.map_some]

/-- The earlier-count premise is necessary: equal whole lists can have
different suffixes if their earlier boundaries differ. -/
example : [1] ++ [2] = ([] : List ℕ) ++ [1,2] ∧ ([2] : List ℕ) ≠ [1,2] := by decide


end
end FormalProof4FHE.HasteBoots.ReceiptOrderSmoke
