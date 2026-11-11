module
import all FormalProof4FHE.HasteBoots.OriginalReceiptSegmentation
import all FormalProof4FHETest.HasteBootsSamplerAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ReceiptSegmentationSmoke
open HasteBootsSamplerAncestrySmoke
open TranscriptFrame (Frame)
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

/-- The active native sampler has one compression label and nine retained
rejected reciprocal draws, without a caller-supplied label certificate. -/
example : LookupReceiptLabels.Labels selection :=
  LookupReceiptLabels.execute basis 1 4 10 [[0]] _ worldZero (LookupReceiptLabels.initial 17 1 1 child)

/-- Both actual completed jobs independently supply compression-headed groups. -/
example (entry : NativeLookupBatch.Completed 17 (ZMod 17)) (member : entry ∈ batch.completed) :
    ReceiptLabelSegmentation.Group (entry.selection.draws.map (fun draw => ReceiptFrameView.frame worldOne draw.coefficients.phase)) :=
  ReceiptLabelSegmentation.native_group worldOne _
    ((LookupBatchReceiptLabels.execute basis 1 30 _ worldOne (LookupBatchReceiptLabels.initial actions child)).2 entry member)

example (draw : NativeLookupEquality.Draw 2 (ZMod 17)) (member : draw ∈ equality.1.draws) :
    draw.coefficients.phase.label = NativeLookupEquality.pointLabel :=
  (EqualityReceiptLabels.request basis 1 2 10 child roots rootsFits worldOne).2 draw member

def packet : NativeLookupMultiplicityWire.Packet := ⟨⟨[],by decide⟩,by decide⟩

/-- The real initializer includes exactly the zero-count identity receipt. -/
example : (ReceiptFrameView.frames (NativeSharedLookupChild.startExecute worldOne parent packet).1.2.input).length = 1 :=
  (LookupInitialReceipt.start worldOne parent packet).2

/-- Marker scanning keeps repeated body elements and stops at the next head. -/
example : ReceiptGroupSegmentation.front id [false,false,true,false,true] =
    ([false,false],[true,false,true]) := rfl

def compression : Frame := ⟨5,NativeLookupChallenge.hashLabel,[1]⟩
def reciprocal : Frame := ⟨5,NativeLookupChallenge.reciprocalLabel,[2]⟩
def eqReceipt : Frame := ⟨5,NativeLookupEquality.pointLabel,[3]⟩
def groups : List (List Frame) := [[compression,reciprocal,reciprocal],[compression,reciprocal]]

theorem grouped : ∀ group ∈ groups, ReceiptLabelSegmentation.Group group := by
  intro group member
  simp only [groups,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact ⟨compression,[reciprocal,reciprocal],rfl,rfl,by simp [reciprocal]⟩
  · exact ⟨compression,[reciprocal],rfl,rfl,by simp [reciprocal]⟩

/-- No body lengths or earlier receipt counts are supplied to recover two
jobs followed by two EQ receipts, even with duplicate reciprocal frames. -/
example (other : List (List Frame)) (otherEQ : List Frame)
    (valid : ∀ group ∈ other, ReceiptLabelSegmentation.Group group)
    (labels : ∀ entry ∈ otherEQ, entry.label = NativeLookupEquality.pointLabel)
    (same : groups.flatten ++ [eqReceipt,eqReceipt] = other.flatten ++ otherEQ) :
    groups = other ∧ [eqReceipt,eqReceipt] = otherEQ :=
  ReceiptLabelSegmentation.prelude_unique groups other _ otherEQ grouped valid (by simp [eqReceipt]) labels same

end
end FormalProof4FHE.HasteBoots.ReceiptSegmentationSmoke
