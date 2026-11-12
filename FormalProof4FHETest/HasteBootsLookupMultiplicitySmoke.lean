module
import all FormalProof4FHE.HasteBoots.CallerLookupMultiplicityRecovery
import all Init.Data.String.Defs

namespace HasteBootsLookupMultiplicitySmoke
open FormalProof4FHE.HasteBoots
open NativeLookupMultiplicityWire (Packet grouped flattened)
noncomputable section

def left : Packet := ⟨⟨[⟨[1,2],by decide⟩,⟨[3],by decide⟩],by decide⟩,by decide⟩
def right : Packet := ⟨⟨[⟨[1],by decide⟩,⟨[2,3],by decide⟩],by decide⟩,by decide⟩

/-- Flattened multiplicities alone do not fix original request row boundaries. -/
theorem grouping_matters : flattened left = flattened right ∧ grouped left ≠ grouped right := by decide +kernel

def view : SharedParentInputView.View :=
  ⟨[SharedParentInputView.groupedFrame (grouped right),SharedParentInputView.flatFrame (flattened right)],
    ⟨[],by decide⟩,grouped left,flattened left⟩

/-- Earlier same-label frames cannot replace the actual adjacent final
multiplicity payload, even when the flattened vectors happen to agree. -/
theorem adjacent_original_payload :
    (SharedParentInputView.parse (TranscriptFrame.encodeMany view.frames)).map
      (fun parsed => (parsed.before,parsed.grouped,parsed.flat)) =
      some (view.before,grouped left,flattened left) := by
  have valid := SharedParentInputView.valid view (by
    intro frame member
    simp only [view,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · constructor
      · change NativeSharedLookupChild.groupedLabel.length < _
        unfold NativeSharedLookupChild.groupedLabel NativeTranscript.utf8
        decide +kernel
      · decide +kernel
    · constructor
      · change NativeSharedLookupChild.flatLabel.length < _
        unfold NativeSharedLookupChild.flatLabel NativeTranscript.utf8
        decide +kernel
      · decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [SharedParentInputView.parse_native view valid]
  rfl

/-- The raw grouped payload retains lazy field spellings. Semantic equality
of counts does not justify substituting a different original serialized row. -/
def lazyZero : NativeFieldRepresentation.GoldWord := ⟨NativeFields.goldilocksModulus,by decide +kernel⟩
def canonical : Packet := ⟨⟨[⟨[0],by decide⟩],by decide⟩,by decide⟩
def lazy : Packet := ⟨⟨[⟨[lazyZero],by decide⟩],by decide⟩,by decide⟩

theorem raw_count_spelling : grouped canonical ≠ grouped lazy ∧
    canonical.groups.values.map (List.map NativeFieldRepresentation.goldCanonical) =
      lazy.groups.values.map (List.map NativeFieldRepresentation.goldCanonical) := by decide +kernel

end
end HasteBootsLookupMultiplicitySmoke
