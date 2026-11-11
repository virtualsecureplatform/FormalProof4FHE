module
import all FormalProof4FHE.HasteBoots.SharedParentBindingsData
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke

namespace FormalProof4FHE.HasteBoots.ParentBindingsSmoke
open HasteBootsRegistryAncestrySmoke
open OracleProgram (run)
noncomputable section

def binding : NativeCanonicalLookupWire.Binding := ⟨config,digest 0,⟨[(digest 0,root)],by decide⟩⟩
def initial := (TranscriptFrame.decodeAll parent.input).getD []
def view : ParentBindingsView.View := ⟨initial,requests,[binding]⟩

theorem actual_parsed : ParentBindingsView.parse preflightParent.input = some view  := by
  have bytes : preflightParent.input = TranscriptFrame.encodeMany view.frames := by decide +kernel
  rw [bytes]
  apply ParentBindingsView.parse_native
  · have decoded : TranscriptFrame.decodeAll (TranscriptFrame.encodeMany view.frames) = some view.frames := by decide +kernel
    exact (TranscriptFrame.decodeAll_sound _ _ decoded).1
  · rfl

theorem actual_relation : ParentBindingTrace.ForRequest description registry.val helper world request binding := by
  refine ⟨[registry.val[1]],rfl,rfl,?_,?_⟩ <;> decide +kernel

/-- Source slot 1 remains slot 1 despite its alias at slot 0. -/
theorem original_address : request.toModel.terminal.sourceSlots = [1] ∧
    ParentBindingSlots.gather expected.val request.toModel.terminal.sourceSlots = some binding.sources.val :=
  ⟨rfl,ParentBindingSlots.binding description registry.val helper expected.val world contexts_computed request binding actual_relation⟩

/-- Literal gathering preserves repeated addresses and their order. -/
theorem repeated_addresses : ParentBindingSlots.gather expected.val [2,1,2] =
    some [(digest 1,root),(digest 0,root),(digest 1,root)] := rfl

/-- An earlier request frame cannot replace the adjacent request vector. -/
theorem decoy : ParentBindingsView.readFrames
    [ParentBindingTrace.frame binding,ParentBindingsView.requestFrame requests,ParentBindingsView.requestFrame ⟨[],by decide⟩] =
    some ⟨[ParentBindingsView.requestFrame ⟨[],by decide⟩],requests,[binding]⟩ := by
  exact ParentBindingsView.readFrames_native [ParentBindingsView.requestFrame ⟨[],by decide⟩] requests [binding]

/-- A malformed canonical binding stops parsing instead of falling back. -/
theorem malformed : ParentBindingsView.readFrames
    [⟨1,NativeCanonicalLookupWire.label,[]⟩,ParentBindingsView.requestFrame requests] = none := by decide +kernel

/-- A well framed request with no corresponding binding is rejected. -/
theorem missing_binding : ParentBindingsView.parse
    (TranscriptFrame.encodeMany [ParentBindingsView.requestFrame requests]) = none := by decide +kernel

end
end FormalProof4FHE.HasteBoots.ParentBindingsSmoke
