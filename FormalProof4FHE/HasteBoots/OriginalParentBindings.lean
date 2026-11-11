module
public import FormalProof4FHE.HasteBoots.ParentBindingsView
public import FormalProof4FHE.HasteBoots.OriginalSharedParent
import all Init.Data.String.Defs
@[expose] public section

/-! Successful native preflight recovers its literal request vector and one
binding per request. Native allocation domains and the original framed
caller parent are explicit; parser output is never used as ownership alone. -/
namespace FormalProof4FHE.HasteBoots.OriginalParentBindings
open InputIndexedOracle (World)
open NativeTranscript (Transcript)
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle)
open NativeLookupRequestWire (Request)
open NativeCanonicalLookupWire (Binding)
open NativePrefixCodec (Vector)
open OracleProgram (run)
noncomputable section

theorem bindings_valid {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (world : World) (requests : List Request) (bindings : List Binding)
    (related : List.Forall₂ (ParentBindingTrace.ForRequest row registry helper world) requests bindings)
    (fits : NativeLookupParentFraming.CallsFit registry requests) : ∀ binding ∈ bindings, TranscriptFrame.Valid (ParentBindingTrace.frame binding) := by
  revert fits
  induction related with
  | nil => intro _ binding member; cases member
  | @cons request binding requests bindings first rest ih =>
    intro fits actual member
    rcases List.mem_cons.mp member with rfl | later
    · exact ParentBindingTrace.binding_valid row registry helper world request actual first
        (fun request member => fits request (by rcases List.mem_singleton.mp member with rfl; exact List.mem_cons_self))
    · exact ih (fun request member => fits request (List.mem_cons_of_mem _ member)) actual later

theorem recover {C : Type} (row : RowDescription C) (registry : List (Oracle C)) (helper : Parameters C)
    (parent : Transcript) (requests : Vector Request) (world : World) (next : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.2 = some next)
    (before : List TranscriptFrame.Frame) (bytes : parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (domain : NativeLookupParentFraming.Domain registry requests) :
    ∃ view : ParentBindingsView.View,
      ParentBindingsView.parse (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.1.input = some view ∧
      view.before = before ∧ view.requests = requests ∧
      List.Forall₂ (ParentBindingTrace.ForRequest row registry helper world) requests.val view.bindings := by
  obtain ⟨bindings,related,emitted⟩ := ParentBindingTrace.preflight row registry helper parent requests world next success
  let view : ParentBindingsView.View := ⟨before,requests,bindings⟩
  have framed : (run (NativeSharedLookupParent.preflight row registry helper parent requests) world).run.1.1.input = TranscriptFrame.encodeMany view.frames := by
    rw [emitted,NativeLookupRequestWire.bindRequests_input,bytes]
    simp only [view,ParentBindingsView.View.frames,ParentBindingsView.requestFrame,SingleOpeningExposure.encodeMany_append,
      TranscriptFrame.encodeMany,List.append_nil,List.append_assoc]
  have bindingValid := bindings_valid row registry helper world requests.val bindings related domain.2
  have allValid : ∀ frame ∈ view.frames, TranscriptFrame.Valid frame := by
    intro frame member
    simp only [view,ParentBindingsView.View.frames,List.mem_append,List.mem_singleton,List.mem_map] at member
    rcases member with (old | rfl) | ⟨binding,named,rfl⟩
    · exact valid frame old
    · constructor
      · change NativeLookupRequestWire.requestsLabel.length < _
        unfold NativeLookupRequestWire.requestsLabel NativeTranscript.utf8
        decide +kernel
      · exact domain.1
    · exact bindingValid binding named
  refine ⟨view,?_,rfl,rfl,related⟩
  rw [framed]
  exact ParentBindingsView.parse_native view allValid related.length_eq.symm

end
end FormalProof4FHE.HasteBoots.OriginalParentBindings
