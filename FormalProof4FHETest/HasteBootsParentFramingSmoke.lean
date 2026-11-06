module
import all FormalProof4FHE.HasteBoots.NativeLookupBodyFraming
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke
open FormalProof4FHE.HasteBoots
open NativeTranscriptFraming (Framed)
open NativeTranscriptExtension (Extends)
open OracleProgram (run)
namespace HasteBootsParentFramingSmoke
noncomputable section
open HasteBootsRegistryAncestrySmoke

local instance {C : Type} (selected : List (NativeSharedLookupParent.Oracle C)) (request : NativeLookupRequestWire.Request) :
    Decidable (NativeLookupParentFraming.FrameFits selected request) := by
  unfold NativeLookupParentFraming.FrameFits
  infer_instance

def callsFit {C : Type} (registry : List (NativeSharedLookupParent.Oracle C)) (requests : List NativeLookupRequestWire.Request) : Bool :=
  requests.all (fun request => match NativeSharedLookupParent.gather registry request.toModel.terminal.sourceSlots with
    | none => true
    | some selected => decide (NativeLookupParentFraming.FrameFits selected request))

theorem calls_domain {C : Type} (registry : List (NativeSharedLookupParent.Oracle C)) (requests : List NativeLookupRequestWire.Request)
    (checked : callsFit registry requests = true) : NativeLookupParentFraming.CallsFit registry requests := by
  intro request member selected computed
  have fits := List.all_eq_true.mp checked request member
  rw [computed] at fits
  exact of_decide_eq_true fits

theorem original_domain : NativeLookupParentFraming.Domain registry.val requests :=
  ⟨by decide +kernel,calls_domain registry.val requests.val (by decide +kernel)⟩

theorem parent_framed : Framed parent := NativeTranscriptFraming.new [] _ (by decide +kernel)

example : Extends parent preparation.1.1 :=
  NativeLookupParentFraming.prepared description registry helper parent requests world original_domain (by decide +kernel)

example : Framed preparation.1.1 := NativeTranscriptFraming.of_extension parent_framed
  (NativeLookupParentFraming.prepared description registry helper parent requests world original_domain (by decide +kernel))

example : Framed (run (NativeSharedLookupParent.prepare failingDescription registry helper parent requests) world).run.1.1 :=
  NativeTranscriptFraming.of_extension parent_framed
    (NativeLookupParentFraming.prepared failingDescription registry helper parent requests world original_domain (by decide +kernel))

def incompatible : NativeSharedLookupPreflight.State := ⟨some (usize 42,usize 43),0,[]⟩
example : (run (NativeSharedLookupParent.step description registry.val helper incompatible parent request) world).run.1.2 = none := by decide +kernel
example : (run (NativeSharedLookupParent.step description registry.val helper incompatible parent request) world).run.1.1.input ≠ parent.input := by decide +kernel
example : Framed (run (NativeSharedLookupParent.step description registry.val helper incompatible parent request) world).run.1.1 :=
  NativeTranscriptFraming.of_extension parent_framed (NativeLookupParentFraming.step description registry.val helper incompatible parent request world original_domain.2)

example : Framed (NativeSharedLookupChild.startExecute world parent packet).1.1.parent :=
  NativeTranscriptFraming.of_extension parent_framed (NativeChildParentFraming.start_parent world parent packet ⟨by decide +kernel,by decide +kernel⟩)

-- Parent framing uses the actual fixed-size fingerprint, not a future child-frame certificate.
def malformedChild : NativeTranscript.Transcript := ⟨[255],parent.profile⟩
example : ¬Framed malformedChild := by rw [NativeTranscriptFraming.framed_iff_decode]; decide +kernel
example : Framed (NativeTranscript.finishLinkedChild world parent malformedChild NativeSharedLookupChild.childLabel).run.1.1 :=
  NativeTranscriptFraming.of_extension parent_framed (NativeChildParentFraming.linked_parent world parent malformedChild _ (by decide +kernel))
example : (run (NativeSharedLookupChild.finish (NativeSharedLookupChild.startExecute world parent packet).1.1 malformedChild) world).run.1.outcome = .ok () :=
  (NativeSharedLookupChild.finish_started_iff world parent packet malformedChild).mpr rfl

example : (NativeCanonicalLookupWire.sourcesCodec.encode expected).length ≤ 9 + 128 * registry.val.length :=
  NativeCanonicalMessageBounds.sources_length expected
end
end HasteBootsParentFramingSmoke
