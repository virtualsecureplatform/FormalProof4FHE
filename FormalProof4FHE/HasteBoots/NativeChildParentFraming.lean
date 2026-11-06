module

public import FormalProof4FHE.HasteBoots.NativeTranscriptFraming
public import FormalProof4FHE.HasteBoots.NativeSharedLookupExecution
import all Init.Data.String.Defs
@[expose] public section

/-! Framed ancestry of the retained classical parent through a native child
fork and successful finish. Child fingerprint bytes have their actual fixed
length; no framing certificate for a future child computation is required. -/
namespace FormalProof4FHE.HasteBoots.NativeChildParentFraming
open NativeTranscript (Transcript utf8)
open NativeTranscriptExtension (Extends)
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (Input World)
open OracleProgram (run)
noncomputable section

theorem fork_parent (world : World) (parent : Transcript) (label context : Input)
    (labelFits : label.length < TranscriptFrame.lengthLimit)
    (contextFits : context.length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeTranscript.forkChild world parent label context).run.1.1 :=
  (NativeTranscriptExtension.absorb parent 6 label context ⟨labelFits,contextFits⟩).trans
    (NativeTranscriptFraming.challenge_bytes _ (utf8 "classical child seed") 64 world (by decide +kernel) (by decide +kernel))

theorem linked_parent (world : World) (parent child : Transcript) (label : Input)
    (labelFits : label.length < TranscriptFrame.lengthLimit) :
    Extends parent (NativeTranscript.finishLinkedChild world parent child label).run.1.1 := by
  apply NativeTranscriptExtension.absorb parent 7 label _
  exact ⟨labelFits,by change (InputIndexedOracle.bytes world _ 0 64).length < _; rw [InputIndexedOracle.bytes_length]; decide +kernel⟩

theorem finish_parent (world : World) (parent child : Transcript) (binding : TypedTranscriptChild.Binding)
    (next : Transcript)
    (success : (run (TypedTranscriptChild.finish (some parent) ⟨some child,some binding⟩) world).run.1.outcome = .ok ())
    (returned : (run (TypedTranscriptChild.finish (some parent) ⟨some child,some binding⟩) world).run.1.parent = some next)
    (labelFits : binding.label.length < TranscriptFrame.lengthLimit) : Extends parent next := by
  rw [TypedTranscriptChild.run_finish] at success returned
  obtain ⟨parentProfile,childProfile,checkpoint⟩ := (TypedTranscriptChild.finish_accepts_iff world parent child binding).mp success
  rw [TypedTranscriptChild.finish_success world parent child binding parentProfile childProfile checkpoint] at returned
  have same := Option.some.inj returned
  rw [← same]
  exact linked_parent world parent child binding.label labelFits

/-- Multiplicity bounds depend only on the original packet, before the seed draw. -/
def PacketDomain (packet : NativeLookupMultiplicityWire.Packet) : Prop :=
  (NativeLookupMultiplicityWire.grouped packet).length < TranscriptFrame.lengthLimit ∧
  (NativeLookupMultiplicityWire.flattened packet).length < TranscriptFrame.lengthLimit

theorem prepare (parent : Transcript) (packet : NativeLookupMultiplicityWire.Packet) (domain : PacketDomain packet) :
    Extends parent (NativeSharedLookupChild.prepare parent packet) :=
  (NativeTranscriptExtension.absorb parent 1 NativeSharedLookupChild.groupedLabel _
    ⟨by change NativeSharedLookupChild.groupedLabel.length < _; decide +kernel,domain.1⟩).trans
    (NativeTranscriptExtension.absorb _ 1 NativeSharedLookupChild.flatLabel _
      ⟨by change NativeSharedLookupChild.flatLabel.length < _; decide +kernel,domain.2⟩)

theorem start_parent (world : World) (parent : Transcript) (packet : NativeLookupMultiplicityWire.Packet)
    (domain : PacketDomain packet) : Extends parent (NativeSharedLookupChild.startExecute world parent packet).1.1.parent :=
  (prepare parent packet domain).trans (fork_parent world _ NativeSharedLookupChild.childLabel NativeSharedLookupChild.childContext
    (by decide +kernel) (by decide +kernel))

/-- The accepted body returns a framed extension of its retained parent even
when the scalar child has undergone arbitrarily many sampling transitions. -/
theorem body_parent {S B : Type} {count dimension : ℕ} (requests : Fin count → NativeSharedLookupStatement.Request)
    (registry : List NativeLookupBindGeometry.Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupBody.body requests registry width state ready proof fuel) world).run.1 = .bound result)
    (labelFits : state.binding.label.length < TranscriptFrame.lengthLimit) : Extends state.parent result.parent := by
  have contract := (NativeSharedLookupBody.body_bound requests registry width state ready proof fuel world result success).2
  apply finish_parent world state.parent (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof) state.binding result.parent
  · exact congrArg TypedTranscriptChild.FinishResult.outcome contract.finished
  · exact congrArg TypedTranscriptChild.FinishResult.parent contract.finished
  · exact labelFits

/-- Actual launch computes the retained parent and binding; neither is supplied
as a framing certificate. -/
theorem launched_body {S B : Type} {count : ℕ} (fits : count ≤ 2^64)
    (requests : Fin count → NativeSharedLookupStatement.Request) (policy : NativeSharedLookupValues.Policy)
    (registry : List NativeLookupBindGeometry.Parameters) (geometry : NativeSharedLookupPreflight.Output)
    (proof : NativeSharedLookupProofData.Proof S B) (lookupFuel equalityFuel scalarFuel : ℕ)
    (parent : Transcript) (world : World) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready geometry.geometry.1.val) (result : NativeSharedLookupBody.Bound)
    (launched : (run (NativeSharedLookupChild.launch fits requests policy registry geometry proof lookupFuel equalityFuel parent) world).run.1 = some (state,ready))
    (body : (run (NativeSharedLookupBody.body requests registry geometry.geometry.2.val state ready proof scalarFuel) world).run.1 = .bound result)
    (domain : PacketDomain proof.multiplicities) : Extends parent result.parent := by
  have original := (NativeSharedLookupChild.launch_spec fits requests policy registry geometry proof lookupFuel equalityFuel parent world state ready launched).1
  have labelFits : state.binding.label.length < TranscriptFrame.lengthLimit := by
    rw [original]
    change NativeSharedLookupChild.childLabel.length < _
    decide +kernel
  have retained := start_parent world parent proof.multiplicities domain
  rw [← original] at retained
  exact retained.trans (body_parent requests registry geometry.geometry.2.val state ready proof scalarFuel world result body labelFits)
end
end FormalProof4FHE.HasteBoots.NativeChildParentFraming
