module

public import FormalProof4FHE.HasteBoots.NativeScalarTranscriptExtension
public import FormalProof4FHE.HasteBoots.NativeLookupTranscriptExtension
public import FormalProof4FHE.HasteBoots.NativeSharedLookupBody
import all Init.Data.String.Defs

@[expose] public section

/-! Native child finishing preserves child and parent transcript ancestry
on successful and rejected mode/profile/checkpoint branches. A body reaching
the PCS boundary returns a child extending its actual pre-scalar transcript
and a parent retaining prior source/context frames. Framing domains are
explicit; authentication, freshness, work and Rust refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open NativeTranscriptExtension (Extends)
open OracleProgram (run)
noncomputable section

theorem challenge (state : Transcript) (label : Input) (count : ℕ) (world : World)
    (labelFits : label.length < TranscriptFrame.lengthLimit) (countFits : count < TranscriptFrame.lengthLimit) :
    Extends state (NativeTranscript.challengeBytes world state label count).run.1.2 := by
  apply (NativeTranscriptExtension.absorb state 2 label (TranscriptFrame.littleEndian 8 count)
    ⟨labelFits,by simp only [TranscriptFrame.littleEndian_length]; decide +kernel⟩).trans
  apply NativeTranscriptExtension.absorb _ 3 label _
  exact ⟨labelFits,by simpa only [InputIndexedOracle.bytes_length] using countFits⟩

theorem linked_child (world : World) (parent child : Transcript) (label : Input) :
    Extends child (NativeTranscript.finishLinkedChild world parent child label).run.1.2 :=
  challenge child (NativeTranscript.utf8 "classical child finish") 64 world (by decide +kernel) (by decide +kernel)

/-- Failed mode/profile/checkpoint guards retain the original child; success appends the actual finish challenge. -/
theorem typed_finish_child (world : World) (parent : Option Transcript) (child : Transcript)
    (binding : Option TypedTranscriptChild.Binding) :
    ∃ after, (run (TypedTranscriptChild.finish parent ⟨some child,binding⟩) world).run.1.child.bytes = some after ∧ Extends child after := by
  rw [TypedTranscriptChild.run_finish]
  cases binding with
  | none => exact ⟨child,rfl,Extends.refl child⟩
  | some binding =>
    cases parent with
    | none => exact ⟨child,rfl,Extends.refl child⟩
    | some parent =>
      by_cases parentProfile : parent.profile = binding.profile
      · by_cases childProfile : child.profile = binding.profile
        · by_cases checkpoint : (NativeTranscript.checkpoint world parent).run.1 = binding.checkpoint
          · simp only [TypedTranscriptChild.finishExecute,parentProfile,childProfile,checkpoint,ite_true]
            exact ⟨_,rfl,linked_child world parent child binding.label⟩
          · simp only [TypedTranscriptChild.finishExecute,parentProfile,childProfile,checkpoint,ite_true,ite_false]
            exact ⟨child,rfl,Extends.refl child⟩
        · simp only [TypedTranscriptChild.finishExecute,parentProfile,childProfile,ite_true,ite_false]
          exact ⟨child,rfl,Extends.refl child⟩
      · simp only [TypedTranscriptChild.finishExecute,parentProfile,ite_false]
        exact ⟨child,rfl,Extends.refl child⟩

/-- Parent acknowledgement retains all earlier source/context frames on every finish branch. -/
theorem typed_finish_parent (world : World) (parent : Transcript) (child : TypedTranscriptChild.Child)
    (labelFits : ∀ binding, child.binding = some binding → binding.label.length < TranscriptFrame.lengthLimit) :
    ∃ after, (run (TypedTranscriptChild.finish (some parent) child) world).run.1.parent = some after ∧ Extends parent after := by
  rw [TypedTranscriptChild.run_finish]
  cases binding : child.binding with
  | none => simp only [TypedTranscriptChild.finishExecute,binding]; exact ⟨parent,rfl,Extends.refl parent⟩
  | some stored =>
    cases bytes : child.bytes with
    | none => simp only [TypedTranscriptChild.finishExecute,binding,bytes]; exact ⟨parent,rfl,Extends.refl parent⟩
    | some childBytes =>
      by_cases parentProfile : parent.profile = stored.profile
      · by_cases childProfile : childBytes.profile = stored.profile
        · by_cases checkpoint : (NativeTranscript.checkpoint world parent).run.1 = stored.checkpoint
          · simp only [TypedTranscriptChild.finishExecute,binding,bytes,parentProfile,childProfile,checkpoint,ite_true]
            refine ⟨_,rfl,?_⟩
            apply NativeTranscriptExtension.absorb parent 7 stored.label _
            exact ⟨labelFits stored binding,by simp only [InputIndexedOracle.bytes_length]; decide +kernel⟩
          · simp only [TypedTranscriptChild.finishExecute,binding,bytes,parentProfile,childProfile,checkpoint,ite_true,ite_false]
            exact ⟨parent,rfl,Extends.refl parent⟩
        · simp only [TypedTranscriptChild.finishExecute,binding,bytes,parentProfile,childProfile,ite_true,ite_false]
          exact ⟨parent,rfl,Extends.refl parent⟩
      · simp only [TypedTranscriptChild.finishExecute,binding,bytes,parentProfile,ite_false]
        exact ⟨parent,rfl,Extends.refl parent⟩

theorem terminal {S B : Type} (state : Transcript) (proof : NativeSharedLookupProofData.Proof S B)
    (fits : (NativeSharedLookupProofData.terminal proof).length < TranscriptFrame.lengthLimit) :
    Extends state (NativeSharedLookupChild.bindTerminal state proof) :=
  NativeTranscriptExtension.absorb state 1 NativeSharedLookupChild.terminalLabel _
    ⟨by change NativeSharedLookupChild.terminalLabel.length < _; decide +kernel,fits⟩

/-- A native PCS-boundary result's returned child extends the actual pre-scalar child. -/
theorem body_bound_child {S B : Type} {count dimension : ℕ} (requests : Fin count → NativeSharedLookupStatement.Request)
    (registry : List NativeLookupBindGeometry.Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupBody.body requests registry width state ready proof fuel) world).run.1 = .bound result)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode ready.statement).length < TranscriptFrame.lengthLimit)
    (roundFits : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (terminalFits : (NativeSharedLookupProofData.terminal proof).length < TranscriptFrame.lengthLimit) :
    ∃ child, result.child.bytes = some child ∧ Extends ready.equality.transcript child := by
  have contract := NativeSharedLookupBody.body_bound requests registry width state ready proof fuel world result success
  have scalar := NativeScalarTranscriptExtension.execute ready.equality.transcript ready.statement proof.algebra fuel _ world roundFits
    (NativeScalarTranscriptExtension.initial ready.equality.transcript ready.statement proof.algebra statementFits)
  have before : Extends ready.equality.transcript result.machine.state.transcript := by
    rw [contract.1]
    exact scalar.1
  have finished := typed_finish_child world (some state.parent)
    (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof) (some state.binding)
  change ∃ child, (run (NativeSharedLookupBody.finish state proof result.machine) world).run.1.child.bytes = some child ∧
    Extends (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof) child at finished
  rw [contract.2.finished] at finished
  obtain ⟨child,bytes,extension⟩ := finished
  exact ⟨child,bytes,before.trans ((terminal _ proof terminalFits).trans extension)⟩

theorem body_bound_parent {S B : Type} {count dimension : ℕ} (requests : Fin count → NativeSharedLookupStatement.Request)
    (registry : List NativeLookupBindGeometry.Parameters) (width : ℕ) (state : NativeSharedLookupChild.State)
    (ready : NativeSharedLookupPrelude.Ready dimension) (proof : NativeSharedLookupProofData.Proof S B)
    (fuel : ℕ) (world : World) (result : NativeSharedLookupBody.Bound)
    (success : (run (NativeSharedLookupBody.body requests registry width state ready proof fuel) world).run.1 = .bound result)
    (labelFits : state.binding.label.length < TranscriptFrame.lengthLimit) : Extends state.parent result.parent := by
  have contract := NativeSharedLookupBody.body_bound requests registry width state ready proof fuel world result success
  have finished := typed_finish_parent world state.parent
    ⟨some (NativeSharedLookupChild.bindTerminal result.machine.state.transcript proof),some state.binding⟩
    (by intro binding same; have equal := Option.some.inj same; subst binding; exact labelFits)
  change ∃ after, (run (NativeSharedLookupBody.finish state proof result.machine) world).run.1.parent = some after ∧ Extends state.parent after at finished
  rw [contract.2.finished] at finished
  obtain ⟨after,same,extension⟩ := finished
  exact Option.some.inj same ▸ extension

end
end FormalProof4FHE.HasteBoots.NativeFinishedChildAncestry
