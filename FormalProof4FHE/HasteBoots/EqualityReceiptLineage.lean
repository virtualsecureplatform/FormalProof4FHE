module
public import FormalProof4FHE.HasteBoots.LookupReceiptLineage
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Actual equality-point receipts remain in the machine transcript after
later points and across suspension. Active reader ancestry is maintained too. -/
namespace FormalProof4FHE.HasteBoots.EqualityReceiptLineage
open InputIndexedOracle (World)
open NativeTranscriptExtension (Extends StateExtends)
noncomputable section

def Equality (world : World) {count : ℕ} {K : Type} (machine : NativeLookupEquality.Machine count K) : Prop :=
  (∀ field, machine.active = some field → StateExtends machine.transcript field) ∧
  ∀ draw ∈ machine.draws, Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 machine.transcript

variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

omit [Field K] [Algebra (ZMod p) K] in
theorem initial (count : ℕ) (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) :
    Equality world (NativeLookupEquality.initial (K := K) count transcript roots fits) := by
  constructor
  · intro field impossible; contradiction
  · intro draw impossible; contradiction

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Equality world machine) :
    Extends machine.transcript (NativeLookupEquality.tickExecute basis w machine world).1.transcript ∧
      Equality world (NativeLookupEquality.tickExecute basis w machine world).1 := by
  by_cases complete : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,complete,ite_true] using And.intro (Extends.refl _) valid
  · cases active : machine.active with
    | none =>
      simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,Equality]
      refine ⟨Extends.refl _,?_,valid.2⟩
      intro field same
      exact Option.some.inj same ▸ NativeTranscriptExtension.vector_begin p degree w count machine.transcript NativeLookupEquality.pointLabel
        (by change (NativeTranscript.utf8 "shared lookup equality point").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
    | some field =>
      have driven := NativeTranscriptExtension.drive_status machine.transcript p 1 field world (valid.1 field active)
      cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
      | suspended next =>
        simp only [result,NativeTranscriptExtension.StatusExtends] at driven
        simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,Equality]
        refine ⟨Extends.refl _,?_,valid.2⟩
        intro field same
        exact Option.some.inj same ▸ driven
      | finished next transcript =>
        simp only [result,NativeTranscriptExtension.StatusExtends] at driven
        have final := LookupReceiptLineage.drive_finished p 1 field next world transcript result
        simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,Equality]
        refine ⟨driven.2,?_,?_⟩
        · intro field impossible; contradiction
        · intro draw member
          rcases List.mem_append.mp member with old | added
          · exact (valid.2 draw old).trans driven.2
          · obtain rfl := List.mem_singleton.mp added
            rw [← final]
            exact Extends.refl _

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Equality world machine) :
    Extends machine.transcript (NativeLookupEquality.execute basis w fuel machine world).1.transcript ∧
      Equality world (NativeLookupEquality.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact ⟨Extends.refl _,valid⟩
  | succ fuel ih =>
    have next := tick basis w machine world descriptorFits valid
    have later := ih _ next.2
    exact ⟨next.1.trans later.1,later.2⟩

theorem request (basis : Module.Basis (Fin degree) (ZMod p) K) (w count fuel : ℕ)
    (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest) (fits : roots.length < 2^64) (world : World)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit) :
    Equality world (OracleProgram.run (NativeLookupEquality.request basis w count fuel transcript roots fits) world).run.1 := by
  rw [NativeLookupEquality.request,NativeLookupEquality.run_steps]
  exact (execute basis w fuel _ world descriptorFits (initial count transcript roots fits world)).2

end
end FormalProof4FHE.HasteBoots.EqualityReceiptLineage
