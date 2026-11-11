module
public import FormalProof4FHE.HasteBoots.ReceiptSequence
public import FormalProof4FHE.HasteBoots.EqualityReceiptLineage
import all FormalProof4FHE.HasteBoots.NativeLookupEquality
import all FormalProof4FHE.HasteBoots.NativeTranscript
@[expose] public section

/-! Equality-point receipts are exactly the chronological kind-5 suffix of
the root-bound transcript, preserving duplicate frames and native draw order. -/
namespace FormalProof4FHE.HasteBoots.EqualityReceiptOrder
open InputIndexedOracle (World)
open ReceiptSequence (Framed)
open ReceiptFrameView (frames frame)
noncomputable section

def Ordered (world : World) (earlier : List TranscriptFrame.Frame) {count : ℕ} {K : Type}
    (machine : NativeLookupEquality.Machine count K) : Prop :=
  Framed machine.transcript ∧ EqualityReceiptLineage.Equality world machine ∧
    (∀ field, machine.active = some field → Framed field.phase.pending ∧ frames field.phase.pending.input = frames machine.transcript.input) ∧
    frames machine.transcript.input = earlier ++ machine.draws.map (fun draw => frame world draw.coefficients.phase)

variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

omit [Field K] [Algebra (ZMod p) K] in
theorem initial (count : ℕ) (transcript : NativeTranscript.Transcript) (roots : List NativeRootMessage.Digest)
    (fits : roots.length < 2^64) (world : World) (old : Framed (NativeLookupEquality.bindRoots transcript roots fits)) :
    Ordered world (frames (NativeLookupEquality.bindRoots transcript roots fits).input)
      (NativeLookupEquality.initial (K := K) count transcript roots fits) := by
  exact ⟨old,EqualityReceiptLineage.initial count transcript roots fits world,
    by intro field impossible; contradiction,by simp [NativeLookupEquality.initial]⟩

theorem tick (basis : Module.Basis (Fin degree) (ZMod p) K) (w : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Ordered world earlier machine) :
    Ordered world earlier (NativeLookupEquality.tickExecute basis w machine world).1 := by
  have lineage := (EqualityReceiptLineage.tick basis w machine world descriptorFits valid.2.1).2
  by_cases complete : machine.remaining = 0
  · simpa only [NativeLookupEquality.tickExecute,complete,ite_true] using valid
  · cases active : machine.active with
    | none =>
      have begun := ReceiptSequence.vector_begin machine.transcript NativeLookupEquality.pointLabel p degree w count valid.1
        (by change (NativeTranscript.utf8 "shared lookup equality point").length < _; unfold NativeTranscript.utf8; decide +kernel) descriptorFits
      refine ⟨?_,lineage,?_,?_⟩
      · simpa only [NativeLookupEquality.tickExecute,complete,ite_false,active] using valid.1
      · simp only [NativeLookupEquality.tickExecute,complete,ite_false,active]
        intro field same
        exact Option.some.inj same ▸ begun
      · simpa only [NativeLookupEquality.tickExecute,complete,ite_false,active] using valid.2.2.2
    | some field =>
      have pending := valid.2.2.1 field active
      have label := (valid.2.1.1 field active).2
      cases result : (NativeFieldVector.driveExecute p 1 field world).1 with
      | suspended next =>
        have fields := NativeTranscriptExtension.execute_fields p 1 field world
        have retained := congrArg NativeFieldVector.stateOf result
        rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
        change (NativeFieldVector.execute p 1 field world).1 = next at retained
        rw [retained] at fields
        refine ⟨?_,lineage,?_,?_⟩
        · simpa only [NativeLookupEquality.tickExecute,complete,ite_false,active,result] using valid.1
        · simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result]
          intro field same
          have nextPending : Framed next.phase.pending ∧ frames next.phase.pending.input = frames machine.transcript.input := by rw [fields.1]; exact pending
          exact Option.some.inj same ▸ nextPending
        · simpa only [NativeLookupEquality.tickExecute,complete,ite_false,active,result] using valid.2.2.2
      | finished next transcript =>
        have fields := NativeTranscriptExtension.execute_fields p 1 field world
        have retained := congrArg NativeFieldVector.stateOf result
        rw [NativeFieldVector.driveExecute,NativeFieldVector.finish_state] at retained
        change (NativeFieldVector.execute p 1 field world).1 = next at retained
        rw [retained] at fields
        have final := LookupReceiptLineage.drive_finished p 1 field next world transcript result
        have done := ReceiptSequence.finish next.phase world (by rw [fields.1]; exact pending.1) (by rw [fields.2]; exact label)
        rw [← final] at done
        refine ⟨?_,lineage,?_,?_⟩
        · simpa only [NativeLookupEquality.tickExecute,complete,ite_false,active,result] using done.1
        · simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result]
          intro field impossible; contradiction
        · simp only [NativeLookupEquality.tickExecute,complete,ite_false,active,result,List.map_append,List.map_singleton]
          rw [done.2,fields.1,pending.2,valid.2.2.2,List.append_assoc]

theorem execute (basis : Module.Basis (Fin degree) (ZMod p) K) (w fuel : ℕ)
    (machine : NativeLookupEquality.Machine count K) (world : World) (earlier : List TranscriptFrame.Frame)
    (descriptorFits : (NativeExtensionDescriptor.descriptor degree w).length < TranscriptFrame.lengthLimit)
    (valid : Ordered world earlier machine) :
    Ordered world earlier (NativeLookupEquality.execute basis w fuel machine world).1 := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih => exact ih _ (tick basis w machine world earlier descriptorFits valid)

end
end FormalProof4FHE.HasteBoots.EqualityReceiptOrder
