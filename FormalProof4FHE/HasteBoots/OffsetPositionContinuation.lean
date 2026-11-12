module
public import FormalProof4FHE.HasteBoots.OffsetPositionKernel
public import FormalProof4FHE.HasteBoots.OffsetContinuation
@[expose] public section

/-! Aggregating inputs, job ordinals and costs does not discard original
continuation witnesses or alter their literal first-read position. -/
namespace FormalProof4FHE.HasteBoots.OffsetPositionContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind)
noncomputable section

theorem event {A B : Type} {program : Program A} {position budget : ℕ} {world : World}
    (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : OffsetPositionKernel.Event program position budget dummy world) :
    OffsetPositionKernel.Event (bind program next) position budget dummy world := by
  obtain ⟨input,ordinal,cost,bounded,occurred⟩ := original
  exact ⟨input,ordinal,cost,bounded,OffsetContinuation.event next dummy occurred⟩

theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (position budget : ℕ) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | OffsetPositionKernel.Event
      (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) position budget dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change OffsetPositionKernel.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) position budget dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.OffsetPositionContinuation
