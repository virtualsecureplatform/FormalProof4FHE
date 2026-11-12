module
public import FormalProof4FHE.HasteBoots.FirstCompressionLifetime
public import FormalProof4FHE.HasteBoots.CompressionContinuation
@[expose] public section

/-! Original first-draw and validated-payload degree bounds persist under
actual program continuation, retaining the literal selecting observation. -/
namespace FormalProof4FHE.HasteBoots.FirstCompressionContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind)
noncomputable section
variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

def candidate (original : FirstCompressionCandidate.Candidate program position world) (next : A → Program B) :
    FirstCompressionCandidate.Candidate (bind program next) position world :=
  ⟨CompressionContinuation.candidate original.toCandidate next,original.head,original.bounded⟩

theorem event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : FirstCompressionWorkPosition.Event program position dummy world) :
    FirstCompressionWorkPosition.Event (bind program next) position dummy world := by
  obtain ⟨original,occurred⟩ := original
  refine ⟨candidate original next,?_⟩
  change LookupCompressionKernel.Event (CompressionContinuation.candidate original.toCandidate next) dummy world
  rw [CompressionContinuation.kernel]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : FirstCompressionLifetime.Event program dummy world) : FirstCompressionLifetime.Event (bind program next) dummy world := by
  obtain ⟨position,occurred⟩ := original
  exact ⟨position,event next dummy occurred⟩

theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | FirstCompressionLifetime.Event
      (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change FirstCompressionLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact lifetime_event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.FirstCompressionContinuation
