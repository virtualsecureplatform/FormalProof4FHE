module
public import FormalProof4FHE.HasteBoots.OffsetClassKernel
public import FormalProof4FHE.HasteBoots.CompressionContinuation
public import FormalProof4FHE.HasteBoots.EqualityContinuation
@[expose] public section

/-! Original accepted-offset candidates and their attained reciprocal classes
persist through actual program continuation. The original complexity, first
read, whole source test and all-budget kernel remain attached to the job. -/
namespace FormalProof4FHE.HasteBoots.OffsetContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind run runPrefix)
open ProgramContinuationPrefix (active_bind log_prefix)
noncomputable section
variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

def candidate (original : LookupOffsetCompressionFixation.Candidate program position world) (next : A → Program B) :
    LookupOffsetCompressionFixation.Candidate (bind program next) position world :=
  ⟨⟨CompressionContinuation.candidate original.source next,original.grouped⟩,original.last,
    LookupReceiptLogs.mono world _ _ _ original.receipts (log_prefix program next world).sublist⟩

theorem sources (original : LookupOffsetCompressionFixation.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    LookupSourceCandidate.sources (candidate original next).source dummy = LookupSourceCandidate.sources original.source dummy :=
  CompressionContinuation.sources original.source next dummy

theorem test (original : LookupOffsetCompressionFixation.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) (y : NativeExtensionFields.Goldilocks3) :
    LookupReciprocalStatement.test (candidate original next).toCandidate dummy y = LookupReciprocalStatement.test original.toCandidate dummy y := by
  unfold LookupReciprocalStatement.test
  rw [sources]
  rfl

theorem kernel (original : LookupOffsetCompressionFixation.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    LookupOffsetKernel.Event (candidate original next) dummy = LookupOffsetKernel.Event original dummy := by
  unfold LookupOffsetKernel.Event
  rw [test]
  rfl

theorem event {input : Input} {ordinal cost : ℕ} (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : OffsetClassKernel.Event program position input ordinal cost dummy world) :
    OffsetClassKernel.Event (bind program next) position input ordinal cost dummy world := by
  obtain ⟨witness,occurred⟩ := original
  refine ⟨⟨candidate witness.val next,witness.property⟩,?_⟩
  rw [kernel]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : OffsetClassKernel.Lifetime program dummy world) :
    OffsetClassKernel.Lifetime (bind program next) dummy world := by
  obtain ⟨position,input,ordinal,cost,occurred⟩ := original
  exact ⟨position,input,ordinal,cost,event next dummy occurred⟩

theorem private_class_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | OffsetClassKernel.Event
      (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) position input ordinal cost dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change OffsetClassKernel.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) position input ordinal cost dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact event _ dummy occurred

theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | OffsetClassKernel.Lifetime
      (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change OffsetClassKernel.Lifetime (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact lifetime_event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.OffsetContinuation
