module
public import FormalProof4FHE.HasteBoots.CompressionClassKernel
public import FormalProof4FHE.HasteBoots.EqualityContinuation
@[expose] public section

/-! Original lookup source candidates and their attained compression classes
persist through actual program continuation. The original complexity, first
read, whole source test and all-budget kernel remain attached to the job. -/
namespace FormalProof4FHE.HasteBoots.CompressionContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind run runPrefix)
open ProgramContinuationPrefix (active_bind log_prefix)
noncomputable section
variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

def candidate (original : LookupSourceCandidate.Candidate program position world) (next : A → Program B) :
    LookupSourceCandidate.Candidate (bind program next) position world := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  refine ⟨original.ctx,original.body,original.allocation,original.origin,original.index,original.job,original.geometry,
    CandidateContinuation.parent original.parent next same,original.registry,original.helper,original.requests,original.parentInput,
    original.draw,original.member,ProgramContinuationPrefix.first original.first next,original.first_position,?_⟩
  constructor
  · intro column
    obtain ⟨index,realized⟩ := original.ancestry.sources column
    exact ⟨index,EqualityContinuation.realized_prefix realized (log_prefix program next world)⟩
  · obtain ⟨index,realized⟩ := original.ancestry.helper
    exact ⟨index,EqualityContinuation.realized_prefix realized (log_prefix program next world)⟩

theorem sources (original : LookupSourceCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    LookupSourceCandidate.sources (candidate original next) dummy = LookupSourceCandidate.sources original dummy := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  unfold LookupSourceCandidate.sources
  simp only [same]
  rfl

theorem test (original : LookupSourceCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    LookupTupleTest.test (candidate original next) dummy = LookupTupleTest.test original dummy := by
  unfold LookupTupleTest.test
  rw [sources]
  rfl

theorem kernel (original : LookupSourceCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    LookupCompressionKernel.Event (candidate original next) dummy = LookupCompressionKernel.Event original dummy := by
  unfold LookupCompressionKernel.Event
  rw [test]
  rfl

theorem event {input : Input} {ordinal cost : ℕ} (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : CompressionClassKernel.Event program position input ordinal cost dummy world) :
    CompressionClassKernel.Event (bind program next) position input ordinal cost dummy world := by
  obtain ⟨witness,occurred⟩ := original
  refine ⟨⟨candidate witness.val next,witness.property⟩,?_⟩
  rw [kernel]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : CompressionClassKernel.Lifetime program dummy world) :
    CompressionClassKernel.Lifetime (bind program next) dummy world := by
  obtain ⟨position,input,ordinal,cost,occurred⟩ := original
  exact ⟨position,input,ordinal,cost,event next dummy occurred⟩

theorem private_class_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (position : ℕ) (input : Input) (ordinal cost : ℕ) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | CompressionClassKernel.Event
      (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) position input ordinal cost dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change CompressionClassKernel.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) position input ordinal cost dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact event _ dummy occurred

theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | CompressionClassKernel.Lifetime
      (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change CompressionClassKernel.Lifetime (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact lifetime_event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.CompressionContinuation
