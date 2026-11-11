module
public import FormalProof4FHE.HasteBoots.CanonicalScalarLifetime
@[expose] public section

/-! Original attained packets persist through program continuation with
unchanged canonical source/helper radii, input, message and scalar test. -/
namespace FormalProof4FHE.HasteBoots.CanonicalCandidateContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind runPrefix)
open ProgramContinuationPrefix (active_bind)
open CandidateContinuation (candidate packet)
noncomputable section
variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

theorem test (original : JobReferenceCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) (message : NativeScalarBatchWire.Message) :
    CanonicalCandidateTest.test (candidate original next) dummy message = CanonicalCandidateTest.test original dummy message := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  change (if (CanonicalCandidateScalarTest.info original).maxMultiplicands.val = 3 then _ else _) = _
  unfold CanonicalCandidateTest.test CanonicalCandidateScalarTest.fullTest CanonicalCandidateScalarTest.partialTest
    CanonicalCandidateTables.fullTables CanonicalCandidateTables.partialTables
    CanonicalCandidateFixation.sources CanonicalCandidateFixation.helpers
  simp only [same]
  rfl

theorem event {input : Input} {ordinal : ℕ} (next : A → Program B)
    (dummy : NativeRootMessage.Digest)
    (original : CanonicalAttainableEvent.Event program position input ordinal dummy world) :
    CanonicalAttainableEvent.Event (bind program next) position input ordinal dummy world := by
  obtain ⟨witness,occurred⟩ := original
  refine ⟨packet witness next,?_⟩
  change ScalarRecoveredUnboundedLaw.event _ _ _ (CanonicalCandidateTest.test (candidate witness.classed.val next) dummy witness.message) world
  rw [test]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : CanonicalScalarLifetime.Event program dummy world) :
    CanonicalScalarLifetime.Event (bind program next) dummy world := by
  obtain ⟨position,input,ordinal,occurred⟩ := original
  exact ⟨position,input,ordinal,event next dummy occurred⟩


theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | CanonicalScalarLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change CanonicalScalarLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact lifetime_event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.CanonicalCandidateContinuation
