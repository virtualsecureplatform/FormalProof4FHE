module
public import FormalProof4FHE.HasteBoots.CanonicalSumLifetime
@[expose] public section

/-! Original attained sum packets persist through program continuation,
retaining their even message, canonical helper family and challenge test. -/
namespace FormalProof4FHE.HasteBoots.CanonicalSumContinuation
open InputIndexedOracle (Input World)
open OracleProgram (Program bind runPrefix)
open ProgramContinuationPrefix (active_bind)
open CandidateContinuation (candidate)
noncomputable section
variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

theorem test (original : JobReferenceCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) (message : NativeScalarBatchWire.Message) :
    CanonicalSumCandidate.test (candidate original next) dummy message = CanonicalSumCandidate.test original dummy message := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  unfold CanonicalSumCandidate.test CanonicalSumCandidate.tables CanonicalCandidateFixation.helpers
  simp only [same]
  rfl

def packet {input : Input} {ordinal : ℕ} (original : CanonicalSumAttainableEvent.Packet program position input ordinal world)
    (next : A → Program B) : CanonicalSumAttainableEvent.Packet (bind program next) position input ordinal world :=
  ⟨⟨candidate original.classed.val next,original.classed.property⟩,original.message,original.messageAt,
    original.configuration,original.found⟩

theorem event {input : Input} {ordinal : ℕ} (next : A → Program B)
    (dummy : NativeRootMessage.Digest)
    (original : CanonicalSumAttainableEvent.Event program position input ordinal dummy world) :
    CanonicalSumAttainableEvent.Event (bind program next) position input ordinal dummy world := by
  obtain ⟨witness,occurred⟩ := original
  refine ⟨packet witness next,?_⟩
  change ScalarRecoveredUnboundedLaw.event _ _ _ (CanonicalSumCandidate.test (candidate witness.classed.val next) dummy witness.message) world
  rw [test]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : CanonicalSumLifetime.Event program dummy world) :
    CanonicalSumLifetime.Event (bind program next) dummy world := by
  obtain ⟨position,input,ordinal,occurred⟩ := original
  exact ⟨position,input,ordinal,event next dummy occurred⟩


theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | CanonicalSumLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change CanonicalSumLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact lifetime_event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.CanonicalSumContinuation
