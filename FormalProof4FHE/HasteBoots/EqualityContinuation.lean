module
public import FormalProof4FHE.HasteBoots.EqualityLogWork
@[expose] public section

/-! Original equality candidates and events persist through program
continuation, retaining original first exposure, complete decoded families,
observed endpoint receipts and the all-budget native equality kernel. -/
namespace FormalProof4FHE.HasteBoots.EqualityContinuation
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open OracleProgram (Program bind run runPrefix)
open ProgramContinuationPrefix (active_bind log_prefix)
noncomputable section

theorem realized_append {world : World} {log : List Observation} {input : Input} {index : ℕ} {fact : NativeSeedAncestry.Fact}
    (original : NativeSeedAncestry.Realized world log input index fact) (later : List Observation) :
    NativeSeedAncestry.Realized world (log++later) input index fact := by
  induction original with
  | direct input index frames parsed fact direct first =>
    exact .direct input index frames parsed fact direct (OracleFirstExposure.locate_preserved log later _ index first)
  | inherit input index frames parsed parent parentIndex fact previous quoted first ih =>
    exact .inherit input index frames parsed parent parentIndex fact ih quoted (OracleFirstExposure.locate_preserved log later _ index first)

theorem realized_prefix {world : World} {before after : List Observation} {input : Input} {index : ℕ} {fact : NativeSeedAncestry.Fact}
    (original : NativeSeedAncestry.Realized world before input index fact) (included : before.IsPrefix after) :
    NativeSeedAncestry.Realized world after input index fact := by
  obtain ⟨later,rfl⟩ := included
  exact realized_append original later

variable {A B : Type} {program : Program A} {position : ℕ} {world : World}

def family (original : EqualityFamilyCandidate.Candidate program position world) (next : A → Program B) :
    EqualityFamilyCandidate.Candidate (bind program next) position world := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.first_position]
    exact congrArg Prod.snd (active_bind program next original.first.position world _ original.first.active)
  refine {
    selection := CandidateContinuation.selection original.selection next same
    draw := original.draw
    drawAt := original.drawAt
    input := original.input
    first := ProgramContinuationPrefix.first original.first next
    first_position := original.first_position
    ancestry := ?_
    rootsFit := original.rootsFit }
  constructor
  · intro column
    obtain ⟨index,realized⟩ := original.ancestry.sources column
    exact ⟨index,realized_prefix realized (log_prefix program next world)⟩
  · obtain ⟨index,realized⟩ := original.ancestry.helper
    exact ⟨index,realized_prefix realized (log_prefix program next world)⟩

def factor {input : Input} {ordinal : ℕ} {side : EqualityLookupFactorFixation.Side}
    (original : EqualityFactorCandidate.At program world input ordinal side) (next : A → Program B) :
    EqualityFactorCandidate.At (bind program next) world input ordinal side :=
  ⟨original.value,original.world_eq,original.input_eq,original.ordinal_eq,original.side_eq,
    (log_prefix program next original.value.world).sublist.subset original.observed⟩

def candidate (original : EqualityFactorCandidate.Candidate program position world) (next : A → Program B) :
    EqualityFactorCandidate.Candidate (bind program next) position world :=
  ⟨family original.family next,factor original.compression next,factor original.offset next,original.y,original.r⟩

theorem residual (original : EqualityFactorCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    EqualityCandidateResidual.residual (candidate original next) dummy = EqualityCandidateResidual.residual original dummy := by
  have same : (runPrefix position (bind program next) world).run.2 = (runPrefix position program world).run.2 := by
    rw [← original.family.first_position]
    exact congrArg Prod.snd (active_bind program next original.family.first.position world _ original.family.first.active)
  unfold EqualityCandidateResidual.residual EqualityCandidateResidual.scalar EqualityFamilyCandidate.sources EqualityFamilyCandidate.helpers
  simp only [same]
  rfl

theorem test (original : EqualityFactorCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    EqualityCandidateResidual.test (candidate original next) dummy = EqualityCandidateResidual.test original dummy := by
  unfold EqualityCandidateResidual.test
  rw [residual]
  rfl

theorem kernel (original : EqualityFactorCandidate.Candidate program position world) (next : A → Program B)
    (dummy : NativeRootMessage.Digest) :
    EqualityCandidateKernel.Event (candidate original next) dummy = EqualityCandidateKernel.Event original dummy := by
  funext other
  unfold EqualityCandidateKernel.Event
  rw [test]
  rfl

theorem event {input : Input} {ordinal : ℕ} (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : EqualityClassKernel.Event program position input ordinal dummy world) :
    EqualityClassKernel.Event (bind program next) position input ordinal dummy world := by
  obtain ⟨witness,occurred⟩ := original
  refine ⟨⟨candidate witness.val next,witness.property⟩,?_⟩
  rw [kernel]
  exact occurred

theorem lifetime_event (next : A → Program B) (dummy : NativeRootMessage.Digest)
    (original : EqualityLifetime.Event program dummy world) : EqualityLifetime.Event (bind program next) dummy world := by
  obtain ⟨position,input,ordinal,occurred⟩ := original
  exact ⟨position,input,ordinal,event next dummy occurred⟩

theorem private_monotone (code : List PrivateCoinByteMachine.Instruction) (publicData : Input) (tape : PrivateCoinReplay.Tape)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : NativeRootMessage.Digest) :
    Monotone (fun fuel => {world | EqualityLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData fuel) dummy world}) := by
  intro first later ordered world occurred
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le ordered
  change EqualityLifetime.Event (InterpreterScalarLifetime.privateProgram code publicData tape privateData (first+extra)) dummy world
  unfold InterpreterScalarLifetime.privateProgram at occurred ⊢
  rw [PrivateCoinByteMachine.take_resume]
  exact lifetime_event _ dummy occurred

end
end FormalProof4FHE.HasteBoots.EqualityContinuation
