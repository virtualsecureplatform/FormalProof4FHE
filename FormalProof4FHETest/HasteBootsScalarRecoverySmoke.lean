module
import all FormalProof4FHE.HasteBoots.ScalarProofPrefixExecution
import all FormalProof4FHETest.HasteBootsScalarReplaySmoke

namespace FormalProof4FHE.HasteBoots.ScalarRecoverySmoke
open ScalarReplaySmoke (target statement proof secondPacket)
open HasteBootsScalarFinishAncestrySmoke (message firstPacket)
open HasteBootsSamplerAncestrySmoke (worldZero child)
open ScalarTranscriptPrefix (statementFrame receiptFrame block)
open ScalarChallengeInputView (roundFrame typedFrame extensionFrame basisFrame fieldFrame)
open InputIndexedOracle (World)
open MeasureTheory ProbabilityTheory
noncomputable section


private theorem checked_valid (frames : List TranscriptFrame.Frame)
    (checked : frames.all (fun frame => decide (frame.label.length < TranscriptFrame.lengthLimit ∧ frame.message.length < TranscriptFrame.lengthLimit)) = true) :
    ∀ frame ∈ frames, TranscriptFrame.Valid frame := by
  intro frame member
  change frame.label.length < TranscriptFrame.lengthLimit ∧ frame.message.length < TranscriptFrame.lengthLimit
  exact of_decide_eq_true (List.all_eq_true.mp checked frame member)

def childFrames := (TranscriptFrame.decodeAll child.input).get (by decide +kernel)
def firstReceipt := (NativeTranscript.receipt worldZero (List.replicate 24 0)).run.1
def history : ScalarTranscriptPrefix.History := ⟨childFrames,statement,[(firstPacket message,firstReceipt)]⟩
def expectedView : ScalarTranscriptPrefix.View := ⟨history,secondPacket⟩
def recoveredProof := (ScalarPrefixProof.reconstruct expectedView).get (by decide +kernel)
def recovered : ScalarRecoveredReplay.Configuration := ⟨expectedView,recoveredProof⟩
theorem found : ScalarRecoveredReplay.recover target = some recovered := by
  have inputEq : target = TranscriptFrame.encodeMany (ScalarChallengeInputView.View.mk history.frames secondPacket).frames := by decide +kernel
  rw [inputEq]
  exact ScalarRecoveredReplay.recover_native expectedView child.profile
    (checked_valid _ (by decide +kernel)) (by intro pair member; have same : pair = (firstPacket message,firstReceipt) := List.mem_singleton.mp member; subst pair; rfl)
    recoveredProof (Option.some_get _).symm

/-- Recover the original statement and both raw message rows directly from
an actual second-round challenge input. -/
example : recovered.view.history.statement = statement ∧ recovered.view.packet = secondPacket := by decide +kernel
example : recovered.view.history.rounds.map (fun pair => pair.1) = [firstPacket message] := by decide +kernel
example : recovered.proof.val.map (fun certificate => certificate.val) = [[message,message]] := by decide +kernel
example : recovered.view.history.before = (TranscriptFrame.decodeAll child.input).get (by decide +kernel) := by decide +kernel

/-- No caller-supplied proof association is needed for the native getter. -/
example : NativeScalarBatchRoundPacket.packet recovered.view.packet.round recovered.proof = some recovered.view.packet :=
  ScalarRecoveredReplay.current_packet target recovered found
example : (recovered.initial child.profile).state.expected = statement.claims.val := by decide +kernel

/-- The recovered executable replay really stops at the second native round
and retains the original seven primitive observations. -/
def replay (world : World) := (OracleProgram.run (ScalarRecoveredReplay.program target child.profile 20) world).run
example : (replay worldZero).1.map (fun result => (result.1,result.2.completed.length)) = some (true,1) ∧
    (replay worldZero).2.length = 7 := by decide +kernel
example (world : World) : CausalStreamExposure.seen (replay world).2 target = false :=
  ScalarRecoveredReplay.unseen target child.profile 20 world
example : (recovered.phase child.profile).pending.input = target := ScalarRecoveredReplay.phase_input target recovered found child.profile

def currentView : ScalarChallengeInputView.View := ⟨recovered.view.history.frames,recovered.view.packet⟩
def inputWith (history : ScalarTranscriptPrefix.History) (packet : NativeScalarBatchWire.RoundPacket) : InputIndexedOracle.Input :=
  TranscriptFrame.encodeMany (ScalarChallengeInputView.View.mk history.frames packet).frames

def trailingStatement : TranscriptFrame.Frame :=
  {statementFrame statement with message := NativeScalarBatchWire.statementCodec.encode statement ++ [42]}
def earlierFrames := recovered.view.history.before ++ [statementFrame statement,trailingStatement]
def brokenStatement := TranscriptFrame.encodeMany
  (earlierFrames ++ [roundFrame (firstPacket message),typedFrame,extensionFrame,basisFrame,fieldFrame,
    receiptFrame firstReceipt,roundFrame secondPacket,typedFrame,extensionFrame,basisFrame,fieldFrame])

/-- An earlier valid statement cannot rescue a malformed adjacent statement. -/
example : (ScalarRecoveredReplay.recover brokenStatement).isNone = true := by decide +kernel

/-- The completed round's receipt width is checked, not guessed or truncated. -/
def shortHistory := {recovered.view.history with rounds := [(firstPacket message,[0])]}
example : (ScalarRecoveredReplay.recover (inputWith shortHistory secondPacket)).isNone = true := by decide +kernel

/-- Syntactically valid packets with wrong ordinal ordering fail reconstruction. -/
def wrongOrdinal := {secondPacket with round := HasteBootsScalarFinishAncestrySmoke.usize 0}
example : (ScalarRecoveredReplay.recover (inputWith recovered.view.history wrongOrdinal)).isNone = true := by decide +kernel

/-- Raw lazy field aliases survive reconstruction without canonicalization. -/
def aliasPacket := {secondPacket with messages := ⟨[ScalarInputSmoke.aliasMessage],by decide⟩}
def aliasInput := inputWith recovered.view.history aliasPacket
def aliasView : ScalarTranscriptPrefix.View := ⟨history,aliasPacket⟩
def aliasRecovered : ScalarRecoveredReplay.Configuration := ⟨aliasView,(ScalarPrefixProof.reconstruct aliasView).get (by decide +kernel)⟩
theorem aliasFound : ScalarRecoveredReplay.recover aliasInput = some aliasRecovered :=
  ScalarRecoveredReplay.recover_native aliasView child.profile (checked_valid _ (by decide +kernel))
    (by intro pair member; have same : pair = (firstPacket message,firstReceipt) := List.mem_singleton.mp member; subst pair; rfl)
    _ (Option.some_get _).symm
example : aliasRecovered.proof.val.map (fun certificate => certificate.val) = [[message,ScalarInputSmoke.aliasMessage]] := by decide +kernel

/-- With one more unexposed round, only that suffix reuses the selected row. -/
def threeInfo : NativeScalarBatchWire.Info := ⟨HasteBootsScalarFinishAncestrySmoke.usize 1,HasteBootsScalarFinishAncestrySmoke.usize 3⟩
def threeStatement : NativeScalarBatchWire.Statement := {statement with infos := ⟨[threeInfo],by decide⟩}
def threeHistory := {recovered.view.history with statement := threeStatement}
def threeInput := inputWith threeHistory aliasPacket
def threeView : ScalarTranscriptPrefix.View := ⟨threeHistory,aliasPacket⟩
def threeRecovered : ScalarRecoveredReplay.Configuration := ⟨threeView,(ScalarPrefixProof.reconstruct threeView).get (by decide +kernel)⟩
theorem threeFound : ScalarRecoveredReplay.recover threeInput = some threeRecovered :=
  ScalarRecoveredReplay.recover_native threeView child.profile (checked_valid _ (by decide +kernel))
    (by intro pair member; have same : pair = (firstPacket message,firstReceipt) := List.mem_singleton.mp member; subst pair; rfl)
    _ (Option.some_get _).symm
example : threeRecovered.proof.val.map (fun certificate => certificate.val) =
    [[message,ScalarInputSmoke.aliasMessage,ScalarInputSmoke.aliasMessage]] := by decide +kernel

/-- The original unseen suffix can differ and even fail its later recurrence.
It cannot change the earlier selected second-round prefix. -/
def originalThreeProof : NativeScalarBatchPreflight.Proof :=
  ⟨[⟨[message,ScalarInputSmoke.aliasMessage,HasteBootsScalarFinishAncestrySmoke.badMessage],by decide⟩],by decide⟩
def originalStart := NativeScalarBatchVerifier.initial (threeRecovered.parent child.profile) threeStatement originalThreeProof

private theorem agree_first : ScalarProofPrefixExecution.AgreeAt originalThreeProof threeRecovered.proof 0 := by
  intro index value
  have same : index = HasteBootsScalarFinishAncestrySmoke.usize 0 := Fin.ext value
  subst index
  have original : NativeScalarBatchRoundPacket.packet (HasteBootsScalarFinishAncestrySmoke.usize 0) originalThreeProof = some (firstPacket message) := rfl
  have restored := ScalarRecoveredReplay.prior_packet threeInput threeRecovered threeFound 0 (firstPacket message,firstReceipt) rfl
  exact original.trans restored.symm

private theorem agree_second : ScalarProofPrefixExecution.AgreeAt originalThreeProof threeRecovered.proof 1 := by
  intro index value
  have same : index = HasteBootsScalarFinishAncestrySmoke.usize 1 := Fin.ext value
  subst index
  have original : NativeScalarBatchRoundPacket.packet (HasteBootsScalarFinishAncestrySmoke.usize 1) originalThreeProof = some aliasPacket := rfl
  exact original.trans (ScalarRecoveredReplay.current_packet threeInput threeRecovered threeFound).symm

example : originalStart = threeRecovered.initial child.profile :=
  ScalarProofPrefixExecution.initial_eq _ _ threeStatement originalThreeProof threeRecovered.proof
    ((NativeScalarBatchPreflight.beginVerify_ok_iff _ _ _ _).mpr ⟨by decide +kernel,by decide +kernel,rfl⟩)
    (ScalarRecoveredReplay.initialized threeInput threeRecovered threeFound child.profile)

example : NativeScalarBatchVerifier.execute threeStatement originalThreeProof 5 originalStart worldZero =
    NativeScalarBatchVerifier.execute threeStatement threeRecovered.proof 5 originalStart worldZero := by
  apply ScalarProofPrefixExecution.execute_eq
  intro index bound _
  have small : (NativeScalarBatchVerifier.execute threeStatement originalThreeProof index originalStart worldZero).1.state.round < 2 := by
    interval_cases index <;> decide +kernel
  have either : (NativeScalarBatchVerifier.execute threeStatement originalThreeProof index originalStart worldZero).1.state.round = 0 ∨
      (NativeScalarBatchVerifier.execute threeStatement originalThreeProof index originalStart worldZero).1.state.round = 1 := by omega
  rcases either with first | second
  · rw [first]; exact agree_first
  · rw [second]; exact agree_second

/-- The later executions really differ; no equivalence of the entire filled
proof and the original proof is asserted. -/
example : (match (NativeScalarBatchVerifier.execute threeStatement originalThreeProof 9 originalStart worldZero).1.control with
    | .failed (.reject .recurrence) => true | _ => false) = true ∧
    (match (NativeScalarBatchVerifier.execute threeStatement threeRecovered.proof 9 originalStart worldZero).1.control with
    | .sampling _ _ => true | _ => false) = true := by decide +kernel

/-- A guessed but wrong receipt remains parseable bytes. Actual replay does
not infer a challenge from it or pretend it reached the selected input. -/
def guessedHistory := {recovered.view.history with rounds := [(firstPacket message,List.replicate 80 0)]}
def guessedInput := inputWith guessedHistory secondPacket
example : (ScalarRecoveredReplay.recover guessedInput).isSome = true := by decide +kernel
example : ((OracleProgram.run (ScalarRecoveredReplay.program guessedInput child.profile 20) worldZero).run.1).map
    (fun result => (result.1,result.2.completed.length)) = some (false,2) := by decide +kernel

/-- Malformed input fails with no primitive observations. -/
example : (OracleProgram.run (ScalarRecoveredReplay.program [255] child.profile 20) worldZero).run.2 = [] := by decide +kernel

/-- The cubic-field bound consumes the recovered configuration alone. -/
example : (InputIndexedOracle.law[|{other | (ScalarHealingSmoke.past other).run = (ScalarHealingSmoke.past worldZero).run}])
    {other | ∃ fuel, ScalarReplayChallengeLaw.event target recovered.view.history.statement recovered.proof 20
      (recovered.initial child.profile) fuel (recovered.phase child.profile)
      (fun _ value => (Polynomial.C (0 : NativeExtensionFields.Goldilocks3)).eval value = Polynomial.X.eval value) other} ≤
        (1 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have bound := ScalarRecoveredReplay.eventual_agreement_bound ScalarHealingSmoke.replay ScalarReplaySmoke.step worldZero
    (fun _ => 0) child.profile target recovered found rfl 20
    (fun _ => Polynomial.C 0) (fun _ => Polynomial.X) 1
    (by intro state same; have coefficient := congrArg (fun poly : Polynomial NativeExtensionFields.Goldilocks3 => poly.coeff 1) same; simp at coefficient)
    (by intro state; simp) (by intro state; simp)
  simpa only [Nat.cast_one] using bound

end
end FormalProof4FHE.HasteBoots.ScalarRecoverySmoke
