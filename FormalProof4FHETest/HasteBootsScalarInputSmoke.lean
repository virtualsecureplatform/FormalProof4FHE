module
import all FormalProof4FHE.HasteBoots.ScalarChallengeInputBound
import all FormalProof4FHETest.HasteBootsScalarHealingSmoke

namespace FormalProof4FHE.HasteBoots.ScalarInputSmoke
open HasteBootsScalarFinishAncestrySmoke (statement info message zero firstPacket singleProof)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open NativeScalarBatchWire (roundCodec messageCodec)
open ScalarChallengeInputView (View roundFrame typedFrame extensionFrame basisFrame fieldFrame parse)
open TranscriptFrame (encodeMany)
open OracleProgram (run)
open InputIndexedOracle (World)
open MeasureTheory ProbabilityTheory
noncomputable section

def transcript := NativeScalarBatchWire.bindStatement child statement
def packet := firstPacket message
def phase := ScalarRoundChallengeMeaning.phase transcript packet
def before := (TranscriptFrame.decodeAll transcript.input).get (by decide +kernel)
theorem parentParsed : TranscriptFrame.decodeAll transcript.input = some before := (Option.some_get _).symm
def view : View := ⟨before,packet⟩
theorem parsed : parse phase.pending.input = some view :=
  ScalarChallengeInputView.actual_parse transcript before packet parentParsed (by decide +kernel)

/-- The online verifier's actual first round creates this same request. -/
example : (NativeScalarBatchVerifier.tickExecute statement (singleProof message)
      (NativeScalarBatchVerifier.initial child statement (singleProof message)) worldZero).1.control =
    .sampling packet (NativeFieldVector.initial phase 3) := rfl

/-- The original round ordinal and raw message are retained exactly. -/
example : view.packet.round.val = 0 ∧ view.packet.messages.val = [message] := ⟨rfl,rfl⟩

def usize (value : ℕ) : NativeUsizeMessage.Usize := ⟨value % 2^64,Nat.mod_lt _ (by decide)⟩

def aliasZero : NativeFieldWire.GoldExtension := ![usize NativeFields.goldilocksModulus,0,0]
def aliasMessage : NativeScalarBatchWire.Message := ⟨⟨[aliasZero,aliasZero],by decide⟩⟩
def aliasPacket := firstPacket aliasMessage
def aliasView : View := ⟨before,aliasPacket⟩
theorem aliasParsed : parse (ScalarRoundChallengeMeaning.phase transcript aliasPacket).pending.input = some aliasView :=
  ScalarChallengeInputView.actual_parse transcript before aliasPacket parentParsed (by decide +kernel)

example : NativeGoldInterpolation.equal zero aliasZero = true ∧ packet ≠ aliasPacket := by decide +kernel

/-- Field-equivalent raw spellings still create different original inputs. -/
example : phase.pending.input ≠ (ScalarRoundChallengeMeaning.phase transcript aliasPacket).pending.input := by
  intro same
  have first := parsed
  rw [same] at first
  have equal := ScalarChallengeInputView.packet_unique _ view aliasView first aliasParsed
  have different : packet ≠ aliasPacket := by decide +kernel
  exact different equal

/-- Bincode varints change payload size; a fixed-u64 size assumption is false. -/
example : (messageCodec.encode message).length = 9 ∧ (messageCodec.encode aliasMessage).length = 25 := by decide +kernel

def badRound : TranscriptFrame.Frame := {roundFrame packet with message := roundCodec.encode packet ++ [42]}
def vectorTyped : TranscriptFrame.Frame := {typedFrame with message := TypedFieldRequest.kindBytes .vector}
def wrongBasis : TranscriptFrame.Frame := {basisFrame with message := NativeExtensionDescriptor.descriptor 3 5}

/-- An earlier good round cannot rescue trailing bytes in the adjacent one. -/
example : (parse (encodeMany (before ++ [roundFrame packet,badRound,typedFrame,extensionFrame,basisFrame,fieldFrame]))).isNone = true := by decide +kernel
example : (parse (encodeMany (before ++ [roundFrame packet,vectorTyped,extensionFrame,basisFrame,fieldFrame]))).isNone = true := by decide +kernel
example : (parse (encodeMany (before ++ [roundFrame packet,typedFrame,extensionFrame,wrongBasis,fieldFrame]))).isNone = true := by decide +kernel
example : (parse (encodeMany (before ++ [roundFrame packet,typedFrame,basisFrame,extensionFrame,fieldFrame]))).isNone = true := by decide +kernel

example : 1 < phase.pending.input.length := ScalarChallengeInputBound.input_degree_size _ view parsed 0 message rfl 1 rfl

def step (_ : Unit) : OracleMachine.Command Unit Unit := .read phase.pending.input 99 1 (fun _ => ())
example : ScalarChallengeInputBound.select step (ScalarHealingSmoke.past worldZero).run = some view := by
  change (some phase.pending.input).bind parse = some view
  exact parsed

/-- The causal parsed input supplies the packet in the native healing bound. -/
example : (InputIndexedOracle.law[|{other | (ScalarHealingSmoke.past other).run = (ScalarHealingSmoke.past worldZero).run}])
    {other | ScalarRoundHealingBound.Event transcript packet message Polynomial.X other} ≤
      (1 : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have restored : (⟨encodeMany before,transcript.profile⟩ : NativeTranscript.Transcript) = transcript :=
    ScalarChallengeInputView.rebuild_transcript transcript before parentParsed
  have falsePrior : (Polynomial.X : Polynomial NativeExtensionFields.Goldilocks3).eval 0 + Polynomial.X.eval 1 ≠ NativeFieldWire.goldExtensionValue zero := by
    have same : zero = NativeGoldLookup.zero := by funext i; fin_cases i <;> rfl
    simp [same,NativeGoldLookup.zero_value]
  have bound := ScalarChallengeInputBound.selected_healing_bound step ScalarHealingSmoke.replay worldZero (fun _ => 0) transcript.profile
    phase.pending.input view parsed rfl (NativeScalarBatchWire.bindRound ⟨encodeMany before,transcript.profile⟩ packet) [zero] rfl statement
    (by decide +kernel) info (by simp [statement]) 0 message zero rfl rfl rfl Polynomial.X
    (by change (Polynomial.X : Polynomial NativeExtensionFields.Goldilocks3).natDegree ≤ 1; simp) falsePrior
  simpa only [view,restored,show info.maxMultiplicands.val = 1 from rfl,Nat.cast_one] using bound

end
end FormalProof4FHE.HasteBoots.ScalarInputSmoke
