module
public import FormalProof4FHE.HasteBoots.ScalarChallengeInputView
public import FormalProof4FHE.HasteBoots.ScalarRoundHealingBound
@[expose] public section

/-! A parsed first-exposure input fixes the actual scalar round packet.
Its received degree is bounded by encoded input bytes, including variable
bincode integer spellings. This is a step toward adaptive exposure accounting,
not a whole-scalar-verifier or physical attacker-work theorem. -/
namespace FormalProof4FHE.HasteBoots.ScalarChallengeInputBound
open InputIndexedOracle (Input World law)
open NativeScalarBatchWire (Message RoundPacket Statement Info)
open NativeScalarBatchPreflight (dimensions bindCheckedRound)
open NativeTranscript (Transcript)
open NativeRootMessage (Digest)
open ScalarChallengeInputView (View)
open NativeExtensionFields (Goldilocks3)
open MeasureTheory ProbabilityTheory
noncomputable section

private theorem usize_positive (value : NativeUsizeMessage.Usize) : 0 < (NativeUsizeMessage.encode value).length := by
  unfold NativeUsizeMessage.encode
  split
  · simp
  · split
    · simp
    · split <;> simp

private theorem extension_positive (value : NativeFieldWire.GoldExtension) : 0 < (NativeFieldWire.goldExtension value).length := by
  unfold NativeFieldWire.goldExtension NativeIntegerPrefix.encodeVector
  rw [List.length_append]
  have positive := usize_positive ⟨(List.ofFn value).length,by simp⟩
  omega

private theorem flatMap_count {A : Type} (f : A → Input) (positive : ∀ value, 0 < (f value).length) (values : List A) :
    values.length ≤ (values.flatMap f).length := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [List.flatMap_cons,List.length_append,List.length_cons]; have := positive head; omega

private theorem member_size {A : Type} (f : A → Input) (values : List A) (value : A) (member : value ∈ values) :
    (f value).length ≤ (values.flatMap f).length := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | old
    · simp only [List.flatMap_cons,List.length_append]; omega
    · have bound := ih old
      simp only [List.flatMap_cons,List.length_append]
      omega

private theorem frame_size (frames : List TranscriptFrame.Frame) (frame : TranscriptFrame.Frame) (member : frame ∈ frames) :
    (TranscriptFrame.encode frame).length ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | old
    · simp only [TranscriptFrame.encodeMany,List.length_append]; omega
    · have bound := ih old
      simp only [TranscriptFrame.encodeMany,List.length_append]
      omega

theorem message_degree_size (message : Message) (degree : ℕ) (width : message.evaluations.val.length = degree+1) :
    degree < (NativeScalarBatchWire.messageCodec.encode message).length := by
  have count := flatMap_count NativeFieldWire.goldExtension extension_positive message.evaluations.val
  rw [NativeScalarBatchWire.message_encode,List.length_append]
  omega

theorem packet_degree_size (packet : RoundPacket) (index : ℕ) (message : Message)
    (found : packet.messages.val[index]? = some message) (degree : ℕ) (width : message.evaluations.val.length = degree+1) :
    degree < (NativeScalarBatchWire.roundCodec.encode packet).length := by
  have small := message_degree_size message degree width
  have bound := member_size NativeScalarBatchWire.messageCodec.encode packet.messages.val message (List.mem_of_getElem? found)
  rw [NativeScalarBatchWire.round_encode,List.length_append,List.length_append]
  omega

/-- Every degree charge is bounded by the original complete input length;
no fixed eight-byte integer encoding assumption is made. -/
theorem input_degree_size (input : Input) (view : View) (parsed : ScalarChallengeInputView.parse input = some view)
    (index : ℕ) (message : Message) (found : view.packet.messages.val[index]? = some message)
    (degree : ℕ) (width : message.evaluations.val.length = degree+1) : degree < input.length := by
  have encoded := (ScalarChallengeInputView.parse_sound input view parsed (fun _ => 0)).1
  rw [ScalarChallengeInputView.phase_input] at encoded
  have member : ScalarChallengeInputView.roundFrame view.packet ∈ view.frames := List.mem_append_right _ List.mem_cons_self
  have bound := frame_size view.frames _ member
  rw [encoded,TranscriptFrame.encode_length] at bound
  have packet := packet_degree_size view.packet index message found degree width
  change 17 + NativeScalarBatchWire.roundLabel.length + (NativeScalarBatchWire.roundCodec.encode view.packet).length ≤ input.length at bound
  omega

theorem degree_charge_le_input (input : Input) (view : View) (parsed : ScalarChallengeInputView.parse input = some view)
    (index : ℕ) (message : Message) (found : view.packet.messages.val[index]? = some message)
    (degree : ℕ) (width : message.evaluations.val.length = degree+1) :
    (degree : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) ≤
      (input.length : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  apply ENNReal.div_le_div_right
  exact_mod_cast (input_degree_size input view parsed index message found degree width).le

/-- Select before executing the first positive read; no oracle-world or
future response argument is used to recover the packet. -/
def select {S A : Type} (step : S → OracleMachine.Command S A) (history : (S ⊕ A) × List NativeTranscript.Observation) : Option View :=
  (CausalStreamExposure.firstRead step history).bind ScalarChallengeInputView.parse

theorem selected_origin {S A : Type} (step : S → OracleMachine.Command S A)
    (history : (S ⊕ A) × List NativeTranscript.Observation) (view : View) (profile : Digest)
    (selected : select step history = some view) :
    ∃ input : Input, CausalStreamExposure.firstRead step history = some input ∧
      ScalarChallengeInputView.parse input = some view ∧ (view.phase profile).pending.input = input := by
  obtain ⟨input,first,parsed⟩ := Option.bind_eq_some_iff.mp selected
  exact ⟨input,first,parsed,(ScalarChallengeInputView.parse_sound input view parsed profile).1⟩

/-- The packet is recovered from the actual first-read input, rather than
supplied independently. Other semantic round data are fixed on the fiber. -/
theorem selected_healing_bound {S A : Type} (step : S → OracleMachine.Command S A)
    {past : World → NativeTranscript.Execution (S ⊕ A)} (replay : ObservationReplay.Replayable past) (world : World)
    (dummy profile : Digest) (input : Input) (view : View)
    (parsed : ScalarChallengeInputView.parse input = some view)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (bound : Transcript) (expected : List NativeGoldExtensionArithmetic.Word)
    (accepted : bindCheckedRound ⟨TranscriptFrame.encodeMany view.before,profile⟩ view.packet expected = .ok bound)
    (statement : Statement) (admitted : dimensions statement = true) (info : Info) (member : info ∈ statement.infos.val)
    (index : ℕ) (message : Message) (prior : NativeGoldExtensionArithmetic.Word)
    (messageAt : view.packet.messages.val[index]? = some message) (priorAt : expected[index]? = some prior)
    (width : message.evaluations.val.length = info.maxMultiplicands.val+1)
    (honest : Polynomial Goldilocks3) (honestDegree : honest.natDegree ≤ info.maxMultiplicands.val)
    (falsePrior : honest.eval 0+honest.eval 1 ≠ NativeFieldWire.goldExtensionValue prior) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ScalarRoundHealingBound.Event ⟨TranscriptFrame.encodeMany view.before,profile⟩ view.packet message honest other} ≤
        (info.maxMultiplicands.val : ENNReal) / (NativeFields.goldilocksModulus^3 : ℕ) := by
  have first : CausalStreamExposure.firstRead step (past world).run = some (view.phase profile).pending.input := by
    rw [(ScalarChallengeInputView.parse_sound input view parsed profile).1]
    exact selected
  exact ScalarRoundHealingBound.event_bound step replay world dummy _ bound view.packet expected accepted first statement admitted info member
    index message prior messageAt priorAt width honest honestDegree falsePrior

end
end FormalProof4FHE.HasteBoots.ScalarChallengeInputBound
