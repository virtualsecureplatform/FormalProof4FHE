module
public import FormalProof4FHE.HasteBoots.ScalarChallengeInputView
@[expose] public section

/-! Strict recovery of the original scalar statement and preceding round
packets from a selected challenge input. Completed receipt bytes are retained
as bytes; decoding a digest does not reveal the earlier challenge. -/
namespace FormalProof4FHE.HasteBoots.ScalarTranscriptPrefix
open InputIndexedOracle (Input)
open TranscriptFrame (Frame encodeMany)
open NativeScalarBatchWire (Statement RoundPacket statementCodec statementLabel challengeLabel)
open ScalarChallengeInputView (roundFrame typedFrame extensionFrame basisFrame fieldFrame)

def statementFrame (statement : Statement) : Frame := ⟨1,statementLabel,statementCodec.encode statement⟩
def receiptFrame (bytes : Input) : Frame := ⟨5,challengeLabel,bytes⟩
def block (packet : RoundPacket) (receipt : Input) : List Frame :=
  [roundFrame packet,typedFrame,extensionFrame,basisFrame,fieldFrame,receiptFrame receipt]

structure History where
  before : List Frame
  statement : Statement
  rounds : List (RoundPacket × Input)

def History.frames (history : History) : List Frame :=
  history.before ++ [statementFrame history.statement] ++ history.rounds.flatMap (fun pair => block pair.1 pair.2)

def readStatement (frame : Frame) : Option Statement :=
  (statementCodec.read frame.message).bind (fun (statement,tail) =>
    if frame = statementFrame statement ∧ tail = [] then some statement else none)

theorem readStatement_native (statement : Statement) : readStatement (statementFrame statement) = some statement := by
  have decoded := NativeScalarBatchWire.statement_roundtrip statement []
  rw [List.append_nil] at decoded
  simp only [readStatement,statementFrame,decoded,Option.bind_some,and_self,ite_true]

theorem readStatement_sound (frame : Frame) (statement : Statement)
    (parsed : readStatement frame = some statement) : frame = statementFrame statement := by
  unfold readStatement at parsed
  obtain ⟨⟨value,tail⟩,_,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  dsimp only at parsed
  split at parsed
  next valid => cases Option.some.inj parsed; exact valid.1
  next => contradiction

/-- Read backwards through adjacent complete six-frame rounds. The first
statement must be immediately adjacent; no label search skips malformed data. -/
def readHistory (frames : List Frame) : Option History :=
  match frames with
  | [] => none
  | frame :: rest =>
      match readStatement frame with
      | some statement => some ⟨rest.reverse,statement,[]⟩
      | none =>
          match rest with
          | field :: basis :: extension :: typed :: round :: earlier =>
              if frame = receiptFrame frame.message ∧ frame.message.length = 80 ∧
                  field = fieldFrame ∧ basis = basisFrame ∧ extension = extensionFrame ∧ typed = typedFrame then
                (ScalarChallengeInputView.readRound round).bind (fun packet =>
                  (readHistory earlier).map (fun history => {history with rounds := history.rounds ++ [(packet,frame.message)]}))
              else none
          | _ => none
termination_by frames.length

/-- The complete retained byte prefix has the exact recovered decomposition. -/
theorem readHistory_sound (frames : List Frame) (history : History)
    (parsed : readHistory frames = some history) : frames = history.frames.reverse := by
  induction frames using (measure (fun frames : List Frame => frames.length)).wf.induction generalizing history with
  | h frames ih =>
    rw [readHistory.eq_def] at parsed
    split at parsed
    next => contradiction
    next frame rest =>
      split at parsed
      next statement decoded =>
        cases Option.some.inj parsed
        have same := readStatement_sound frame statement decoded
        simp only [History.frames,List.flatMap_nil,List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.reverse_reverse]
        rw [same]
        rfl
      next rejected =>
        split at parsed
        next field basis extension typed round earlier =>
          split at parsed
          next valid =>
            obtain ⟨packet,roundParsed,parsed⟩ := Option.bind_eq_some_iff.mp parsed
            obtain ⟨prior,priorParsed,same⟩ := Option.map_eq_some_iff.mp parsed
            subst history
            have smaller : earlier.length < (frame :: field :: basis :: extension :: typed :: round :: earlier).length := by simp only [List.length_cons]; omega
            have before := ih earlier smaller prior priorParsed
            have roundEq := ScalarChallengeInputView.readRound_sound round packet roundParsed
            simp only [History.frames,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
              List.reverse_append,block,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
            have tailEq : earlier =
                (prior.rounds.flatMap (fun pair => block pair.1 pair.2)).reverse ++
                  statementFrame prior.statement :: prior.before.reverse := by
              simpa only [History.frames,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append] using before
            simp only [block] at tailEq
            rw [← tailEq]
            rw [valid.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,valid.2.2.2.2.2,roundEq]
            rfl
          next => contradiction
        next => contradiction

theorem receipt_not_statement (bytes : Input) : readStatement (receiptFrame bytes) = none := by
  cases found : readStatement (receiptFrame bytes) with
  | none => rfl
  | some statement =>
    have kind := congrArg Frame.kind (readStatement_sound _ statement found)
    have value := congrArg Fin.val kind
    change 5 = 1 at value
    contradiction

theorem readHistory_statement (before : List Frame) (statement : Statement) :
    readHistory (statementFrame statement :: before.reverse) = some ⟨before,statement,[]⟩ := by
  rw [readHistory.eq_def]
  simp only [readStatement_native,List.reverse_reverse]

theorem readHistory_snoc (history : History) (packet : RoundPacket) (receipt : Input)
    (length : receipt.length = 80) (prior : readHistory history.frames.reverse = some history) :
    readHistory ({history with rounds := history.rounds ++ [(packet,receipt)]}.frames.reverse) =
      some {history with rounds := history.rounds ++ [(packet,receipt)]} := by
  have frames : ({history with rounds := history.rounds ++ [(packet,receipt)]}.frames.reverse) =
      receiptFrame receipt :: fieldFrame :: basisFrame :: extensionFrame :: typedFrame :: roundFrame packet :: history.frames.reverse := by
    simp only [History.frames,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,block,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
  rw [frames,readHistory.eq_def]
  dsimp only
  rw [receipt_not_statement]
  simp only [receiptFrame,length,and_self,ite_true,
    ScalarChallengeInputView.readRound_native,Option.bind_some,prior,Option.map_some]

theorem readHistory_native (history : History) (lengths : ∀ pair ∈ history.rounds, pair.2.length = 80) :
    readHistory history.frames.reverse = some history := by
  cases history with
  | mk before statement rounds =>
    induction rounds using List.reverseRecOn with
    | nil =>
      simpa only [History.frames,List.flatMap_nil,List.append_nil,List.reverse_append,List.reverse_cons,
        List.reverse_nil,List.nil_append,List.cons_append] using readHistory_statement before statement
    | append_singleton earlier pair ih =>
      exact readHistory_snoc ⟨before,statement,earlier⟩ pair.1 pair.2
        (lengths pair (by simp)) (ih (fun p member => lengths p (List.mem_append_left _ member)))

structure View where
  history : History
  packet : RoundPacket

def parse (input : Input) : Option View :=
  (ScalarChallengeInputView.parse input).bind (fun current =>
    (readHistory current.before.reverse).map (fun history => ⟨history,current.packet⟩))

/-- The selected input reconstructs the original parent frames and every
adjacent completed raw packet, without querying either ideal oracle. -/
theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) :
    ScalarChallengeInputView.parse input = some ⟨view.history.frames,view.packet⟩ := by
  obtain ⟨current,currentParsed,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨history,priorParsed,same⟩ := Option.map_eq_some_iff.mp parsed
  subst view
  have before := readHistory_sound current.before.reverse history priorParsed
  have same := congrArg List.reverse before
  simp only [List.reverse_reverse] at same
  cases current
  simp only at same currentParsed ⊢
  rw [same] at currentParsed
  exact currentParsed

theorem parse_native (view : View) (profile : NativeRootMessage.Digest)
    (valid : ∀ frame ∈ (ScalarChallengeInputView.View.mk view.history.frames view.packet).frames, TranscriptFrame.Valid frame)
    (lengths : ∀ pair ∈ view.history.rounds, pair.2.length = 80) :
    parse ((ScalarChallengeInputView.View.mk view.history.frames view.packet).phase profile).pending.input = some view := by
  rw [parse,ScalarChallengeInputView.parse_native _ profile valid,Option.bind_some,readHistory_native view.history lengths,Option.map_some]

end FormalProof4FHE.HasteBoots.ScalarTranscriptPrefix
