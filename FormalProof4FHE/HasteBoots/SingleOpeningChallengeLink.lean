module
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldInputView
public import FormalProof4FHE.HasteBoots.SingleOpeningColumnInputView
@[expose] public section

/-! Recover the field prefix and raw receipt quote behind a parsed column
nonce. Exact placement and receipt length are checked. This links byte inputs;
it does not assert that the quoted receipt is the true hash of consumed bytes. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningChallengeLink
open InputIndexedOracle (Input)
open TranscriptFrame (Frame encodeMany)
open SingleOpeningColumnInputView (responseFrame)

def receiptFrame (payload : Input) : Frame := ⟨5,NativeGoldPcsPrelude.randomLabel,payload⟩

structure View where
  column : SingleOpeningColumnInputView.View
  field : SingleOpeningFieldInputView.View
  fieldFrames : List Frame
  receipt : Input

def readParts (column : SingleOpeningColumnInputView.View) (response receipt : Frame) (rest : List Frame) : Option View :=
  if response = responseFrame column.opening ∧ receipt = receiptFrame receipt.message ∧ receipt.message.length = 80 then
    (SingleOpeningFieldInputView.parse (encodeMany rest.reverse)).map (fun field => ⟨column,field,rest.reverse,receipt.message⟩)
  else none

def readColumn (column : SingleOpeningColumnInputView.View) : Option View :=
  match column.index.before.reverse with
  | response :: receipt :: rest => readParts column response receipt rest
  | _ => none

def parse (input : Input) : Option View := (SingleOpeningColumnInputView.parse input).bind readColumn

theorem readParts_sound (column : SingleOpeningColumnInputView.View) (response receipt : Frame) (rest : List Frame)
    (view : View) (parsed : readParts column response receipt rest = some view) :
    view.column = column ∧ view.fieldFrames = rest.reverse ∧ view.receipt.length = 80 ∧
      SingleOpeningFieldInputView.parse (encodeMany view.fieldFrames) = some view.field ∧
      response = responseFrame view.column.opening ∧ receipt = receiptFrame view.receipt := by
  unfold readParts at parsed
  split at parsed
  next shape =>
    obtain ⟨field,read,equal⟩ := Option.map_eq_some_iff.mp parsed
    subst view
    exact ⟨rfl,rfl,shape.2.2,read,shape.1,shape.2.1⟩
  next => contradiction

theorem readColumn_sound (column : SingleOpeningColumnInputView.View) (view : View)
    (parsed : readColumn column = some view) :
    view.column = column ∧ view.receipt.length = 80 ∧
      SingleOpeningFieldInputView.parse (encodeMany view.fieldFrames) = some view.field ∧
      column.index.before = view.fieldFrames ++ [receiptFrame view.receipt,responseFrame view.column.opening] := by
  unfold readColumn at parsed
  split at parsed
  next response receipt rest reversed =>
    obtain ⟨same,frames,length,read,responseEq,receiptEq⟩ := readParts_sound column response receipt rest view parsed
    refine ⟨same,length,read,?_⟩
    have equal := congrArg List.reverse reversed
    simpa only [List.reverse_reverse,List.reverse_cons,← frames,responseEq,receiptEq,List.append_assoc,List.cons_append,List.nil_append] using equal
  next => contradiction

/-- The same accepted complete nonce supplies its original raw single-opening binding, field
phase input, and exact80-byte receipt quote. Receipt validity is not assumed. -/
theorem parse_sound (input : Input) (view : View) (parsed : parse input = some view) (profile : NativeRootMessage.Digest) :
    SingleOpeningColumnInputView.parse input = some view.column ∧ view.receipt.length = 80 ∧
      (view.field.phase profile).pending.input = encodeMany view.fieldFrames ∧
      view.column.index.before = view.fieldFrames ++ [receiptFrame view.receipt,responseFrame view.column.opening] ∧
      0 < view.field.count.val := by
  obtain ⟨column,read,parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨same,length,fieldRead,frames⟩ := readColumn_sound column view parsed
  have field := SingleOpeningFieldInputView.parse_sound _ view.field fieldRead profile
  exact ⟨by rw [same]; exact read,length,field.1,by simpa only [same] using frames,field.2.1⟩

theorem readColumn_native (field : SingleOpeningFieldInputView.View) (opening : NativeGoldPcsOpening.Opening)
    (label : Input) (domain count : NativeUsizeMessage.Usize) (payload : Input) (length : payload.length = 80)
    (positive : 0 < field.count.val) (framed : ∀ frame ∈ field.frames, TranscriptFrame.Valid frame) :
    readColumn ⟨⟨field.frames++[receiptFrame payload,responseFrame opening],label,domain,count⟩,opening⟩ =
      some ⟨⟨⟨field.frames++[receiptFrame payload,responseFrame opening],label,domain,count⟩,opening⟩,field,field.frames,payload⟩ := by
  have decoded : SingleOpeningFieldInputView.parse (encodeMany field.frames) = some field := by
    rw [← SingleOpeningFieldInputView.phase_input field (fun _ => 0)]
    exact SingleOpeningFieldInputView.parse_native field _ positive framed
  simp only [readColumn,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    readParts,receiptFrame,and_self,length,ite_true,List.reverse_reverse,decoded,Option.map_some]
end FormalProof4FHE.HasteBoots.SingleOpeningChallengeLink
