module
public import FormalProof4FHE.HasteBoots.GoldBatchFieldCountCost
public import FormalProof4FHE.HasteBoots.StoredBatchFramesCost
@[expose] public section

/-! Complete measured parsing of the original Gold batch field input. Only the
immediate terminal batch/typed/prime/field suffix is recognized. All query/value
bytes, original preceding frames and raw stored context/root bytes are retained.
Trusted parameter/context production and physical/native refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldBatchFieldInputCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)
open NativeUsizeMessage (Usize)

structure Stored where
  before : List Frame
  data : StoredBatchMessageCost.Stored
  count : Usize

def view (field : Stored) : NativeGoldBatchFieldInputView.View :=
  ⟨field.before,StoredBatchMessageCost.view field.data,field.count⟩

def readParts (field prime typed batch : Frame) (rest : List Frame) : Run (Option Stored) :=
  let first := FrameMatchCost.equal prime NativeGoldBatchFieldInputView.primeFrame
  if first.value then
    let second := FrameMatchCost.equal typed NativeGoldBatchFieldInputView.typedFrame
    if second.value then
      let count := GoldBatchFieldCountCost.read field
      match count.value with
      | none => ⟨none,first.cost+second.cost+count.cost+5⟩
      | some size =>
        let data := StoredBatchFramesCost.frameBatch batch
        match data.value with
        | none => ⟨none,first.cost+second.cost+count.cost+data.cost+7⟩
        | some binding =>
          let before := ParentSeedRequestCost.reverseAux rest []
          ⟨some ⟨before.value,binding,size⟩,first.cost+second.cost+count.cost+data.cost+before.cost+9⟩
    else ⟨none,first.cost+second.cost+4⟩
  else ⟨none,first.cost+2⟩

theorem batch_value (frame : Frame) :
    (StoredBatchFramesCost.frameBatch frame).value.map StoredBatchMessageCost.view =
      NativeGoldBatchFieldInputView.readBatch frame := StoredBatchFramesCost.frameBatch_value frame

theorem readParts_value (field prime typed batch : Frame) (rest : List Frame) :
    (readParts field prime typed batch rest).value.map view =
      NativeGoldBatchFieldInputView.readParts field prime typed batch rest := by
  simp only [readParts,FrameMatchCost.equal_value,NativeGoldBatchFieldInputView.readParts,
    ← GoldBatchFieldCountCost.read_value,← batch_value,Option.bind_eq_bind]
  by_cases primeEq : prime = NativeGoldBatchFieldInputView.primeFrame <;>
    by_cases typedEq : typed = NativeGoldBatchFieldInputView.typedFrame
  all_goals
    simp only [primeEq,typedEq,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,
      and_true,and_false,Option.map_none]
  cases count : (GoldBatchFieldCountCost.read field).value with
  | none => rfl
  | some size =>
    simp only [Option.bind_some]
    cases data : (StoredBatchFramesCost.frameBatch batch).value with
    | none => rfl
    | some binding =>
      simp only [Option.map_some,Option.bind_some,ParentSeedRequestCost.reverseAux_value,List.append_nil,view]
      rfl

def labelBytes : ℕ := NativeGoldBatchFieldInputView.primeFrame.label.length+
  NativeGoldBatchFieldInputView.primeFrame.message.length+
  NativeGoldBatchFieldInputView.typedFrame.label.length+
  NativeGoldBatchFieldInputView.typedFrame.message.length+
  NativeGoldBatchPrelude.randomLabel.length+StoredBatchFramesCost.label.length

theorem readParts_cost (field prime typed batch : Frame) (rest : List Frame) :
    (readParts field prime typed batch rest).cost ≤ 557*batch.message.length+3*field.message.length+
      3*rest.length+6*labelBytes+3400 := by
  have first := FrameMatchCost.equal_cost prime NativeGoldBatchFieldInputView.primeFrame
  have second := FrameMatchCost.equal_cost typed NativeGoldBatchFieldInputView.typedFrame
  have count := GoldBatchFieldCountCost.read_cost field
  have data := StoredBatchFramesCost.frameBatch_cost batch
  have reversed := ParentSeedRequestCost.reverseAux_cost rest []
  simp only [readParts,labelBytes]
  split
  · split
    · split
      · dsimp only; omega
      · split <;> dsimp only <;> omega
    · dsimp only; omega
  · dsimp only; omega

def readFrames : List Frame → Run (Option Stored)
  | field::prime::typed::batch::rest => readParts field prime typed batch rest
  | _ => ⟨none,1⟩

theorem readFrames_value (frames : List Frame) :
    (readFrames frames).value.map view = NativeGoldBatchFieldInputView.readFrames frames := by
  match frames with
  | field::prime::typed::batch::rest => exact readParts_value _ _ _ _ _
  | [] | [_] | [_,_] | [_,_,_] => rfl

def messageBytes (frames : List Frame) : ℕ := (frames.map (fun frame => frame.message.length)).sum

theorem messageBytes_le_encoded (frames : List Frame) : messageBytes frames ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => exact le_rfl
  | cons head tail ih =>
    simp only [messageBytes,List.map_cons,List.sum_cons,TranscriptFrame.encodeMany,
      List.length_append,TranscriptFrame.encode_length] at *
    omega

theorem messageBytes_reverse (frames : List Frame) : messageBytes frames.reverse = messageBytes frames := by
  simp only [messageBytes,List.map_reverse,List.sum_reverse]

theorem readFrames_cost (frames : List Frame) :
    (readFrames frames).cost ≤ 557*messageBytes frames+3*frames.length+6*labelBytes+3400 := by
  match frames with
  | field::prime::typed::batch::rest =>
    have parts := readParts_cost field prime typed batch rest
    simp only [readFrames,messageBytes,List.map_cons,List.sum_cons,List.length_cons]
    omega
  | [] | [_] | [_,_] | [_,_,_] => simp only [readFrames]; omega

def parse (input : Input) : Run (Option Stored) :=
  let decoded := TranscriptFrameStreamCost.decodeAll input
  match decoded.value with
  | none => ⟨none,decoded.cost+2⟩
  | some frames =>
    let reversed := ParentSeedRequestCost.reverseAux frames []
    let result := readFrames reversed.value
    ⟨result.value,decoded.cost+reversed.cost+result.cost+3⟩

theorem parse_value (input : Input) : (parse input).value.map view = NativeGoldBatchFieldInputView.parse input := by
  simp only [parse,TranscriptFrameStreamCost.decodeAll_value,NativeGoldBatchFieldInputView.parse]
  cases decoded : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => simp only [Option.bind_some,ParentSeedRequestCost.reverseAux_value,List.append_nil,readFrames_value]
theorem parse_cost (input : Input) : (parse input).cost ≤ 587*input.length+6*labelBytes+3410 := by
  have decoded := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [parse]
  split
  · dsimp only; omega
  · rename_i frames found
    have native : TranscriptFrame.decodeAll input = some frames := by
      rw [← TranscriptFrameStreamCost.decodeAll_value]; exact found
    have encoded := (TranscriptFrame.decodeAll_sound input frames native).2
    have count := ParentSeedRequestCost.frameCount_le_encoded frames
    have messages := messageBytes_le_encoded frames
    rw [← encoded] at count messages
    have reversed := ParentSeedRequestCost.reverseAux_cost frames []
    have body := readFrames_cost (ParentSeedRequestCost.reverseAux frames []).value
    rw [ParentSeedRequestCost.reverseAux_value,List.append_nil,messageBytes_reverse,List.length_reverse] at body
    dsimp only
    simp only [ParentSeedRequestCost.reverseAux_value,List.append_nil]
    omega

theorem parse_sound (input : Input) (field : Stored) (found : (parse input).value = some field) :
    TranscriptFrame.encodeMany (view field).frames = input ∧ 0 < field.count.val := by
  have native := parse_value input
  rw [found,Option.map_some] at native
  have sound := NativeGoldBatchFieldInputView.parse_sound input (view field) native.symm (fun _ => 0)
  rw [NativeGoldBatchFieldInputView.phase_input] at sound
  exact ⟨sound.1,sound.2.1⟩
end FormalProof4FHE.HasteBoots.StoredGoldBatchFieldInputCost
