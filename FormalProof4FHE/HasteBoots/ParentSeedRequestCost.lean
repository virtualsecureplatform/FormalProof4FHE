module
public import FormalProof4FHE.HasteBoots.TranscriptFrameStreamCost
public import FormalProof4FHE.HasteBoots.ExecutableParentInputView
public import FormalProof4FHE.HasteBoots.BytePrefixMatchCost
@[expose] public section

/-! Measured recognition of the original terminal parent fork/request pair.
Whole-stream parsing, reverse traversal and exact byte comparisons are charged.
This preserves the structural parent recognizer; protocol ownership, source/helper
meaning, ledger replay and physical/native refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.ParentSeedRequestCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)

def reverseAux : List Frame → List Frame → Run (List Frame)
  | [],saved => ⟨saved,1⟩
  | head::tail,saved =>
    let rest := reverseAux tail (head::saved)
    ⟨rest.value,rest.cost+3⟩

theorem reverseAux_value (frames saved : List Frame) :
    (reverseAux frames saved).value = frames.reverse++saved := by
  induction frames generalizing saved with
  | nil => rfl
  | cons head tail ih => simp only [reverseAux,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem reverseAux_cost (frames saved : List Frame) :
    (reverseAux frames saved).cost = 3*frames.length+1 := by
  induction frames generalizing saved with
  | nil => rfl
  | cons head tail ih => simp only [reverseAux,ih,List.length_cons]; omega

def label : Input := NativeTranscript.utf8 "classical child seed"
def message : Input := TranscriptFrame.littleEndian 8 64

def request (req fork : Frame) : Run Bool :=
  if req.kind = 2 ∧ fork.kind = 6 then
    let named := BytePrefixMatchCost.equal label req.label
    if named.value then
      let sized := BytePrefixMatchCost.equal message req.message
      ⟨sized.value,named.cost+sized.cost+5⟩
    else ⟨false,named.cost+3⟩
  else ⟨false,3⟩

theorem request_value (req fork : Frame) : (request req fork).value =
    decide (req.kind = 2 ∧ req.label = label ∧ req.message = message ∧ fork.kind = 6) := by
  by_cases kind : req.kind = 2 <;> by_cases other : fork.kind = 6 <;>
    by_cases named : req.label = label <;> by_cases sized : req.message = message <;>
      simp only [request,BytePrefixMatchCost.equal_value,
        Eq.comm (a := label) (b := req.label),Eq.comm (a := message) (b := req.message),
        kind,other,named,sized,and_true,and_false,
        decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]

theorem request_cost (req fork : Frame) :
    (request req fork).cost ≤ 6*label.length+6*message.length+23 := by
  have named := BytePrefixMatchCost.equal_cost label req.label
  have sized := BytePrefixMatchCost.equal_cost message req.message
  have namedSize := Nat.min_le_left label.length req.label.length
  have sizedSize := Nat.min_le_left message.length req.message.length
  simp only [request]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

def seedFrames (frames : List Frame) : Run Bool :=
  let reversed := reverseAux frames []
  match reversed.value with
  | req::fork::_ =>
    let result := request req fork
    ⟨result.value,reversed.cost+result.cost+3⟩
  | _ => ⟨false,reversed.cost+2⟩

theorem seedFrames_value (frames : List Frame) :
    (seedFrames frames).value = ExecutableParentInputView.seedFrames frames := by
  simp only [seedFrames,reverseAux_value,List.append_nil,ExecutableParentInputView.seedFrames]
  cases reversed : frames.reverse with
  | nil => rfl
  | cons req rest =>
    cases rest with
    | nil => rfl
    | cons fork tail => exact request_value req fork

theorem seedFrames_cost (frames : List Frame) :
    (seedFrames frames).cost ≤ 3*frames.length+6*label.length+6*message.length+27 := by
  have reversed := reverseAux_cost frames []
  simp only [seedFrames]
  split
  · rename_i req fork rest found
    have checked := request_cost req fork
    dsimp only; omega
  · dsimp only; omega

theorem frameCount_le_encoded (frames : List Frame) :
    frames.length ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    simp only [TranscriptFrame.encodeMany,List.length_cons,List.length_append,TranscriptFrame.encode_length]
    omega

def parse (input : Input) : Run (Option (List Frame)) :=
  let decoded := TranscriptFrameStreamCost.decodeAll input
  match decoded.value with
  | none => ⟨none,decoded.cost+2⟩
  | some frames =>
    let checked := seedFrames frames
    ⟨if checked.value then some frames else none,decoded.cost+checked.cost+4⟩

theorem parse_value (input : Input) :
    (parse input).value = ExecutableParentInputView.parseParent input := by
  simp only [parse,TranscriptFrameStreamCost.decodeAll_value,ExecutableParentInputView.parseParent]
  cases decoded : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => simp only [Option.bind_some,seedFrames_value]

theorem parse_cost (input : Input) :
    (parse input).cost ≤ 27*input.length+6*label.length+6*message.length+32 := by
  have decoded := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [parse]
  split
  · dsimp only; omega
  · rename_i frames found
    have encoding := (TranscriptFrameStreamCost.decodeAll_sound input frames found).2
    have count := frameCount_le_encoded frames
    rw [← encoding] at count
    have checked := seedFrames_cost frames
    dsimp only; omega

theorem parse_sound (input : Input) (frames : List Frame)
    (found : (parse input).value = some frames) :
    (∀ frame ∈ frames, TranscriptFrame.Valid frame) ∧
      input = TranscriptFrame.encodeMany frames ∧ NativeParentInputView.isSeedFrames frames := by
  simp only [parse] at found
  split at found
  · contradiction
  · rename_i decoded parsed
    split at found
    · rename_i accepted
      have same := Option.some.inj found
      subst frames
      have sound := TranscriptFrameStreamCost.decodeAll_sound input decoded parsed
      rw [seedFrames_value] at accepted
      exact ⟨sound.1,sound.2,(ExecutableParentInputView.seedFrames_iff decoded).mp accepted⟩
    · contradiction
end FormalProof4FHE.HasteBoots.ParentSeedRequestCost
