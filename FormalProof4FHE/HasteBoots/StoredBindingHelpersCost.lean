module
public import FormalProof4FHE.HasteBoots.StoredBindingFramesCost
public import FormalProof4FHE.HasteBoots.StoredMetadataCost
public import FormalProof4FHE.HasteBoots.NativeRootMentionSize
@[expose] public section

/-! Stored helpers from complete original canonical-binding frames. Full bindings
are decoded before their helper bytes can enter inherited metadata. -/
namespace FormalProof4FHE.HasteBoots.StoredBindingHelpersCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)
open StoredMetadataCost (Root)
open StoredBindingFramesCost (frameBinding label messageBytes messageBytes_le_encoded)

def collect : List Frame → Run (List Root)
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := frameBinding head
    let rest := collect tail
    ⟨match first.value with | none => rest.value | some binding => binding.helper::rest.value,
      first.cost+rest.cost+3⟩

theorem collect_value (frames : List Frame) :
    (collect frames).value.map Vector.get = frames.filterMap ExecutableParentInputView.frameHelper := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    have reference := StoredBindingFramesCost.helper_value head
    cases parsed : (frameBinding head).value with
    | none =>
      rw [parsed,Option.map_none] at reference
      simp only [collect,parsed,ih,List.filterMap_cons,← reference]
    | some binding =>
      rw [parsed,Option.map_some] at reference
      simp only [collect,parsed,List.map_cons,ih,List.filterMap_cons,← reference]

theorem collect_cost (frames : List Frame) :
    (collect frames).cost ≤ 2066*messageBytes frames+(6*label.length+2881)*frames.length+1 := by
  induction frames with
  | nil => simp [collect,messageBytes]
  | cons head tail ih =>
    have first := StoredBindingFramesCost.frameBinding_cost head
    have size := Nat.div_le_self head.message.length 128
    simp only [collect,messageBytes,List.length_cons]
    nlinarith

def fromInput (input : Input) : Run (List Root) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨[],frames.cost+2⟩
  | some values =>
    let bindings := collect values
    ⟨bindings.value,frames.cost+bindings.cost+3⟩

theorem fromInput_value (input : Input) :
    (fromInput input).value.map Vector.get = ExecutableParentLedger.helpers input := by
  simp only [fromInput,TranscriptFrameStreamCost.decodeAll_value,ExecutableParentLedger.helpers,ExecutableParentLedger.frames]
  cases parsed : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => simp only [Option.getD_some,collect_value]

theorem fromInput_cost (input : Input) :
    (fromInput input).cost ≤ (4971+6*label.length)*input.length+5 := by
  have decoded := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [fromInput]
  split
  · dsimp only; nlinarith
  · rename_i frames parsed
    have encoded := (TranscriptFrameStreamCost.decodeAll_sound input frames parsed).2
    have count := ParentSeedRequestCost.frameCount_le_encoded frames
    have messages := messageBytes_le_encoded frames
    rw [← encoded] at count messages
    have bindings := collect_cost frames
    have visits := Nat.mul_le_mul_left (6*label.length+2881) count
    dsimp only
    nlinarith
theorem fromInput_size (input : Input) : (fromInput input).value.length ≤ input.length := by
  have same := congrArg List.length (fromInput_value input)
  rw [List.length_map,ExecutableParentLedger.helpers_eq] at same
  rw [same]
  exact NativeRootMentionSize.helpers_size input
end FormalProof4FHE.HasteBoots.StoredBindingHelpersCost
