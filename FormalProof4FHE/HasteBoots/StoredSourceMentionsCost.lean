module
public import FormalProof4FHE.HasteBoots.StoredRegistrySourcesCost
public import FormalProof4FHE.HasteBoots.StoredBindingFramesCost
public import FormalProof4FHE.HasteBoots.StoredBatchFramesCost
public import FormalProof4FHE.HasteBoots.StoredSingleSourcesCost
public import FormalProof4FHE.HasteBoots.NativeRootMentionSize
public import FormalProof4FHE.HasteBoots.ExecutableParentLedger
@[expose] public section

/-! Closed original-format source recognition and ordered transcript mentions.
The stored output retains every alias and duplicate. This is a direct-input
projection; inherited metadata replay and first-owner selection remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredSourceMentionsCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)

def frameSources (frame : Frame) : Run (Option (List Source)) :=
  if frame.kind = 1 then
    let registry := BytePrefixMatchCost.equal StoredRegistrySourcesCost.label frame.label
    if registry.value then
      let decoded := StoredRegistrySourcesCost.frameSources frame
      ⟨decoded.value.map Subtype.val,registry.cost+decoded.cost+2⟩
    else
      let binding := BytePrefixMatchCost.equal StoredBindingFramesCost.label frame.label
      if binding.value then
        let decoded := StoredBindingFramesCost.frameBinding frame
        ⟨decoded.value.map (fun data => data.sources.val),registry.cost+binding.cost+decoded.cost+3⟩
      else
        let batch := BytePrefixMatchCost.equal StoredBatchFramesCost.label frame.label
        if batch.value then
          let decoded := StoredBatchFramesCost.frameBatch frame
          ⟨decoded.value.map (fun data => [data.source]),registry.cost+binding.cost+batch.cost+decoded.cost+3⟩
        else ⟨none,registry.cost+binding.cost+batch.cost+4⟩
  else ⟨none,2⟩

theorem frameSources_value (frame : Frame) :
    (frameSources frame).value.map (List.map sourceView) = NativeRootInputView.frameSources frame := by
  dsimp only [frameSources]
  split
  · rename_i kind
    split
    · rename_i named
      have registry : frame.label = StoredRegistrySourcesCost.label := by
        simpa only [BytePrefixMatchCost.equal_value,Eq.comm (a := StoredRegistrySourcesCost.label) (b := frame.label),decide_eq_true_eq] using named
      simpa only [Option.map_map,Function.comp_def,StoredSourceVectorReadCost.view,
        StoredRegistrySourcesCost.registryView,ite_eq_left registry] using StoredRegistrySourcesCost.frameSources_value frame
    · rename_i notNamed
      have registry : frame.label ≠ StoredRegistrySourcesCost.label := by
        simpa only [BytePrefixMatchCost.equal_value,Eq.comm (a := StoredRegistrySourcesCost.label) (b := frame.label),decide_eq_true_eq] using notNamed
      split
      · rename_i named
        have binding : frame.label = StoredBindingFramesCost.label := by
          simpa only [BytePrefixMatchCost.equal_value,Eq.comm (a := StoredBindingFramesCost.label) (b := frame.label),decide_eq_true_eq] using named
        simpa only [Option.map_map,Function.comp_def,StoredSourceVectorReadCost.view]
          using StoredBindingFramesCost.binding_sources_value frame binding
      · rename_i notNamed
        have binding : frame.label ≠ StoredBindingFramesCost.label := by
          simpa only [BytePrefixMatchCost.equal_value,Eq.comm (a := StoredBindingFramesCost.label) (b := frame.label),decide_eq_true_eq] using notNamed
        split
        · rename_i named
          have batch : frame.label = StoredBatchFramesCost.label := by
            simpa only [BytePrefixMatchCost.equal_value,Eq.comm (a := StoredBatchFramesCost.label) (b := frame.label),decide_eq_true_eq] using named
          simpa only [Option.map_map,Function.comp_def,List.map_cons,List.map_nil]
            using StoredBatchFramesCost.batch_sources_value frame batch
        · rename_i notNamed
          have batch : frame.label ≠ StoredBatchFramesCost.label := by
            simpa only [BytePrefixMatchCost.equal_value,Eq.comm (a := StoredBatchFramesCost.label) (b := frame.label),decide_eq_true_eq] using notNamed
          dsimp only [StoredRegistrySourcesCost.label] at registry
          dsimp only [StoredBindingFramesCost.label] at binding
          dsimp only [StoredBatchFramesCost.label] at batch
          simp only [Option.map_none,NativeRootInputView.frameSources,ite_eq_left kind,
            ite_eq_right registry,ite_eq_right binding,ite_eq_right batch]
  · rename_i kind
    simp only [Option.map_none,NativeRootInputView.frameSources,ite_eq_right kind]

def frameLabelBytes := StoredRegistrySourcesCost.label.length+
  StoredBindingFramesCost.label.length+StoredBatchFramesCost.label.length

theorem frameSources_cost (frame : Frame) :
    (frameSources frame).cost ≤ 2100*frame.message.length+12*frameLabelBytes+5000 := by
  have registry := BytePrefixMatchCost.equal_cost StoredRegistrySourcesCost.label frame.label
  have registrySize := Nat.min_le_left StoredRegistrySourcesCost.label.length frame.label.length
  have binding := BytePrefixMatchCost.equal_cost StoredBindingFramesCost.label frame.label
  have bindingSize := Nat.min_le_left StoredBindingFramesCost.label.length frame.label.length
  have batch := BytePrefixMatchCost.equal_cost StoredBatchFramesCost.label frame.label
  have batchSize := Nat.min_le_left StoredBatchFramesCost.label.length frame.label.length
  have registryDecode := StoredRegistrySourcesCost.frameSources_cost frame
  have bindingDecode := StoredBindingFramesCost.frameBinding_cost frame
  have batchDecode := StoredBatchFramesCost.frameBatch_cost frame
  have divided := Nat.div_le_self frame.message.length 128
  simp only [frameLabelBytes,frameSources]
  split
  · split
    · dsimp only; omega
    · split
      · dsimp only; omega
      · split <;> dsimp only <;> omega
  · dsimp only; omega

theorem frameSources_size (frame : Frame) :
    ((frameSources frame).value.getD []).length ≤ frame.message.length := by
  have native := frameSources_value frame
  have size := NativeRootMentionSize.frameSources_getD_size frame
  cases parsed : (frameSources frame).value with
  | none => exact Nat.zero_le _
  | some values =>
    rw [parsed,Option.map_some] at native
    rw [← native,Option.getD_some,List.length_map] at size
    exact size
def adjacent (head : Frame) (tail : List Frame) : Run (Option Source) :=
  match tail with
  | [] => ⟨none,1⟩
  | next::_ => StoredSingleSourcesCost.single head next

theorem adjacent_value (head : Frame) (tail : List Frame) :
    (adjacent head tail).value.map sourceView =
      match tail with | [] => none | next::_ => NativeRootInputView.single head next := by
  cases tail with
  | nil => rfl
  | cons next rest => exact StoredSingleSourcesCost.single_value head next

def singleLabelBytes := StoredSingleSourcesCost.contextLabel.length+StoredSingleSourcesCost.openingLabel.length

def collect : List Frame → Run (List Source)
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := frameSources head
    let next := adjacent head tail
    let rest := collect tail
    let attached := next.value.toList ++ rest.value
    let joined := StoredRegistrySourcesCost.appendSources (first.value.getD []) attached
    ⟨joined.value,first.cost+next.cost+rest.cost+joined.cost+8⟩

theorem collect_value (frames : List Frame) :
    (collect frames).value.map sourceView = NativeRootInputView.mentions frames := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    have first := frameSources_value head
    have next := adjacent_value head tail
    have firstList : ((frameSources head).value.getD []).map sourceView =
        (NativeRootInputView.frameSources head).getD [] := by
      cases parsed : (frameSources head).value with
      | none =>
        rw [parsed,Option.map_none] at first
        rw [← first]
        rfl
      | some values =>
        rw [parsed,Option.map_some] at first
        rw [← first]
        rfl
    have nextList : (adjacent head tail).value.toList.map sourceView =
        (match tail with | [] => [] | frame::_ => (NativeRootInputView.single head frame).toList) := by
      rw [← Option.toList_map,next]
      cases tail <;> rfl
    rw [collect.eq_def,NativeRootInputView.mentions.eq_def]
    simp only [StoredRegistrySourcesCost.appendSources_value,List.map_append,firstList,nextList,ih,
      List.append_assoc]
    cases tail <;> rfl

theorem collect_cost (frames : List Frame) :
    (collect frames).cost ≤ 2103*StoredSingleSourcesCost.messageBytes frames+
      419*StoredSingleSourcesCost.afterMessages frames+
      (12*frameLabelBytes+6*singleLabelBytes+6910)*frames.length+1 := by
  induction frames with
  | nil => simp [collect,StoredSingleSourcesCost.messageBytes,StoredSingleSourcesCost.afterMessages]
  | cons head tail ih =>
    have first := frameSources_cost head
    have size := frameSources_size head
    rw [collect.eq_def]
    simp only [StoredRegistrySourcesCost.appendSources_cost]
    cases tail with
    | nil =>
      simp only [adjacent,collect,StoredSingleSourcesCost.messageBytes,
        StoredSingleSourcesCost.afterMessages,List.length_cons,List.length_nil] at *
      nlinarith
    | cons next rest =>
      have second := StoredSingleSourcesCost.single_cost head next
      simp only [adjacent,StoredSingleSourcesCost.messageBytes,
        StoredSingleSourcesCost.afterMessages,List.length_cons,singleLabelBytes] at *
      nlinarith

def fromInput (input : Input) : Run (List Source) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨[],frames.cost+2⟩
  | some values =>
    let sources := collect values
    ⟨sources.value,frames.cost+sources.cost+3⟩

theorem fromInput_value (input : Input) :
    (fromInput input).value.map sourceView = (NativeRootInputView.raw input).getD [] := by
  simp only [fromInput,NativeRootInputView.raw,TranscriptFrameStreamCost.decodeAll_value]
  cases parsed : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => exact collect_value frames

theorem direct_value (input : Input) :
    (fromInput input).value.map sourceView = ExecutableParentLedger.direct input := fromInput_value input

theorem fromInput_size (input : Input) : (fromInput input).value.length ≤ input.length := by
  have same := congrArg List.length (direct_value input)
  rw [List.length_map,ExecutableParentLedger.direct_eq] at same
  rw [same]
  exact NativeRootMentionSize.direct_size input

theorem fromInput_cost (input : Input) :
    (fromInput input).cost ≤ (9456+12*frameLabelBytes+6*singleLabelBytes)*input.length+5 := by
  have decoded := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [fromInput]
  split
  · dsimp only; nlinarith
  · rename_i frames parsed
    have native : TranscriptFrame.decodeAll input = some frames := by
      rw [← TranscriptFrameStreamCost.decodeAll_value]; exact parsed
    have encoded := (TranscriptFrame.decodeAll_sound input frames native).2
    have messages := StoredSingleSourcesCost.messageBytes_le_encoded frames
    have after := StoredSingleSourcesCost.afterMessages_le_encoded frames
    have count := ParentSeedRequestCost.frameCount_le_encoded frames
    have sources := collect_cost frames
    rw [← encoded] at messages after count
    dsimp only
    nlinarith
end FormalProof4FHE.HasteBoots.StoredSourceMentionsCost
