module
public import FormalProof4FHE.HasteBoots.StoredSourceVectorCost
public import FormalProof4FHE.HasteBoots.ParentSeedRequestCost
public import FormalProof4FHE.HasteBoots.NativeRootInputView
@[expose] public section

/-! Measured registry-source mentions from complete framed inputs. Every original
context/root pair, order and duplicate is retained in stored form. Semantic recognition equals
the registry branch of the original source-mention view. Inherited source/helper metadata replay,
snapshot selection and physical/compiler/native refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredRegistrySourcesCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source Sources sourceView view)

def label : Input := NativeCanonicalLookupWire.registryLabel

/-- The registry branch of the original source-mention view. Other formats are
intentionally left to their own measured decoders. -/
def registryView (frame : Frame) : Option (List NativeCanonicalLookupWire.Source) :=
  if frame.label = label then NativeRootInputView.frameSources frame else none

theorem registryView_eq_decode (frame : Frame) : registryView frame =
    if frame.kind = 1 ∧ frame.label = label then
      (NativeExactCodec.read NativeCanonicalLookupWire.sourcesCodec frame.message).map Subtype.val
    else none := by
  by_cases kind : frame.kind = 1 <;> by_cases named : frame.label = label
  all_goals
    dsimp only [label] at named
    simp only [registryView,NativeRootInputView.frameSources,label,kind,named,
      and_true,and_false,ite_true,ite_false]

def frameSources (frame : Frame) : Run (Option Sources) :=
  if frame.kind = 1 then
    let named := BytePrefixMatchCost.equal label frame.label
    if named.value then
      let roots := StoredSourceVectorCost.decode frame.message
      ⟨roots.value,named.cost+roots.cost+5⟩
    else ⟨none,named.cost+3⟩
  else ⟨none,2⟩

theorem frameSources_value (frame : Frame) :
    (frameSources frame).value.map (fun sources => (view sources).val) = registryView frame := by
  by_cases kind : frame.kind = 1 <;> by_cases named : frame.label = label
  all_goals
    dsimp only [label] at named
    simp only [frameSources,registryView_eq_decode,label,kind,named,
      BytePrefixMatchCost.equal_value,Eq.comm (a := NativeCanonicalLookupWire.registryLabel) (b := frame.label),
      and_true,and_false,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true,
      ← StoredSourceVectorCost.decode_value,Option.map_map,Function.comp_def,Option.map_none]

theorem frameSources_cost (frame : Frame) :
    (frameSources frame).cost ≤ 1764*(frame.message.length/128+1)+6*frame.message.length+6*label.length+15 := by
  have named := BytePrefixMatchCost.equal_cost label frame.label
  have size := Nat.min_le_left label.length frame.label.length
  have decoded := StoredSourceVectorCost.decode_cost frame.message
  simp only [frameSources]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

theorem frameSources_size (frame : Frame) (roots : Sources)
    (found : (frameSources frame).value = some roots) : roots.val.length ≤ frame.message.length/128 := by
  simp only [frameSources] at found
  split at found
  · split at found
    · exact StoredSourceVectorCost.decode_size frame.message roots found
    · contradiction
  · contradiction

def appendSources : List Source → List Source → Run (List Source)
  | [],last => ⟨last,1⟩
  | head::tail,last =>
    let rest := appendSources tail last
    ⟨head::rest.value,rest.cost+3⟩

theorem appendSources_value (first last : List Source) : (appendSources first last).value = first++last := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [appendSources,ih,List.cons_append]

theorem appendSources_cost (first last : List Source) : (appendSources first last).cost = 3*first.length+1 := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [appendSources,ih,List.length_cons]; omega

def collect : List Frame → Run (List Source)
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := frameSources head
    let rest := collect tail
    match first.value with
    | none => ⟨rest.value,first.cost+rest.cost+3⟩
    | some roots =>
      let joined := appendSources roots.val rest.value
      ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem collect_value (frames : List Frame) :
    (collect frames).value.map sourceView = frames.flatMap (fun frame => (registryView frame).getD []) := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    have reference := frameSources_value head
    cases parsed : (frameSources head).value with
    | none =>
      rw [parsed,Option.map_none] at reference
      simp only [collect,parsed,ih,List.flatMap_cons,← reference,Option.getD_none,List.nil_append]
    | some roots =>
      rw [parsed,Option.map_some] at reference
      simp only [collect,parsed,appendSources_value,List.map_append,ih,List.flatMap_cons,
        ← reference,Option.getD_some,view]

def messageBytes : List Frame → ℕ
  | [] => 0
  | head::tail => head.message.length+messageBytes tail

theorem collect_cost (frames : List Frame) :
    (collect frames).cost ≤ 1800*messageBytes frames+(6*label.length+1800)*frames.length+1 := by
  induction frames with
  | nil => simp [collect,messageBytes]
  | cons head tail ih =>
    have first := frameSources_cost head
    have size := Nat.div_le_self head.message.length 128
    simp only [collect,messageBytes,List.length_cons]
    split
    · dsimp only; nlinarith
    · rename_i roots parsed
      have count := frameSources_size head roots parsed
      simp only [appendSources_cost]
      nlinarith

theorem messageBytes_le_encoded (frames : List Frame) :
    messageBytes frames ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    simp only [messageBytes,TranscriptFrame.encodeMany,List.length_append,TranscriptFrame.encode_length]
    omega

def mentions (input : Input) : List NativeCanonicalLookupWire.Source :=
  ((TranscriptFrame.decodeAll input).getD []).flatMap (fun frame => (registryView frame).getD [])

def fromInput (input : Input) : Run (List Source) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨[],frames.cost+2⟩
  | some values =>
    let roots := collect values
    ⟨roots.value,frames.cost+roots.cost+3⟩

theorem fromInput_value (input : Input) :
    (fromInput input).value.map sourceView = mentions input := by
  simp only [fromInput,TranscriptFrameStreamCost.decodeAll_value,mentions]
  cases parsed : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => simp only [Option.getD_some,collect_value]

theorem fromInput_cost (input : Input) :
    (fromInput input).cost ≤ (3624+6*label.length)*input.length+5 := by
  have decoded := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [fromInput]
  split
  · dsimp only; nlinarith
  · rename_i frames parsed
    have encoded := (TranscriptFrameStreamCost.decodeAll_sound input frames parsed).2
    have count := ParentSeedRequestCost.frameCount_le_encoded frames
    have messages := messageBytes_le_encoded frames
    rw [← encoded] at count messages
    have roots := collect_cost frames
    have visits := Nat.mul_le_mul_left (6*label.length+1800) count
    dsimp only
    nlinarith

theorem frameSources_encode (sources : Sources) :
    (frameSources ⟨1,label,(StoredSourceVectorCost.encode sources).value⟩).value = some sources := by
  simp only [frameSources,BytePrefixMatchCost.equal_value,decide_true,ite_true,
    StoredSourceVectorCost.decode_encode]
end FormalProof4FHE.HasteBoots.StoredRegistrySourcesCost
