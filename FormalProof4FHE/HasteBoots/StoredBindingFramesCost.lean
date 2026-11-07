module
public import FormalProof4FHE.HasteBoots.StoredCanonicalBindingCost
public import FormalProof4FHE.HasteBoots.ParentSeedRequestCost
import all Init.Data.String.Defs
@[expose] public section

/-! Measured canonical-binding frames from complete raw inputs. Full stored
bindings retain the original configuration, helper and ordered sources. Helper
and binding-source projections equal the original structural views. Inherited
metadata replay, first-owner selection and physical/native refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.StoredBindingFramesCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open StoredCanonicalBindingCost (Stored view)
open SolverOperationCost (Run)

def label : Input := NativeCanonicalLookupWire.label

def bindingView (frame : Frame) : Option NativeCanonicalLookupWire.Binding :=
  if frame.kind = 1 ∧ frame.label = label then NativeExactCodec.read NativeRootInputView.bindingCodec frame.message else none

def frameBinding (frame : Frame) : Run (Option Stored) :=
  if frame.kind = 1 then
    let named := BytePrefixMatchCost.equal label frame.label
    if named.value then
      let binding := StoredCanonicalBindingCost.decode frame.message
      ⟨binding.value,named.cost+binding.cost+5⟩
    else ⟨none,named.cost+3⟩
  else ⟨none,2⟩

theorem frameBinding_value (frame : Frame) : (frameBinding frame).value.map view = bindingView frame := by
  by_cases kind : frame.kind = 1 <;> by_cases named : frame.label = label <;>
    simp only [frameBinding,bindingView,BytePrefixMatchCost.equal_value,
      Eq.comm (a := label) (b := frame.label),kind,named,and_true,and_false,ite_true,ite_false,
      decide_true,decide_false,Bool.false_eq_true,StoredCanonicalBindingCost.decode_value,Option.map_none]

theorem helper_value (frame : Frame) :
    (frameBinding frame).value.map (fun binding => binding.helper.get) = ExecutableParentInputView.frameHelper frame := by
  have reference := congrArg (Option.map NativeCanonicalLookupWire.Binding.helper) (frameBinding_value frame)
  change _ = if frame.kind = 1 ∧ frame.label = label then
    (NativeExactCodec.read NativeRootInputView.bindingCodec frame.message).map NativeCanonicalLookupWire.Binding.helper else none
  by_cases accepted : frame.kind = 1 ∧ frame.label = label <;>
    simpa only [bindingView,accepted,and_true,ite_true,ite_false,Option.map_map,Function.comp_def,
      view,Option.map_none] using reference

theorem binding_sources_value (frame : Frame) (named : frame.label = label) :
    (frameBinding frame).value.map (fun binding => (StoredSourceVectorReadCost.view binding.sources).val) =
      NativeRootInputView.frameSources frame := by
  have different : NativeCanonicalLookupWire.label ≠ NativeCanonicalLookupWire.registryLabel := by
    unfold NativeCanonicalLookupWire.label NativeCanonicalLookupWire.registryLabel NativeTranscript.utf8
    decide +kernel
  have notRegistry : frame.label ≠ NativeCanonicalLookupWire.registryLabel := by rw [named]; exact different
  have reference := congrArg (Option.map (fun binding : NativeCanonicalLookupWire.Binding => binding.sources.val))
    (frameBinding_value frame)
  by_cases kind : frame.kind = 1 <;>
    simpa only [bindingView,kind,named,and_true,and_self,ite_true,ite_false,Option.map_map,
      Function.comp_def,view,NativeRootInputView.frameSources,notRegistry,label,different,Option.map_none] using reference

theorem frameBinding_cost (frame : Frame) :
    (frameBinding frame).cost ≤ 302*frame.message.length+1764*(frame.message.length/128+1)+6*label.length+1114 := by
  have named := BytePrefixMatchCost.equal_cost label frame.label
  have size := Nat.min_le_left label.length frame.label.length
  have decoded := StoredCanonicalBindingCost.decode_cost frame.message
  simp only [frameBinding]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

def collect : List Frame → Run (List Stored)
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := frameBinding head
    let rest := collect tail
    ⟨match first.value with | none => rest.value | some binding => binding::rest.value,
      first.cost+rest.cost+3⟩

theorem collect_value (frames : List Frame) :
    (collect frames).value.map view = frames.filterMap bindingView := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    have reference := frameBinding_value head
    cases parsed : (frameBinding head).value with
    | none =>
      rw [parsed,Option.map_none] at reference
      simp only [collect,parsed,ih,List.filterMap_cons,← reference]
    | some binding =>
      rw [parsed,Option.map_some] at reference
      simp only [collect,parsed,List.map_cons,ih,List.filterMap_cons,← reference]

def messageBytes : List Frame → ℕ
  | [] => 0
  | head::tail => head.message.length+messageBytes tail

theorem collect_cost (frames : List Frame) :
    (collect frames).cost ≤ 2066*messageBytes frames+(6*label.length+2881)*frames.length+1 := by
  induction frames with
  | nil => simp [collect,messageBytes]
  | cons head tail ih =>
    have first := frameBinding_cost head
    have size := Nat.div_le_self head.message.length 128
    simp only [collect,messageBytes,List.length_cons]
    nlinarith

theorem messageBytes_le_encoded (frames : List Frame) :
    messageBytes frames ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => rfl
  | cons head tail ih => simp only [messageBytes,TranscriptFrame.encodeMany,List.length_append,TranscriptFrame.encode_length]; omega

def fromInput (input : Input) : Run (List Stored) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨[],frames.cost+2⟩
  | some values =>
    let bindings := collect values
    ⟨bindings.value,frames.cost+bindings.cost+3⟩

theorem fromInput_value (input : Input) :
    (fromInput input).value.map view = ((TranscriptFrame.decodeAll input).getD []).filterMap bindingView := by
  simp only [fromInput,TranscriptFrameStreamCost.decodeAll_value]
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
end FormalProof4FHE.HasteBoots.StoredBindingFramesCost
