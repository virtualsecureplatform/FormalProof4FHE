module
public import FormalProof4FHE.HasteBoots.StoredBatchMessageCost
public import FormalProof4FHE.HasteBoots.ParentSeedRequestCost
import all Init.Data.String.Defs
@[expose] public section

/-! Original batch-frame sources with complete measured message decoding.
No query or value suffix is ignored when recognizing a context/root mention. -/
namespace FormalProof4FHE.HasteBoots.StoredBatchFramesCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open StoredBatchMessageCost (Stored view)
open SolverOperationCost (Run)

def label : Input := NativeTranscript.utf8 "mw batched row-code v1"

def batchView (frame : Frame) : Option NativeGoldBatchMessage.Data :=
  if frame.kind = 1 ∧ frame.label = label then NativeExactCodec.read NativeGoldBatchMessage.codec frame.message else none

def frameBatch (frame : Frame) : Run (Option Stored) :=
  if frame.kind = 1 then
    let named := BytePrefixMatchCost.equal label frame.label
    if named.value then
      let batch := StoredBatchMessageCost.decode frame.message
      ⟨batch.value,named.cost+batch.cost+5⟩
    else ⟨none,named.cost+3⟩
  else ⟨none,2⟩

theorem frameBatch_value (frame : Frame) : (frameBatch frame).value.map view = batchView frame := by
  by_cases kind : frame.kind = 1 <;> by_cases named : frame.label = label <;>
    simp only [frameBatch,batchView,BytePrefixMatchCost.equal_value,
      Eq.comm (a := label) (b := frame.label),kind,named,and_true,and_false,ite_true,ite_false,
      decide_true,decide_false,Bool.false_eq_true,StoredBatchMessageCost.decode_value,Option.map_none]

theorem batch_sources_value (frame : Frame) (named : frame.label = label) :
    (frameBatch frame).value.map (fun batch => [StoredSourceVectorReadCost.sourceView batch.source]) =
      NativeRootInputView.frameSources frame := by
  have notRegistry : label ≠ NativeCanonicalLookupWire.registryLabel := by
    unfold label NativeCanonicalLookupWire.registryLabel NativeTranscript.utf8
    decide +kernel
  have notBinding : label ≠ NativeCanonicalLookupWire.label := by
    unfold label NativeCanonicalLookupWire.label NativeTranscript.utf8
    decide +kernel
  dsimp only [label] at notRegistry notBinding
  have reference := congrArg (Option.map (fun batch : NativeGoldBatchMessage.Data => [(batch.context,batch.root)]))
    (frameBatch_value frame)
  by_cases kind : frame.kind = 1 <;>
    simpa only [batchView,kind,named,and_true,and_self,ite_true,ite_false,Option.map_map,
      Function.comp_def,view,NativeRootInputView.frameSources,notRegistry,notBinding,
      StoredSourceVectorReadCost.sourceView,label,Option.map_none] using reference

theorem frameBatch_cost (frame : Frame) :
    (frameBatch frame).cost ≤ 557*frame.message.length+6*label.length+2414 := by
  have named := BytePrefixMatchCost.equal_cost label frame.label
  have size := Nat.min_le_left label.length frame.label.length
  have decoded := StoredBatchMessageCost.decode_cost frame.message
  simp only [frameBatch]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega
end FormalProof4FHE.HasteBoots.StoredBatchFramesCost
