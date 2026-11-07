module
public import FormalProof4FHE.HasteBoots.StoredDigestVectorCost
public import FormalProof4FHE.HasteBoots.ParentSeedRequestCost
public import FormalProof4FHE.HasteBoots.ExecutableParentLedger
@[expose] public section

/-! Measured helper-root mentions from complete framed inputs. Every original
root, order and duplicate is retained in stored form. Semantic recognition equals
the original parent-ledger roots view. Inherited source/helper metadata replay,
snapshot selection and physical/compiler/native refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.StoredHelperRootsCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)
open StoredDigestVectorReadCost (Root Roots view)

def label : Input := NativeLookupEquality.rootsLabel

def frameRoots (frame : Frame) : Run (Option Roots) :=
  if frame.kind = 1 then
    let named := BytePrefixMatchCost.equal label frame.label
    if named.value then
      let roots := StoredDigestVectorCost.decode frame.message
      ⟨roots.value,named.cost+roots.cost+5⟩
    else ⟨none,named.cost+3⟩
  else ⟨none,2⟩

theorem frameRoots_value (frame : Frame) :
    (frameRoots frame).value.map (fun roots => (view roots).val) = ExecutableParentInputView.helperRoots frame := by
  by_cases kind : frame.kind = 1 <;> by_cases named : frame.label = label
  all_goals
    dsimp only [label] at named
    simp only [frameRoots,ExecutableParentInputView.helperRoots,label,kind,named,
      BytePrefixMatchCost.equal_value,Eq.comm (a := NativeLookupEquality.rootsLabel) (b := frame.label),
      and_true,and_false,ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true,
      ← StoredDigestVectorCost.decode_value,Option.map_map,Function.comp_def,Option.map_none]

theorem frameRoots_cost (frame : Frame) :
    (frameRoots frame).cost ≤ 787*(frame.message.length/64+1)+6*frame.message.length+6*label.length+15 := by
  have named := BytePrefixMatchCost.equal_cost label frame.label
  have size := Nat.min_le_left label.length frame.label.length
  have decoded := StoredDigestVectorCost.decode_cost frame.message
  simp only [frameRoots]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

theorem frameRoots_size (frame : Frame) (roots : Roots)
    (found : (frameRoots frame).value = some roots) : roots.val.length ≤ frame.message.length/64 := by
  simp only [frameRoots] at found
  split at found
  · split at found
    · exact StoredDigestVectorCost.decode_size frame.message roots found
    · contradiction
  · contradiction

def appendRoots : List Root → List Root → Run (List Root)
  | [],last => ⟨last,1⟩
  | head::tail,last =>
    let rest := appendRoots tail last
    ⟨head::rest.value,rest.cost+3⟩

theorem appendRoots_value (first last : List Root) : (appendRoots first last).value = first++last := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [appendRoots,ih,List.cons_append]

theorem appendRoots_cost (first last : List Root) : (appendRoots first last).cost = 3*first.length+1 := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [appendRoots,ih,List.length_cons]; omega

def collect : List Frame → Run (List Root)
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := frameRoots head
    let rest := collect tail
    match first.value with
    | none => ⟨rest.value,first.cost+rest.cost+3⟩
    | some roots =>
      let joined := appendRoots roots.val rest.value
      ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem collect_value (frames : List Frame) :
    (collect frames).value.map Vector.get = frames.flatMap (fun frame => (ExecutableParentInputView.helperRoots frame).getD []) := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    have reference := frameRoots_value head
    cases parsed : (frameRoots head).value with
    | none =>
      rw [parsed,Option.map_none] at reference
      simp only [collect,parsed,ih,List.flatMap_cons,← reference,Option.getD_none,List.nil_append]
    | some roots =>
      rw [parsed,Option.map_some] at reference
      simp only [collect,parsed,appendRoots_value,List.map_append,ih,List.flatMap_cons,
        ← reference,Option.getD_some,view]

def messageBytes : List Frame → ℕ
  | [] => 0
  | head::tail => head.message.length+messageBytes tail

theorem collect_cost (frames : List Frame) :
    (collect frames).cost ≤ 800*messageBytes frames+(6*label.length+820)*frames.length+1 := by
  induction frames with
  | nil => simp [collect,messageBytes]
  | cons head tail ih =>
    have first := frameRoots_cost head
    have size := Nat.div_le_self head.message.length 64
    simp only [collect,messageBytes,List.length_cons]
    split
    · dsimp only; nlinarith
    · rename_i roots parsed
      have count := frameRoots_size head roots parsed
      simp only [appendRoots_cost]
      nlinarith

theorem messageBytes_le_encoded (frames : List Frame) :
    messageBytes frames ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    simp only [messageBytes,TranscriptFrame.encodeMany,List.length_append,TranscriptFrame.encode_length]
    omega

def fromInput (input : Input) : Run (List Root) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨[],frames.cost+2⟩
  | some values =>
    let roots := collect values
    ⟨roots.value,frames.cost+roots.cost+3⟩

theorem fromInput_value (input : Input) :
    (fromInput input).value.map Vector.get = ExecutableParentLedger.roots input := by
  simp only [fromInput,TranscriptFrameStreamCost.decodeAll_value,ExecutableParentLedger.roots,ExecutableParentLedger.frames]
  cases parsed : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => simp only [Option.getD_some,collect_value]

theorem fromInput_cost (input : Input) :
    (fromInput input).cost ≤ (1644+6*label.length)*input.length+5 := by
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
    have visits := Nat.mul_le_mul_left (6*label.length+820) count
    dsimp only
    nlinarith
end FormalProof4FHE.HasteBoots.StoredHelperRootsCost
