module
public import FormalProof4FHE.HasteBoots.StoredSingleOpeningCost
public import FormalProof4FHE.HasteBoots.StoredChildSeedQuote
public import FormalProof4FHE.HasteBoots.StoredSourceVectorReadCost
public import FormalProof4FHE.HasteBoots.ParentSeedRequestCost
@[expose] public section

/-! Measured adjacent single-opening source mentions. Context and opening
messages are completely checked before retaining their stored context/root pair.
Every original adjacency and duplicate is preserved. This is the single-opening
component, not the complete multi-format source view or PCS acceptance. -/
namespace FormalProof4FHE.HasteBoots.StoredSingleSourcesCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open StoredSourceVectorReadCost (Source sourceView)
open SolverOperationCost (Run)

def contextLabel : Input := NativeTranscript.utf8 "mw brakedown row-code v2"
def openingLabel : Input := NativeTranscript.utf8 "mw commitment and query"

def single (context opening : Frame) : Run (Option Source) :=
  if context.kind = 1 ∧ opening.kind = 1 then
    let first := BytePrefixMatchCost.equal contextLabel context.label
    if first.value then
      let second := BytePrefixMatchCost.equal openingLabel opening.label
      if second.value then
        let decoded := PublicSourceByteInputs.digest context.message
        match decoded.value with
        | none => ⟨none,first.cost+second.cost+decoded.cost+8⟩
        | some value =>
          let claim := StoredSingleOpeningCost.decode opening.message
          ⟨claim.value.map (fun data => (value,data.root)),first.cost+second.cost+decoded.cost+claim.cost+9⟩
      else ⟨none,first.cost+second.cost+6⟩
    else ⟨none,first.cost+4⟩
  else ⟨none,3⟩

theorem single_value (context opening : Frame) :
    (single context opening).value.map sourceView = NativeRootInputView.single context opening := by
  change _ = if context.kind = 1 ∧ context.label = contextLabel ∧ opening.kind = 1 ∧ opening.label = openingLabel then
    (do let ctx ← NativeExactCodec.read NativeByteCodec.digest context.message
        let claim ← NativeExactCodec.read NativeGoldPcsWire.openingCodec opening.message
        pure (ctx,claim.1)) else none
  simp only [Option.bind_eq_bind,← StoredChildSeedQuote.digest_as_native,← StoredSingleOpeningCost.decode_value]
  by_cases firstKind : context.kind = 1 <;> by_cases secondKind : opening.kind = 1 <;>
    by_cases firstName : context.label = contextLabel <;> by_cases secondName : opening.label = openingLabel
  all_goals
    simp only [single,BytePrefixMatchCost.equal_value,
      Eq.comm (a := contextLabel) (b := context.label),Eq.comm (a := openingLabel) (b := opening.label),
      firstKind,secondKind,firstName,secondName,and_true,and_false,ite_true,ite_false,
      decide_true,decide_false,Bool.false_eq_true,Option.map_none]
  cases decoded : (PublicSourceByteInputs.digest context.message).value with
  | none => simp only [Option.map_none,Option.bind_none]
  | some value =>
    simp only [Option.map_some,Option.bind_some]
    cases claim : (StoredSingleOpeningCost.decode opening.message).value <;> rfl

theorem single_cost (context opening : Frame) :
    (single context opening).cost ≤ 419*opening.message.length+6*(contextLabel.length+openingLabel.length)+1900 := by
  have first := BytePrefixMatchCost.equal_cost contextLabel context.label
  have firstSize := Nat.min_le_left contextLabel.length context.label.length
  have second := BytePrefixMatchCost.equal_cost openingLabel opening.label
  have secondSize := Nat.min_le_left openingLabel.length opening.label.length
  have decoded := PublicSourceByteInputs.digest_cost context.message
  have claim := StoredSingleOpeningCost.decode_cost opening.message
  simp only [single]
  split
  · split
    · split
      · split <;> dsimp only <;> omega
      · dsimp only; omega
    · dsimp only; omega
  · dsimp only; omega

def mentions : List Frame → List NativeCanonicalLookupWire.Source
  | [] => []
  | head::tail =>
    (match tail with | [] => [] | next::_ => (NativeRootInputView.single head next).toList) ++ mentions tail

def collect : List Frame → Run (List Source)
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := collect tail
    match tail with
    | [] => ⟨rest.value,rest.cost+3⟩
    | next::_ =>
      let first := single head next
      ⟨match first.value with | none => rest.value | some source => source::rest.value,
        first.cost+rest.cost+3⟩

theorem collect_value (frames : List Frame) : (collect frames).value.map sourceView = mentions frames := by
  induction frames with
  | nil => rfl
  | cons head tail ih =>
    rw [collect.eq_def,mentions.eq_def]
    cases tail with
    | nil => rfl
    | cons next rest =>
      have reference := single_value head next
      cases parsed : (single head next).value with
      | none =>
        rw [parsed,Option.map_none] at reference
        simp only [parsed,ih,← reference,Option.toList_none,List.nil_append]
      | some source =>
        rw [parsed,Option.map_some] at reference
        simp only [parsed,List.map_cons,ih,← reference,Option.toList_some,List.singleton_append]

def messageBytes : List Frame → ℕ
  | [] => 0
  | head::tail => head.message.length+messageBytes tail

def afterMessages : List Frame → ℕ
  | [] => 0
  | _::tail => messageBytes tail

theorem collect_cost (frames : List Frame) :
    (collect frames).cost ≤ 419*afterMessages frames+
      (6*(contextLabel.length+openingLabel.length)+1903)*frames.length+1 := by
  induction frames with
  | nil => simp [collect,afterMessages]
  | cons head tail ih =>
    rw [collect.eq_def]
    cases tail with
    | nil => simp only [collect,afterMessages,messageBytes,List.length_cons,List.length_nil]; omega
    | cons next rest =>
      have first := single_cost head next
      simp only [afterMessages,messageBytes,List.length_cons] at *
      nlinarith

theorem messageBytes_le_encoded (frames : List Frame) :
    messageBytes frames ≤ (TranscriptFrame.encodeMany frames).length := by
  induction frames with
  | nil => rfl
  | cons head tail ih => simp only [messageBytes,TranscriptFrame.encodeMany,List.length_append,TranscriptFrame.encode_length]; omega

theorem afterMessages_le_encoded (frames : List Frame) :
    afterMessages frames ≤ (TranscriptFrame.encodeMany frames).length := by
  cases frames with
  | nil => rfl
  | cons head tail =>
    have remaining := messageBytes_le_encoded tail
    simp only [afterMessages,TranscriptFrame.encodeMany,List.length_append,TranscriptFrame.encode_length]
    omega

def fromInput (input : Input) : Run (List Source) :=
  let frames := TranscriptFrameStreamCost.decodeAll input
  match frames.value with
  | none => ⟨[],frames.cost+2⟩
  | some values =>
    let sources := collect values
    ⟨sources.value,frames.cost+sources.cost+3⟩

theorem fromInput_value (input : Input) :
    (fromInput input).value.map sourceView = mentions ((TranscriptFrame.decodeAll input).getD []) := by
  simp only [fromInput,TranscriptFrameStreamCost.decodeAll_value]
  cases parsed : TranscriptFrame.decodeAll input with
  | none => rfl
  | some frames => simp only [Option.getD_some,collect_value]

theorem fromInput_cost (input : Input) :
    (fromInput input).cost ≤ (2346+6*(contextLabel.length+openingLabel.length))*input.length+5 := by
  have decoded := TranscriptFrameStreamCost.decodeAll_cost input
  simp only [fromInput]
  split
  · dsimp only; nlinarith
  · rename_i frames parsed
    have encoded := (TranscriptFrameStreamCost.decodeAll_sound input frames parsed).2
    have count := ParentSeedRequestCost.frameCount_le_encoded frames
    have messages := afterMessages_le_encoded frames
    rw [← encoded] at count messages
    have sources := collect_cost frames
    have visits := Nat.mul_le_mul_left (6*(contextLabel.length+openingLabel.length)+1903) count
    dsimp only
    nlinarith
end FormalProof4FHE.HasteBoots.StoredSingleSourcesCost
