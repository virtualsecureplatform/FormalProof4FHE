module
public import FormalProof4FHE.HasteBoots.FrameMatchCost
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFieldInputView
@[expose] public section

/-! Original fixed-width Gold vector-challenge suffix. Exact frame kind, label,
modulus bytes, canonical u64 count and positivity are checked with measured
operations. This is structural recognition, not trusted application parameters. -/
namespace FormalProof4FHE.HasteBoots.GoldBatchFieldCountCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open NativeUsizeMessage (Usize)
open SolverOperationCost (Run)

def fieldFrame (count : Usize) : Run Frame :=
  let prime := IntegerEncodingCost.littleEndian 16 NativeFields.goldilocksModulus
  let size := IntegerEncodingCost.littleEndian 8 count.val
  let joined := RowEncodingCost.append prime.value size.value
  ⟨⟨4,NativeGoldBatchPrelude.randomLabel,joined.value⟩,prime.cost+size.cost+joined.cost+3⟩

theorem fieldFrame_value (count : Usize) : (fieldFrame count).value = NativeGoldBatchFieldInputView.fieldFrame count := by
  simp only [fieldFrame,RowEncodingCost.append_value,IntegerEncodingCost.littleEndian_value,
    NativeGoldBatchFieldInputView.fieldFrame]

theorem fieldFrame_cost (count : Usize) : (fieldFrame count).cost = 198 := by
  simp only [fieldFrame,IntegerEncodingCost.littleEndian_cost,RowEncodingCost.append_cost,
    IntegerEncodingCost.littleEndian_value,TranscriptFrame.littleEndian_length]

def read (frame : Frame) : Run (Option Usize) :=
  let skipped := BytePrefixCost.takeExact 16 frame.message
  match skipped.value with
  | none => ⟨none,skipped.cost+2⟩
  | some (_,tail) =>
    let count := FrameMatchCost.readU64 tail
    match count.value with
    | none => ⟨none,skipped.cost+count.cost+4⟩
    | some value =>
      let expected := fieldFrame value
      let checked := FrameMatchCost.equal frame expected.value
      ⟨if checked.value && decide (0 < value.val) then some value else none,
        skipped.cost+count.cost+expected.cost+checked.cost+7⟩

theorem read_value (frame : Frame) : (read frame).value = NativeGoldBatchFieldInputView.readCount frame := by
  by_cases enough : 16 ≤ frame.message.length
  · simp only [read,BytePrefixCost.takeExact_value,enough,ite_true,FrameMatchCost.readU64_value,
      FrameMatchCost.equal_value,fieldFrame_value,NativeGoldBatchFieldInputView.readCount,Option.bind_eq_bind]
    cases parsed : NativeIndexInputView.readU64 (frame.message.drop 16) with
    | none => rfl
    | some count =>
      simp only [Option.bind_some]
      by_cases same : frame = NativeGoldBatchFieldInputView.fieldFrame count <;> by_cases positive : 0 < count.val <;>
        simp only [same,positive,decide_true,decide_false,Bool.true_and,Bool.false_and,and_true,and_false,ite_true,ite_false,Bool.false_eq_true]
  · have dropped : frame.message.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
    simp only [read,BytePrefixCost.takeExact_value,enough,ite_false,NativeGoldBatchFieldInputView.readCount,
      dropped,NativeIndexInputView.readU64,List.length_nil,OfNat.zero_ne_ofNat,dite_false,Option.bind_eq_bind,Option.bind_none]

theorem read_cost (frame : Frame) :
    (read frame).cost ≤ 3*frame.message.length+6*NativeGoldBatchPrelude.randomLabel.length+900 := by
  have skipped := BytePrefixCost.takeExact_cost 16 frame.message
  have skipBound := Nat.min_le_left 16 frame.message.length
  simp only [read]
  split
  · dsimp only; omega
  · rename_i first tail parsed
    have remaining : tail.length ≤ frame.message.length := by
      rw [BytePrefixCost.takeExact_value] at parsed
      split at parsed
      · have same := congrArg Prod.snd (Option.some.inj parsed)
        change frame.message.drop 16 = tail at same
        rw [← same,List.length_drop]
        omega
      · contradiction
    have count := FrameMatchCost.readU64_cost tail
    split
    · dsimp only; omega
    · rename_i value found
      have expected := fieldFrame_cost value
      have checked := FrameMatchCost.equal_cost frame (fieldFrame value).value
      simp only [fieldFrame_value,NativeGoldBatchFieldInputView.fieldFrame,List.length_append,
        TranscriptFrame.littleEndian_length] at checked
      dsimp only
      simp only [fieldFrame_value,NativeGoldBatchFieldInputView.fieldFrame]
      omega
end FormalProof4FHE.HasteBoots.GoldBatchFieldCountCost
