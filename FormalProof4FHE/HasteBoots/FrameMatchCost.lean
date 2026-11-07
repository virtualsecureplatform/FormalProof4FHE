module
public import FormalProof4FHE.HasteBoots.BytePrefixMatchCost
public import FormalProof4FHE.HasteBoots.IntegerEncodingCost
public import FormalProof4FHE.HasteBoots.RowEncodingCost
public import FormalProof4FHE.HasteBoots.NativeIndexInputView
@[expose] public section

/-! Charged exact frame equality and fixed-width u64 structural decoding.
Comparisons inspect supplied byte lists; the bounded integer witness follows
from the successful fixed-width parse, independently of cost theorems. -/
namespace FormalProof4FHE.HasteBoots.FrameMatchCost
open InputIndexedOracle (Input)
open TranscriptFrame (Frame)
open SolverOperationCost (Run)

def equal (actual expected : Frame) : Run Bool :=
  if actual.kind = expected.kind then
    let label := BytePrefixMatchCost.equal actual.label expected.label
    if label.value then
      let message := BytePrefixMatchCost.equal actual.message expected.message
      ⟨message.value,label.cost+message.cost+5⟩
    else ⟨false,label.cost+3⟩
  else ⟨false,2⟩

theorem equal_value (actual expected : Frame) : (equal actual expected).value = decide (actual = expected) := by
  cases actual with
  | mk kind label message =>
    cases expected with
    | mk expectedKind expectedLabel expectedMessage =>
      by_cases kinds : kind = expectedKind <;> by_cases labels : label = expectedLabel <;>
        simp [equal,BytePrefixMatchCost.equal_value,kinds,labels,TranscriptFrame.Frame.mk.injEq]

theorem equal_cost (actual expected : Frame) :
    (equal actual expected).cost ≤ 6*(expected.label.length+expected.message.length)+24 := by
  have label := BytePrefixMatchCost.equal_cost actual.label expected.label
  have labelSize := Nat.min_le_right actual.label.length expected.label.length
  have message := BytePrefixMatchCost.equal_cost actual.message expected.message
  have messageSize := Nat.min_le_right actual.message.length expected.message.length
  simp only [equal]
  split
  · split <;> dsimp only <;> omega
  · dsimp only; omega

def readU64 (input : Input) : Run (Option NativeUsizeMessage.Usize) :=
  let count := RowEncodingCost.length input
  if sized : count.value = 8 then
    let decoded := BytePrefixCost.fromLittleEndian input
    have bound : decoded.value < 2^64 := by
      rw [BytePrefixCost.fromLittleEndian_value]
      have size : input.length = 8 := (RowEncodingCost.length_value input).symm.trans sized
      have bounded := TranscriptFrame.fromLittleEndian_lt input
      rw [size] at bounded
      exact bounded
    ⟨some ⟨decoded.value,bound⟩,count.cost+decoded.cost+4⟩
  else ⟨none,count.cost+2⟩

theorem readU64_value (input : Input) : (readU64 input).value = NativeIndexInputView.readU64 input := by
  by_cases sized : input.length = 8 <;>
    simp only [readU64,RowEncodingCost.length_value,NativeIndexInputView.readU64,sized,dite_true,dite_false,
      BytePrefixCost.fromLittleEndian_value]

theorem readU64_cost (input : Input) : (readU64 input).cost ≤ 3*input.length+46 := by
  have count := RowEncodingCost.length_cost input
  have decoded := BytePrefixCost.fromLittleEndian_cost input
  simp only [readU64]
  split
  · rename_i sized
    rw [RowEncodingCost.length_value] at sized
    dsimp only
    omega
  · dsimp only; omega
end FormalProof4FHE.HasteBoots.FrameMatchCost
