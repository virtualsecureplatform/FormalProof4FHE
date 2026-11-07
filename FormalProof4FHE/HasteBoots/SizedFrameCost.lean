module
public import FormalProof4FHE.HasteBoots.FixedByteReadCost
@[expose] public section

/-! Charged native u64-length-prefixed frame payloads. Declared lengths never
cause traversal beyond the supplied bytes. These are abstract byte/arithmetic/
list charges; physical u64, framing callers and compiler refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.SizedFrameCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)

theorem header_length (input : Input) (count : ℕ) (tail : Input)
    (found : (BytePrefixCost.readWide 8 input).value = some (count,tail)) :
    input.length = tail.length+8 := by
  rw [BytePrefixCost.readWide_value] at found
  split at found
  · rename_i enough
    have rest : input.drop 8 = tail := congrArg Prod.snd (Option.some.inj found)
    rw [← rest,List.length_drop]
    omega
  · contradiction

def read (input : Input) : Run (Option (Input × Input)) :=
  let header := BytePrefixCost.readWide 8 input
  match header.value with
  | none => ⟨none,header.cost+2⟩
  | some (count,tail) =>
    let result := BytePrefixCost.takeExact count tail
    ⟨result.value,header.cost+result.cost+3⟩

theorem read_value (input : Input) : (read input).value = TranscriptFrame.readSized input := by
  by_cases enough : 8 ≤ input.length <;>
    simp [read,BytePrefixCost.readWide_value,BytePrefixCost.takeExact_value,
      TranscriptFrame.readSized,TranscriptFrame.takeBytes,enough]

theorem read_cost (input : Input) : (read input).cost ≤ 10*input.length+10 := by
  have header := BytePrefixCost.readWide_cost 8 input
  simp only [read]
  split
  · dsimp only
    have bound := Nat.min_le_right 8 input.length
    omega
  · rename_i count tail found
    have lengths := header_length input count tail found
    have bound := Nat.min_le_left 8 input.length
    have body := BytePrefixCost.takeExact_cost count tail
    have size := Nat.min_le_right count tail.length
    dsimp only
    omega

theorem read_success_cost (input first rest : Input)
    (found : (read input).value = some (first,rest)) :
    (read input).cost ≤ 10*(input.length-rest.length)+10 := by
  have header := BytePrefixCost.readWide_cost 8 input
  simp only [read] at found ⊢
  split at found
  · contradiction
  · rename_i count tail parsed
    have lengths := header_length input count tail parsed
    have parts := FixedByteReadCost.takeExact_parts count tail first rest found
    have size := congrArg List.length parts.2
    simp only [List.length_append] at size
    have body := BytePrefixCost.takeExact_cost count tail
    have bound := Nat.min_le_left 8 input.length
    have width := Nat.min_le_left count tail.length
    dsimp only
    omega

theorem read_remaining (input first rest : Input)
    (found : (read input).value = some (first,rest)) : rest.length+8 ≤ input.length := by
  rw [read_value] at found
  have parts := (TranscriptFrame.readSized_sound input first rest found).2
  have lengths := congrArg List.length parts
  simp only [TranscriptFrame.sized,List.length_append,TranscriptFrame.littleEndian_length] at lengths
  omega
end FormalProof4FHE.HasteBoots.SizedFrameCost
