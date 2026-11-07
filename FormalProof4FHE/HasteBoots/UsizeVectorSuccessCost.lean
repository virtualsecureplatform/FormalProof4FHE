module
public import FormalProof4FHE.HasteBoots.UsizeVectorCost
@[expose] public section

/-! Successful row-reader costs in terms of consumed bytes. These bounds permit
amortized nesting without charging every remaining suffix repeatedly. Existing
codec definitions and pure bounded-length witnesses are unchanged. -/
namespace FormalProof4FHE.HasteBoots.UsizeVectorSuccessCost
open InputIndexedOracle (Input)
open NativeUsizeMessage (Usize)

theorem readCount_cost (count : ℕ) (bytes : Input) (values : List Usize) (rest : Input)
    (found : (UsizeVectorCost.readCount count bytes).value = some (values,rest)) :
    (UsizeVectorCost.readCount count bytes).cost ≤ 106*count+1 := by
  induction count generalizing bytes values rest with
  | zero => simp [UsizeVectorCost.readCount]
  | succ count ih =>
    have first := IntegerPrefixCost.readUsize_cost bytes
    cases parsed : (IntegerPrefixCost.readUsize bytes).value with
    | none => simp only [UsizeVectorCost.readCount,parsed] at found; contradiction
    | some pair =>
      rcases pair with ⟨value,tail⟩
      simp only [UsizeVectorCost.readCount,parsed] at found ⊢
      obtain ⟨⟨remaining,last⟩,continued,same⟩ := Option.map_eq_some_iff.mp found
      have bound := ih tail remaining last continued
      omega

theorem read_cost (bytes : Input) (values : NativePrefixCodec.Vector Usize) (rest : Input)
    (found : (UsizeVectorCost.read bytes).value = some (values,rest)) :
    (UsizeVectorCost.read bytes).cost ≤ 107*(bytes.length-rest.length)+1 := by
  have first := IntegerPrefixCost.readUsize_cost bytes
  simp only [UsizeVectorCost.read] at found ⊢
  split at found
  · contradiction
  · rename_i count tail parsed
    split at found
    · contradiction
    · rename_i entries last decoded
      have body := readCount_cost count.val tail entries last decoded
      have consumed := UsizeVectorCost.readCount_success count.val tail entries last decoded
      have length := UsizeVectorCost.readCount_length count.val tail entries last decoded
      have header := IntegerPrefixCost.readUsize_remaining bytes count tail parsed
      have same := Option.some.inj found
      cases same
      dsimp only
      omega
end FormalProof4FHE.HasteBoots.UsizeVectorSuccessCost
