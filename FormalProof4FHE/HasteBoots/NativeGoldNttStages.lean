module

public import FormalProof4FHE.HasteBoots.NativeGoldNtt

@[expose] public section

/-! Exact scalar butterfly reads and separation of contiguous sub-buffers.
All equalities retain canonical stored words, not just field projections. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldNttStages

open NativeGoldSolinas (Word)
open NativeGoldNtt (stage breadth depthFirst)

def entry (remaining start : ℕ) (twid data : List Word) (index : ℕ) : Word :=
  let t := 2^remaining
  let group := index/(2*t)
  let first := group*(2*t)+index%t
  let weighted := NativeGoldSolinas.mul (data[first+t]?.getD 0) (twid[start+group]?.getD 0)
  if index/t%2 = 0 then NativeGoldSolinas.add (data[first]?.getD 0) weighted
  else NativeGoldSolinas.sub (data[first]?.getD 0) weighted

theorem stage_get (log remaining start : ℕ) (twid data : List Word) (index : Fin (2^log)) :
    (stage log remaining start twid data)[index.val]'(by rw [NativeGoldNtt.stage_length]; exact index.isLt) =
      entry remaining start twid data index.val := by
  simp only [stage,List.getElem_map,List.getElem_range]
  rfl

theorem stride_factor (log remaining : ℕ) (before : remaining < log) :
    2^log = (2*2^remaining)*2^(log-(remaining+1)) := by
  conv_lhs => rw [← Nat.sub_add_cancel (by omega : remaining+1 ≤ log),pow_add,pow_succ]
  ac_rfl

theorem entry_append_left (log remaining start : ℕ) (twid left right : List Word)
    (before : remaining < log) (leftSize : left.length = 2^log) (index : Fin (2^log)) :
    entry remaining start twid (left++right) index.val = entry remaining start twid left index.val := by
  have bounds := NativeGoldNtt.pair_addresses log remaining before index
  dsimp only at bounds
  dsimp only [entry]
  simp only [List.getElem?_append_left (by rw [leftSize]; exact bounds.2),
    List.getElem?_append_left (by rw [leftSize]; exact bounds.1)]

theorem entry_append_right (log remaining start : ℕ) (twid left right : List Word)
    (before : remaining < log) (leftSize : left.length = 2^log) (index : ℕ) :
    entry remaining start twid (left++right) (2^log+index) =
      entry remaining (start+2^(log-(remaining+1))) twid right index := by
  let t := 2^remaining
  let m := 2^(log-(remaining+1))
  have width : 2^log = (2*t)*m := stride_factor log remaining before
  have width' : 2^log = t*(2*m) := by rw [width]; ac_rfl
  have positive : 0 < t := by dsimp [t]; positivity
  have quotient : (2^log+index)/(2*t) = m+index/(2*t) := by
    rw [width,Nat.mul_add_div (by positivity : 0 < 2*t)]
  have remainder : (2^log+index)%t = index%t := by rw [width',Nat.mul_add_mod]
  have parity : (2^log+index)/t%2 = index/t%2 := by
    rw [width',Nat.mul_add_div positive,Nat.mul_add_mod]
  have address : (m+index/(2*t))*(2*t)+index%t =
      2^log+(index/(2*t)*(2*t)+index%t) := by rw [width]; ring
  have read_right (offset : ℕ) : (left++right)[2^log+offset]? = right[offset]? := by
    rw [List.getElem?_append_right (by rw [leftSize]; omega),leftSize,Nat.add_sub_cancel_left]
  dsimp only [t,m] at quotient remainder parity address
  dsimp only [entry]
  simp only [quotient,remainder,parity,address,Nat.add_assoc,read_right]

/-- A stage below the top split is exactly two independent child stages. -/
theorem stage_append (log remaining start : ℕ) (twid left right : List Word)
    (before : remaining < log) (leftSize : left.length = 2^log) (rightSize : right.length = 2^log) :
    stage (log+1) remaining start twid (left++right) =
      stage log remaining start twid left ++ stage log remaining (start+2^(log-(remaining+1))) twid right := by
  apply List.ext_getElem (by simp only [NativeGoldNtt.stage_length,List.length_append,pow_succ]; omega)
  intro index present other
  have bound : index < 2^log+2^log := by
    simpa only [List.length_append,NativeGoldNtt.stage_length] using other
  by_cases first : index < 2^log
  · rw [stage_get _ _ _ _ _ ⟨index,by rw [pow_succ]; omega⟩,
      List.getElem_append_left (by rw [NativeGoldNtt.stage_length]; exact first),stage_get _ _ _ _ _ ⟨index,first⟩]
    exact entry_append_left log remaining start twid left right before leftSize ⟨index,first⟩
  · have last : index-2^log < 2^log := by omega
    have address : index = 2^log+(index-2^log) := by omega
    rw [stage_get _ _ _ _ _ ⟨index,by rw [pow_succ]; omega⟩,
      List.getElem_append_right (by rw [NativeGoldNtt.stage_length]; omega)]
    simp only [NativeGoldNtt.stage_length]
    rw [stage_get _ _ _ _ _ ⟨index-2^log,last⟩]
    dsimp only
    conv_lhs => arg 5; rw [address]
    exact entry_append_right log remaining start twid left right before leftSize (index-2^log)

end FormalProof4FHE.HasteBoots.NativeGoldNttStages
