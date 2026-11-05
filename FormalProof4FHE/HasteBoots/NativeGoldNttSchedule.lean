module

public import FormalProof4FHE.HasteBoots.NativeGoldNttStages

@[expose] public section

/-! The actual breadth/depth schedules agree with one recursive butterfly tree.
The tree is a proof intermediary; the operational encoder remains the original
computed breadth/depth implementation, with its native cutoff unchanged. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldNttSchedule

open NativeGoldSolinas (Word)
open NativeGoldNtt (stage breadth depthFirst)

def tree : (log depth half : ℕ) → List Word → List Word → List Word
  | 0,_,_,_,data => data
  | log+1,depth,half,twid,data =>
    let next := stage (log+1) log (2^depth+half) twid data
    tree log (depth+1) (half*2) twid (next.take (2^log)) ++
      tree log (depth+1) (half*2+1) twid (next.drop (2^log))

/-- Remaining breadth-first rounds act independently on the two old halves. -/
theorem breadth_append (log depth half : ℕ) (twid : List Word) (rounds : ℕ) (left right : List Word)
    (roundBound : rounds ≤ log) (leftSize : left.length = 2^log) (rightSize : right.length = 2^log) :
    breadth (log+1) depth half twid rounds (left++right) =
      breadth log (depth+1) (half*2) twid rounds left ++
      breadth log (depth+1) (half*2+1) twid rounds right := by
  induction rounds generalizing left right with
  | zero => rfl
  | succ rounds ih =>
    have before : rounds < log := by omega
    have exponent : (log+1)-(rounds+1) = (log-(rounds+1))+1 := by omega
    have leftOffset : 2^((log+1)-(rounds+1))*2^depth+half*2^((log+1)-(rounds+1)) =
        2^(log-(rounds+1))*2^(depth+1)+(half*2)*2^(log-(rounds+1)) := by
      rw [exponent,pow_succ,pow_succ]
      ring
    have rightOffset : 2^((log+1)-(rounds+1))*2^depth+half*2^((log+1)-(rounds+1))+2^(log-(rounds+1)) =
        2^(log-(rounds+1))*2^(depth+1)+(half*2+1)*2^(log-(rounds+1)) := by
      rw [exponent,pow_succ,pow_succ]
      ring
    simp only [breadth]
    rw [NativeGoldNttStages.stage_append log rounds _ twid left right before leftSize rightSize,
      ih _ _ (by omega) (NativeGoldNtt.stage_length _ _ _ _ _) (NativeGoldNtt.stage_length _ _ _ _ _),rightOffset,leftOffset]

/-- All recursive buffers retain the full local coefficient count. -/
theorem tree_length (log depth half : ℕ) (twid data : List Word) (size : data.length = 2^log) :
    (tree log depth half twid data).length = 2^log := by
  induction log generalizing depth half data with
  | zero => exact size
  | succ log ih =>
    rw [tree,List.length_append,
      ih _ _ _ (by rw [List.length_take,NativeGoldNtt.stage_length,pow_succ]; omega),
      ih _ _ _ (by rw [List.length_drop,NativeGoldNtt.stage_length,pow_succ]; omega),pow_succ]
    omega

/-- The complete breadth-first execution is exactly the same raw tree. -/
theorem breadth_tree (log depth half : ℕ) (twid data : List Word) (size : data.length = 2^log) :
    breadth log depth half twid log data = tree log depth half twid data := by
  induction log generalizing depth half data with
  | zero => rfl
  | succ log ih =>
    let next := stage (log+1) log (2^depth+half) twid data
    have leftSize : (next.take (2^log)).length = 2^log := by
      rw [List.length_take,NativeGoldNtt.stage_length,pow_succ]; omega
    have rightSize : (next.drop (2^log)).length = 2^log := by
      rw [List.length_drop,NativeGoldNtt.stage_length,pow_succ]; omega
    have partition : next = next.take (2^log) ++ next.drop (2^log) := (List.take_append_drop _ _).symm
    rw [breadth]
    simp only [Nat.sub_self,pow_zero,one_mul,mul_one]
    change breadth (log+1) depth half twid log next = _
    calc
      _ = breadth (log+1) depth half twid log (next.take (2^log) ++ next.drop (2^log)) := congrArg _ partition
      _ = breadth log (depth+1) (half*2) twid log (next.take (2^log)) ++
          breadth log (depth+1) (half*2+1) twid log (next.drop (2^log)) :=
        breadth_append log depth half twid log _ _ le_rfl leftSize rightSize
      _ = _ := by rw [ih _ _ _ leftSize,ih _ _ _ rightSize]; rfl

/-- The real 1024-element cutoff changes scheduling, not any stored output. -/
theorem depthFirst_tree (log depth half : ℕ) (twid data : List Word) (size : data.length = 2^log) :
    depthFirst log depth half twid data = tree log depth half twid data := by
  induction log generalizing depth half data with
  | zero => rfl
  | succ log ih =>
    rw [depthFirst]
    split
    · exact breadth_tree _ _ _ _ _ size
    · dsimp only
      rw [tree]
      rw [ih _ _ _ (by rw [List.length_take,NativeGoldNtt.stage_length,pow_succ]; omega),
        ih _ _ _ (by rw [List.length_drop,NativeGoldNtt.stage_length,pow_succ]; omega)]

end FormalProof4FHE.HasteBoots.NativeGoldNttSchedule
