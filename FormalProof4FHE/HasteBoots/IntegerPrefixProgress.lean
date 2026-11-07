module
public import FormalProof4FHE.HasteBoots.IntegerPrefixCost
@[expose] public section

/-! Successful integer-prefix parsing consumes at least one and at most nine
bytes. These bounds support future row-parser termination/cost arguments on
supplied bytes, without a cap on the attacker-declared element count. -/
namespace FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input)

namespace BytePrefixCost
theorem readWide_remaining (count : ℕ) (bytes : Input) (value : ℕ) (rest : Input)
    (found : (readWide count bytes).value = some (value,rest)) :
    rest.length ≤ bytes.length ∧ bytes.length ≤ rest.length+count := by
  rw [readWide_value] at found
  split at found
  · have pair := Option.some.inj found
    have remaining := congrArg Prod.snd pair
    change bytes.drop count = rest at remaining
    rw [← remaining,List.length_drop]
    omega
  · contradiction
end BytePrefixCost

namespace IntegerPrefixCost
theorem read_remaining (bytes : Input) (value : ℕ) (rest : Input)
    (found : (read bytes).value = some (value,rest)) :
    rest.length < bytes.length ∧ bytes.length ≤ rest.length+9 := by
  cases bytes with
  | nil => simp only [read] at found; contradiction
  | cons tag tail =>
    simp only [read] at found
    split at found
    · have pair := Option.some.inj found
      have remaining := congrArg Prod.snd pair
      change tail = rest at remaining
      rw [← remaining,List.length_cons]
      omega
    · split at found
      · have remaining := BytePrefixCost.readWide_remaining 2 tail value rest found
        simp only [List.length_cons]
        omega
      · split at found
        · have remaining := BytePrefixCost.readWide_remaining 4 tail value rest found
          simp only [List.length_cons]
          omega
        · split at found
          · have remaining := BytePrefixCost.readWide_remaining 8 tail value rest found
            simp only [List.length_cons]
            omega
          · contradiction

theorem readUsize_remaining (bytes : Input) (value : NativeUsizeMessage.Usize) (rest : Input)
    (found : (readUsize bytes).value = some (value,rest)) :
    rest.length < bytes.length ∧ bytes.length ≤ rest.length+9 := by
  rw [readUsize_value] at found
  obtain ⟨⟨number,tail⟩,parsed,converted⟩ := Option.bind_eq_some_iff.mp found
  split at converted
  · have pair := Option.some.inj converted
    have remaining := congrArg Prod.snd pair
    change tail = rest at remaining
    have progress := read_remaining bytes number tail (by rw [read_value]; exact parsed)
    simpa only [remaining] using progress
  · contradiction
end IntegerPrefixCost
end FormalProof4FHE.HasteBoots
