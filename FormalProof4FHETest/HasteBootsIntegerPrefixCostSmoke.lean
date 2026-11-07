module
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.SolverOperationCost
open FormalProof4FHE.HasteBoots
private def usize (n : Nat) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide)⟩

-- All bincode width boundaries, including the maximum lazy Goldilocks u64.
/-- info: true -/
#guard_msgs in
#eval [0,250,251,65535,65536,2^32-1,2^32,2^64-1].all (fun value =>
      let encoded := NativeUsizeMessage.encode (usize value) ++ [42,43]
      decide ((IntegerPrefixCost.read encoded).value = some (value,[42,43]) ∧
        (IntegerPrefixCost.readUsize encoded).value = some (usize value,[42,43]) ∧
        NativePrefixCodec.usize.read encoded = some (usize value,[42,43])))

/-- info: [6, 6, 33, 33, 55, 55, 97, 97] -/
#guard_msgs in
#eval [0,250,251,65535,65536,2^32-1,2^32,2^64-1].map (fun value =>
      (IntegerPrefixCost.read (NativeUsizeMessage.encode (usize value))).cost)

/-- info: [10, 37, 59, 101] -/
#guard_msgs in
#eval [0,251,65536,2^32].map (fun value =>
      (IntegerPrefixCost.readUsize (NativeUsizeMessage.encode (usize value))).cost)

-- Empty, invalid tags and each truncated wide encoding fail closed structurally.
/-- info: true -/
#guard_msgs in
#eval [[],[254],[255],[251],[251,1],[252,1,2,3],[253,1,2,3,4,5,6,7]].all
      (fun bytes => (IntegerPrefixCost.read bytes).value.isNone)

-- Wider noncanonical integers retain the old structural result. Strict role
-- canonicality is a separate guard; this parser must not silently change it.
/-- info: true -/
#guard_msgs in
#eval decide ((IntegerPrefixCost.read [251,1,0,99]).value = some (1,[99]))

-- An enormous forged width inspects only the three supplied bytes.
/-- info: true -/
#guard_msgs in
#eval let result := BytePrefixCost.takeExact (2^64-1) [1,2,3]
      decide (result.value = none ∧ result.cost = 16)

/-- info: true -/
#guard_msgs in
#eval let result := BytePrefixCost.takeExact 2 [1,2,3,4]
      decide (result.value = some ([1,2],[3,4]) ∧ result.cost = 11)

/-- info: true -/
#guard_msgs in
#eval let result := BytePrefixCost.readWide 2 [1,2,3,4]
      decide (result.value = some (513,[3,4]) ∧ result.cost = 25)

/-- info: true -/
#guard_msgs in
#eval let result := BytePrefixCost.readWide (2^64-1) [1,2,3]
      decide (result.value = none ∧ result.cost = 18)
