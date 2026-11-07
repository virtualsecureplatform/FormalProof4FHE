module
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input)
private def usize (n : Nat) : NativeUsizeMessage.Usize := ⟨n % 2^64,Nat.mod_lt _ (by decide)⟩
private def encoded (values : List Nat) : Input :=
  NativeUsizeMessage.encode (usize values.length) ++ values.flatMap (fun value => NativeUsizeMessage.encode (usize value))
private def view (bytes : Input) : Option (List Nat × Input) :=
  (UsizeVectorCost.read bytes).value.map (fun pair => (pair.1.val.map Fin.val,pair.2))

-- All integer-width boundaries through the maximum raw/lazy u64; keep suffix.
/-- info: true -/
#guard_msgs in
#eval let values := [0,250,251,65535,65536,2^32-1,2^32,2^64-1]
      let result := UsizeVectorCost.read (encoded values ++ [42,43])
      decide (view (encoded values ++ [42,43]) = some (values,[42,43]) ∧ result.cost = 471)

/-- info: true -/
#guard_msgs in
#eval let values := [0,251,2^64-1]
      let words := values.flatMap (fun value => NativeUsizeMessage.encode (usize value))
      let result := UsizeVectorCost.readCount 3 (words++[42,43])
      decide (result.value.map (fun pair => (pair.1.map Fin.val,pair.2)) = some (values,[42,43]) ∧ result.cost = 164)

-- A declared maximum count with no words fails after one attempted word.
/-- info: true -/
#guard_msgs in
#eval let result := UsizeVectorCost.read (NativeUsizeMessage.encode (usize (2^64-1)))
      decide (result.value = none ∧ result.cost = 112)

-- The same huge declaration with two supplied words remains bounded by bytes.
/-- info: true -/
#guard_msgs in
#eval let result := UsizeVectorCost.read (NativeUsizeMessage.encode (usize (2^64-1))++[1,2])
      decide (result.value = none ∧ result.cost = 142)

/-- info: true -/
#guard_msgs in
#eval let result := UsizeVectorCost.readCount (2^64-1) []
      decide (result.value = none ∧ result.cost = 6)

-- Empty rows do not traverse the returned suffix to rediscover their length.
/-- info: true -/
#guard_msgs in
#eval let bytes := [0]++List.replicate 10000 42
      let result := UsizeVectorCost.read bytes
      decide (result.cost = 17 ∧ result.value.map (fun pair => (pair.1.val.length,pair.2.length)) = some (0,10000))

-- Structural permissiveness is preserved; strict role canonicality is separate.
/-- info: true -/
#guard_msgs in
#eval decide (view [251,1,0,251,1,0] = some ([1],[])) &&
      decide ((UsizeVectorCost.read [251,1,0,251,1,0]).cost = 86)

-- Invalid tag after a valid word stops without building an accepted partial row.
/-- info: true -/
#guard_msgs in
#eval let result := UsizeVectorCost.read [2,1,254]
      decide (result.value = none ∧ result.cost = 45)

-- The native row codec uses the measured parser and preserves raw u64 spelling.
/-- info: true -/
#guard_msgs in
#eval let row : NativeLookupRequestWire.Row := ⟨[usize 0,usize (2^64-1)],by decide⟩
      decide (NativeLookupRequestWire.rowCodec.read (NativeLookupRequestWire.rowCodec.encode row++[99]) = some (row,[99]))

/-- info: true -/
#guard_msgs in
#eval [[],[254],[253,1],[3,1,2]].all (fun bytes => (UsizeVectorCost.read bytes).value.isNone)
