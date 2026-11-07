module
import all FormalProof4FHE.HasteBoots.NativeParentLedger
import all FormalProof4FHE.HasteBoots.StoredShakeByteCache
import all FormalProof4FHE.HasteBoots.StoredParentSeedCheck
import all FormalProof4FHE.HasteBoots.StoredShakeHistory
import all FormalProof4FHE.HasteBoots.FixedByteReadCost
import all FormalProof4FHE.HasteBoots.CostedMerkleNode
import all FormalProof4FHE.HasteBoots.BytePrefixMatchCost
import all FormalProof4FHE.HasteBoots.IntegerEncodingCost
import all FormalProof4FHE.HasteBoots.RowEncodingCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeaf
import all FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
import all FormalProof4FHE.HasteBoots.PreparedMerklePayloads
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeFieldWire
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.PreparedMerkleNodes
import all FormalProof4FHE.HasteBoots.StoredDigestView
import all FormalProof4FHE.HasteBoots.CostedMerkleTree
import all VCVio.CryptoFoundations.MerkleTree.Extractor
import all ToMathlib.Data.IndexedBinaryTree.Perfect
import all ToMathlib.Data.IndexedBinaryTree.Basic
import all FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
import all FormalProof4FHE.HasteBoots.CostedMerkleWord
import all FormalProof4FHE.HasteBoots.NativeGoldRawAvailability

open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Byte)
private def seed : Vector Byte 64 := Vector.ofFn (fun i => if i.val = 63 then 9 else 0)
private def history : List NativeTranscript.Observation :=
  [.start [1],.hash [1] (List.replicate 64 0),.output [1] 63 [7],.output [1] 63 [9],.output [2] 0 [6]]

-- Repeated/overlapping writes shadow old coordinates but preserve every entry.
/-- info: true -/
#guard_msgs in
#eval let cache := StoredShakeHistory.replay history
  decide (cache.value.length = 3 ∧ cache.cost = 46 ∧
    (StoredShakeByteCache.lookup cache.value [1] 63).value = some 9 ∧
    (StoredShakeByteCache.lookup cache.value [2] 0).value = some 6 ∧
    (StoredShakeByteCache.lookup cache.value [1] 0).value = none)

-- Prefix observations remain partial: unknown bytes must remain wildcards.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredShakeHistory.parentCompatible [] [1] seed).value ∧
  (StoredShakeHistory.parentCompatible history [1] seed).value ∧
  !(StoredShakeHistory.parentCompatible history [1] (Vector.replicate 64 0)).value)

-- Inputs have distinct coordinate spaces. Off-seed offsets do not constrain a quote.
/-- info: true -/
#guard_msgs in
#eval decide ((StoredShakeHistory.parentCompatible [.output [2] 0 [7]] [1] seed).value ∧
  (StoredShakeHistory.parentCompatible [.output [1] 64 [7]] [1] seed).value ∧
  !(StoredShakeHistory.parentCompatible [.output [1] 0 [7]] [1] seed).value)

-- Empty output, start and hash records are visited, while leaving known bytes intact.
/-- info: true -/
#guard_msgs in
#eval let first := StoredShakeHistory.replay history
  let later := StoredShakeHistory.replay (history ++ [.output [1] 0 [],.start [1],.hash [1] (List.replicate 64 8)])
  decide (later.value = first.value ∧ later.cost = first.cost+11)

-- Install a whole interval at a nonzero offset. Partial cache boundaries stay exact.
/-- info: true -/
#guard_msgs in
#eval let result := StoredShakeByteCache.write [] [3,4] 5 [7,8,9]
  decide (result.value.length = 3 ∧ result.cost = 25 ∧
    (StoredShakeByteCache.lookup result.value [3,4] 4).value = none ∧
    (StoredShakeByteCache.lookup result.value [3,4] 5).value = some 7 ∧
    (StoredShakeByteCache.lookup result.value [3,4] 7).value = some 9 ∧
    (StoredShakeByteCache.lookup result.value [3,4] 8).value = none)

-- A contradiction in the first exposed coordinate short-circuits later seed scans.
/-- info: true -/
#guard_msgs in
#eval let cache := (StoredShakeByteCache.write [] [1] 0 [7]).value
  let bad := StoredParentSeedCheck.compatible cache [1] seed
  let good := StoredParentSeedCheck.compatible cache [2] seed
  decide (!bad.value ∧ good.value ∧ bad.cost < good.cost ∧
    bad.cost ≤ 64*((6*1+14)*cache.length+5)+131)

-- Full history check composes replay and seed scans once, including rejected work.
/-- info: true -/
#guard_msgs in
#eval let cache := StoredShakeHistory.replay history
  let checked := StoredParentSeedCheck.compatible cache.value [1] seed
  let result := StoredShakeHistory.parentCompatible history [1] seed
  decide (result.value = checked.value ∧ result.cost = cache.cost+checked.cost+1 ∧
    result.cost ≤ 8*3+5*history.length+64*((6*1+14)*3+5)+133)

/-- info: [28, 45, 3250] -/
#guard_msgs in
#eval let cache := (StoredShakeHistory.replay history).value
  [(StoredShakeByteCache.lookup cache [1] 63).cost,(StoredShakeByteCache.lookup cache [1] 0).cost,
   (StoredParentSeedCheck.compatible cache [1] seed).cost]

-- Visit and retain every compatible parent, including an unknown parent and
-- a duplicate. A conflicting parent is removed without reordering the others.
/-- info: true -/
#guard_msgs in
#eval let cache := (StoredShakeHistory.replay history).value
  let candidates : List NativeParentLedger.Parent :=
    [⟨[1],[],[]⟩,⟨[2],[],[]⟩,⟨[3],[],[]⟩,⟨[1],[],[]⟩]
  let result := StoredParentSeedCheck.parents cache seed candidates
  decide (result.value.map (fun parent => parent.input) = [[1],[3],[1]] ∧
    result.cost ≤ 64*(6*StoredParentSeedCheck.parentInputBytes candidates+14*candidates.length)*cache.length+
      454*candidates.length+1)
