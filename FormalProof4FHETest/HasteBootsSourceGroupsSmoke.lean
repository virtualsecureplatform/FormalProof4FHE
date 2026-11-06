module
import all FormalProof4FHE.HasteBoots.NativeSourceRegistry
import all FormalProof4FHE.HasteBoots.NativeGoldBatchBinding
import all FormalProof4FHETest.HasteBootsPcsClaimSmoke
import all FormalProof4FHETest.HasteBootsRegistryAncestrySmoke
open FormalProof4FHE.HasteBoots
open OracleProgram (run)
open HasteBootsRegistryAncestrySmoke (usize digest root description registry expected world parent helper requests)
namespace HasteBootsSourceGroupsSmoke
noncomputable section

def initialized := (run (NativeSourceRegistry.startRegistry description registry parent) world).run
example : initialized.1.isSome = true ∧ initialized.2.length = 3 := by decide +kernel
example : initialized.1.map (fun state => NativeSourceRegistry.groupCount state.sources) = some 2 := by decide +kernel
example : initialized.1.map (fun state => (List.finRange state.sources.val.length).map (fun index => (NativeSourceRegistry.owner state.sources index).val)) =
    some [0,0,2] := by decide +kernel
-- The only requested slot is 1, yet its native source owner is the earlier unused slot 0.
example : requests.val.flatMap (fun request => request.sourceSlots.val.map Fin.val) = [1] ∧
    (NativeSourceRegistry.owner expected ⟨1,by decide⟩).val = 0 := by decide +kernel
example : (NativeSourceRegistry.group expected ⟨0,by decide⟩).val ≠ (NativeSourceRegistry.group expected ⟨2,by decide⟩).val := by decide +kernel

def mixed : NativePrefixCodec.Vector NativeCanonicalLookupWire.Source :=
  ⟨[(digest 0,digest 7),(digest 0,digest 8),(digest 1,digest 7),(digest 0,digest 7)],by decide⟩
example : (List.finRange mixed.val.length).map (fun index => (NativeSourceRegistry.owner mixed index).val) = [0,1,2,0] := by decide +kernel
example : ∀ index : Fin mixed.val.length, NativeSourceRegistry.owner mixed (NativeSourceRegistry.owner mixed index) = NativeSourceRegistry.owner mixed index :=
  NativeSourceRegistry.owner_idempotent mixed
example : ((run (NativeSourceRegistry.startRegistry description ⟨[],by decide⟩ parent) world).run.1.isNone,
    (run (NativeSourceRegistry.startRegistry description ⟨[],by decide⟩ parent) world).run.2.length) = (true,0) := by decide +kernel

def failing : NativeBrakedownContext.RowDescription (Fin 2) :=
  {description with serialize := fun code => if code.val = 0 then some [0] else none}
def failure := (run (NativeSourceRegistry.startRegistry failing registry parent) world).run
example : failure.1.isNone = true ∧ failure.2.length = 2 := by decide +kernel
-- Context collisions really do merge native aliases; no parameter-equality conclusion is inferred.
def collisionWorld : InputIndexedOracle.World := fun _ => 0
def collision := (run (NativeSourceRegistry.startRegistry description registry parent) collisionWorld).run
example : collision.1.map (fun state => NativeSourceRegistry.groupCount state.sources) = some 1 := by decide +kernel
example : collision.1.map (fun state => (List.finRange state.sources.val.length).map (fun index => (NativeSourceRegistry.owner state.sources index).val)) =
    some [0,0,0] := by decide +kernel
example : ((run (NativeSourceRegistry.startRegistry description registry parent) world).run.1.map NativeSourceRegistry.Initialized.parent,
    (run (NativeSourceRegistry.startRegistry description registry parent) world).run.2) =
    (run (NativeSharedLookupParent.register description registry parent) world).run := NativeSourceRegistry.initialize_erasure _ _ _ _

def matrix (value : ℕ) : NativeGoldPcsWire.Matrix := ⟨usize 1,⟨[usize value],by change 1 < 2^64; decide⟩⟩
def pair (atZero atOne : ℕ) : NativeGoldPcsWire.Pair := (matrix atZero,matrix atOne)
def query (first second : NativeGoldPcsWire.Pair) : NativeGoldPcsWire.Query := ⟨[first,second],by change 2 < 2^64; decide⟩
def queries : NativePrefixCodec.Vector NativeGoldPcsWire.Query :=
  ⟨[query (pair 0 1) (pair 1 0),query (pair 0 1) (pair 2 3),query (pair 1 0) (pair 0 1),
    query (pair NativeFields.goldilocksModulus 1) (pair 1 0)],by decide⟩
def groupSummary (left : ℕ) := (List.finRange queries.val.length).map (fun index => (NativeGoldQueryGroups.group left queries index).val)
def representativeSummary (left : ℕ) := (List.finRange (NativeGoldQueryGroups.groupCount left queries)).map
  (fun index => (NativeGoldQueryGroups.representative left queries index).val)
example : groupSummary 1 = [0,0,1,0] := by decide +kernel
example : groupSummary 2 = [0,1,2,0] := by decide +kernel
example : representativeSummary 2 = [0,1,2] := by decide +kernel
example : NativeGoldQueryGroups.key 2 (query (pair 0 1) (pair 1 0)) ≠
    NativeGoldQueryGroups.key 2 (query (pair 1 0) (pair 0 1)) := by decide +kernel
-- Lazy field-equivalent entries share a response, but keep different transcript bytes.
example : NativeGoldQueryGroups.key 2 (query (pair 0 1) (pair 1 0)) =
    NativeGoldQueryGroups.key 2 (query (pair NativeFields.goldilocksModulus 1) (pair 1 0)) := by decide +kernel
example : NativeGoldPcsWire.queryCodec.encode (query (pair 0 1) (pair 1 0)) ≠
    NativeGoldPcsWire.queryCodec.encode (query (pair NativeFields.goldilocksModulus 1) (pair 1 0)) := by decide +kernel

-- Captured from successful native open_many/verify_many at dff353006322693cab3dc6b654f82151f658f294.
-- Native batch has four claims and two ordered-prefix response groups, including one lazy field alias.
def bytes (values : List ℕ) : InputIndexedOracle.Input := values.map (fun value => ⟨value % 256,Nat.mod_lt _ (by decide)⟩)
def nativeRootBytes : InputIndexedOracle.Input :=
  bytes [236,255,121,148,40,92,99,241,64,131,187,250,61,215,77,252,205,24,186,73,136,206,154,126,126,206,87,101,210,171,159,114,65,145,231,96,151,110,42,225,28,79,6,117,197,155,189,109,217,11,238,118,214,241,171,107,34,128,73,40,11,4,235,250]
def nativeQueries : InputIndexedOracle.Input :=
  bytes [4,2,1,1,0,1,1,1,1,1,1,1,1,0,2,1,1,0,1,1,1,1,1,2,1,1,3,2,1,1,1,1,1,0,1,1,0,1,1,1,2,1,1,253,1,0,0,0,255,255,255,255,1,1,1,1,1,1,1,1,0]
def nativeValues : InputIndexedOracle.Input :=
  bytes [4,1,1,1,11,1,2,1,1]
def nativeContextInput : InputIndexedOracle.Input :=
  bytes [72,97,115,116,101,66,111,111,116,115,47,109,119,45,112,97,114,97,109,101,116,101,114,115,47,118,50,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,2,1,1,1,2,32,26,98,108,111,99,107,45,114,115,47,110,101,103,97,99,121,99,108,105,99,45,110,116,116,47,118,49,2,2,1,32,20,49,56,52,52,54,55,52,52,48,54,57,52,49,52,53,56,52,51,50,49,253,0,0,0,0,128] ++
  bytes [0,0,0]
def nativeContextDigest : InputIndexedOracle.Input :=
  bytes [215,128,227,180,182,92,110,247,243,98,252,99,110,173,56,166,213,97,87,21,39,25,189,12,37,154,74,86,139,106,153,34,56,167,152,87,55,65,245,153,16,101,7,158,173,37,22,201,109,38,36,240,113,210,96,96,210,7,228,46,159,176,73,75]
def nativePrefix : InputIndexedOracle.Input :=
  bytes [0,8,0,0,0,0,0,0,0,112,114,111,116,111,99,111,108,29,0,0,0,0,0,0,0,72,97,115,116,101,66,111,111,116,115,32,102,114,97,109,101,100,32,83,72,65,75,69,50,53,54,32,118,49,0,11,0,0,0,0,0,0,0,97,112,112,108,105,99,97,116,105,111,110,35,0,0,0,0,0,0,0,72,97,115,116,101,66,111,111,116,115,32,116,121,112,101,100,32,99,108,97,115,115,105,99,97,108,32,112,114,105] ++
  bytes [109,101,32,118,49,0,15,0,0,0,0,0,0,0,116,114,117,115,116,101,100,32,112,114,111,102,105,108,101,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,17,0,0,0,0,0,0,0,116,121] ++
  bytes [112,101,100,32,112,114,105,109,101,32,102,105,101,108,100,16,0,0,0,0,0,0,0,1,0,0,0,255,255,255,255,0,0,0,0,0,0,0,0,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,23,0,0,0,0,0,0,0,97,116,111,109,105,99,32,78,84,84,32,114,111,119,32,112,104,97,115,101,32,118,50,1,28,0,0,0] ++
  bytes [0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,27,0,0,0,0,0,0,0,97,116,111,109,105,99,32,106,111,105,110,116,32,112,114,111,106,101,99,116,105,111,110,115,32,118,51,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,26,0,0,0,0,0,0,0] ++
  bytes [97,116,111,109,105,99,32,112,97,99,107,101,100,32,122,101,114,111,99,104,101,99,107,32,118,52,1,28,0,0,0,0,0,0,0,99,108,97,115,115,105,99,97,108,32,99,104,97,108,108,101,110,103,101,32,115,99,104,101,100,117,108,101,27,0,0,0,0,0,0,0,97,116,111,109,105,99,32,66,114,97,107,101,100,111,119,110,32,99,111,108,117,109,110,115,32,118,53,1,22,0,0,0,0,0,0,0,109,119,32,98,97] ++
  bytes [116,99,104,101,100,32,114,111,119,45,99,111,100,101,32,118,49,198,0,0,0,0,0,0,0,215,128,227,180,182,92,110,247,243,98,252,99,110,173,56,166,213,97,87,21,39,25,189,12,37,154,74,86,139,106,153,34,56,167,152,87,55,65,245,153,16,101,7,158,173,37,22,201,109,38,36,240,113,210,96,96,210,7,228,46,159,176,73,75,236,255,121,148,40,92,99,241,64,131,187,250,61,215,77,252,205,24,186,73,136,206,154] ++
  bytes [126,126,206,87,101,210,171,159,114,65,145,231,96,151,110,42,225,28,79,6,117,197,155,189,109,217,11,238,118,214,241,171,107,34,128,73,40,11,4,235,250,4,2,1,1,0,1,1,1,1,1,1,1,1,0,2,1,1,0,1,1,1,1,1,2,1,1,3,2,1,1,1,1,1,0,1,1,0,1,1,1,2,1,1,253,1,0,0,0,255,255,255,255,1,1,1,1,1,1,1,1,0,4,1,1,1,11,1,2,1,1]

def nativeRoot : NativeRootMessage.Digest := fun index => nativeRootBytes[index.val]?.getD 0
def nativeDigest : NativeRootMessage.Digest := fun index => nativeContextDigest[index.val]?.getD 0
def batchParameters := {NativePcsClaimSmoke.retainedParameters with width := usize 1}
def rowValue (value : ℕ) : NativeLookupRequestWire.Row := ⟨[usize value],by change 1 < 2^64; decide⟩
def values : NativePrefixCodec.Vector NativeLookupRequestWire.Row := ⟨[rowValue 1,rowValue 11,rowValue 2,rowValue 1],by decide⟩
def batchWorld : InputIndexedOracle.World
  | .inl _ => 255
  | .inr (input,index) => if input = nativeContextInput then nativeDigest index else 255
def batch := (run (NativeGoldBatchBinding.protocol NativeGoldBlockCode.description.row batchParameters NativePcsClaimSmoke.parent
  nativeRoot queries values) batchWorld).run
example : NativeBrakedownContext.input NativeGoldBlockCode.description.row batchParameters = some nativeContextInput := by decide +kernel
example : NativeGoldBatchBinding.queriesCodec.encode queries = nativeQueries := by decide +kernel
example : NativeGoldBatchBinding.valuesCodec.encode values = nativeValues := by decide +kernel
example : batch.1.map (fun bound => bound.parent.input) = some nativePrefix := by decide +kernel
example : batch.2 = [.hash nativeContextInput nativeContextDigest] := by decide +kernel
example : batch.1.map (fun bound => NativeGoldQueryGroups.groupCount batchParameters.leftVariables.val bound.queries) = some 2 := by decide +kernel
example : (NativeGoldBatchBinding.check batchParameters ⟨[],by decide⟩ ⟨[],by decide⟩) = false := by decide +kernel
example : (run (NativeGoldBatchBinding.protocol NativeGoldBlockCode.description.row batchParameters NativePcsClaimSmoke.parent
    nativeRoot queries ⟨[],by decide⟩) batchWorld).run.2 = [] := by decide +kernel
-- An invalid matrix width is rejected before its parameter context is hashed.
def invalidQueries : NativePrefixCodec.Vector NativeGoldPcsWire.Query :=
  ⟨[query (⟨usize 2,⟨[usize 0],by decide⟩⟩,matrix 1) (pair 1 0)],by decide⟩
example : (run (NativeGoldBatchBinding.protocol NativeGoldBlockCode.description.row batchParameters NativePcsClaimSmoke.parent
    nativeRoot invalidQueries ⟨[rowValue 1],by decide⟩) batchWorld).run.1.isNone = true ∧
    (run (NativeGoldBatchBinding.protocol NativeGoldBlockCode.description.row batchParameters NativePcsClaimSmoke.parent
    nativeRoot invalidQueries ⟨[rowValue 1],by decide⟩) batchWorld).run.2 = [] := by decide +kernel

end
end HasteBootsSourceGroupsSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_key

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.representative_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.representative_first

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_first

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_le

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_idempotent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.owner_idempotent

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.group_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.group_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialize_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialize_erasure

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialized_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialized_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialized_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialized_sources

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialized_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.initialized_owner

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.registered_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.registered_metadata

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.prepared_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.prepared_metadata

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.bound_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.bound_metadata

/-- info: 'FormalProof4FHE.HasteBoots.NativeSourceRegistry.helpers_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSourceRegistry.helpers_metadata

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.canonical_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.canonical_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.matrixKey_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.matrixKey_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.pairKey_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.pairKey_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.key_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.key_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.group_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.group_eq_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.representative_key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.representative_key

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.representative_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.representative_first

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.group_key' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldQueryGroups.group_key

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.check_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.check_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.rejected

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.serialization_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.serialization_failure

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.accepted

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.appendBound_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.appendBound_input

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.bound_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.bound_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.bound_groups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldBatchBinding.bound_groups
