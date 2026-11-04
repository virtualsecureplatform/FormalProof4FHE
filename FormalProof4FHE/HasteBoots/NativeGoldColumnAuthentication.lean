module

public import FormalProof4FHE.HasteBoots.NativeHashOracleBridge
public import FormalProof4FHE.HasteBoots.NativeLookupRequestWire
public import FormalProof4FHE.HasteBoots.NativeByteCodec
public import FormalProof4FHE.HasteBoots.NativeMerkleVerifier

@[expose] public section

/-!
# Concrete Goldilocks column authentication in the transcript's oracle world

Native paths include the claimed leaf first. Height validation precedes the
leaf hash; the original index determines each sibling order. All hashes
share the same SHA-512 input domain as contexts and other Merkle calls.
Authentication is not code membership or full PCS verification.
-/
namespace FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication

open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row rowCodec)
open NativeTranscript (Observation)
open NativePrefixCodec (Codec product transport vector)
open OracleProgram (Program bind run)
open OracleSpec OracleComp

/-- Decide digest equality through the literal fixed-size byte sequence. -/
def digestDecidableEq : DecidableEq Digest := fun left right =>
  decidable_of_iff (List.ofFn left = List.ofFn right) List.ofFn_inj

local instance : DecidableEq Digest := digestDecidableEq

structure Column where
  values : Row
  path : NativePrefixCodec.Vector Digest
  deriving DecidableEq

def columnEquiv : (Row × NativePrefixCodec.Vector Digest) ≃ Column where
  toFun := fun pair => ⟨pair.1,pair.2⟩
  invFun := fun column => ⟨column.values,column.path⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def columnCodec : Codec Column := transport (product rowCodec (vector NativeByteCodec.digest)) columnEquiv

def leafInput (values : Row) : Input := NativeFieldWire.columnDomain ++ rowCodec.encode values

def nodeInput (left right : Digest) : Input := List.ofFn left ++ List.ofFn right

def encoding : MerkleOracle.Encoding Input Digest Row where
  leaf _ := leafInput
  node _ := fun pair => nodeInput pair.1 pair.2
  leaf_injective _ := by
    intro left right same
    exact rowCodec.encode_injective (List.append_cancel_left same)
  node_injective _ := (product NativeByteCodec.digest NativeByteCodec.digest).encode_injective

theorem column_encode (column : Column) : columnCodec.encode column =
    rowCodec.encode column.values ++ NativeRootMessage.encode column.path.val column.path.property := rfl

theorem column_prefix (column : Column) (suffix : Input) :
    columnCodec.read (columnCodec.encode column ++ suffix) = some (column,suffix) := columnCodec.read_encode _ _

def decodePath (height : ℕ) (path : List Digest) : Option (Digest × List.Vector Digest height) :=
  match path with
  | [] => none
  | leaf :: siblings => if length : siblings.length = height then some (leaf,⟨siblings,length⟩) else none

def nodes (index : ℕ) : ℕ → Digest → List Digest → Program Digest
  | _,leaf,[] => .pure leaf
  | level,leaf,sibling :: tail =>
    let input := if index / 2^level % 2 = 0 then nodeInput leaf sibling else nodeInput sibling leaf
    .hash input (fun next => nodes index (level+1) next tail)

def verifyDecoded (height index : ℕ) (root leaf : Digest) (values : Row) (siblings : List.Vector Digest height) : Program Bool :=
  .hash (leafInput values) (fun observed =>
    if observed = leaf then bind (nodes index 0 leaf siblings.toList) (fun computed => .pure (computed == root)) else .pure false)

def verify (height index : ℕ) (root : Digest) (column : Column) : Program Bool :=
  match decodePath height column.path.val with
  | none => .pure false
  | some (leaf,siblings) => verifyDecoded height index root leaf column.values siblings

theorem decodePath_spec (height : ℕ) (path : List Digest) (leaf : Digest) (siblings : List.Vector Digest height)
    (success : decodePath height path = some (leaf,siblings)) : path = leaf :: siblings.toList := by
  cases path with
  | nil => contradiction
  | cons head tail =>
    simp only [decodePath] at success
    split at success
    next length =>
      have same := Option.some.inj success
      cases same
      rfl
    next rejected => contradiction

theorem invalid_path (height index : ℕ) (root : Digest) (column : Column) (world : World)
    (invalid : decodePath height column.path.val = none) : (run (verify height index root column) world).run = (false,[]) := by
  simp only [verify,invalid,OracleProgram.run,CanonicalTranscriptSampler.run_pure]

theorem nodes_compile (index level : ℕ) (leaf : Digest) (siblings : List Digest) :
    nodes index level leaf siblings = NativeHashOracleBridge.compile
      (NativeMerklePathM.loopFrom (NativeMerkleVerifier.nodeHash encoding) index level leaf siblings) := by
  induction siblings generalizing level leaf with
  | nil => rfl
  | cons sibling tail ih =>
    simp only [nodes,NativeMerklePathM.loopFrom,NativeMerklePathM.branch]
    split <;>
      simp only [NativeMerkleVerifier.nodeHash,encoding,NativeHashOracleBridge.compile_bind,
        NativeHashOracleBridge.compile_hash,OracleProgram.bind,ih]

theorem verifyDecoded_compile (height index : ℕ) (root leaf : Digest) (values : Row) (siblings : List.Vector Digest height) :
    verifyDecoded height index root leaf values siblings = NativeHashOracleBridge.compile
      (NativeMerkleVerifier.verifyPayload encoding height index values leaf root siblings) := by
  simp only [verifyDecoded,NativeMerkleVerifier.verifyPayload,NativeHashOracleBridge.compile_bind,
    NativeHashOracleBridge.compile_hash,OracleProgram.bind,encoding]
  congr 1
  funext observed
  by_cases same : observed = leaf
  · simp only [same,ite_true,NativeMerkleVerifier.verifyNodes,NativeHashOracleBridge.compile_bind,
      NativeHashOracleBridge.compile_pure]
    rw [nodes_compile]
    rfl
  · simp only [same,ite_false,NativeHashOracleBridge.compile_pure]

theorem run_verifyDecoded (height index : ℕ) (root leaf : Digest) (values : Row) (siblings : List.Vector Digest height) (world : World) :
    run (verifyDecoded height index root leaf values siblings) world =
      simulateQ (NativeHashOracleBridge.implementation world) (NativeMerkleVerifier.verifyPayload encoding height index values leaf root siblings) := by
  rw [verifyDecoded_compile,NativeHashOracleBridge.run_compile]

/-- Replay in the cache computed from the actual earlier execution and actual
column hashes; no replay or Merkle-acceptance certificate is supplied. -/
theorem accepted_replay (height index : ℕ) (root leaf : Digest) (values : Row) (siblings : List.Vector Digest height)
    (world : World) (earlier : List Observation) (past : ObservationReplay.Agrees world earlier)
    (accepted : (run (verifyDecoded height index root leaf values siblings) world).run.1 = true) :
    simulateQ (JointHashCache.project (earlier ++ (run (verifyDecoded height index root leaf values siblings) world).run.2)).cache.toPartialImpl
      (NativeMerkleVerifier.verifyPayload encoding height index values leaf root siblings) = some true := by
  rw [run_verifyDecoded] at accepted ⊢
  rw [NativeHashOracleBridge.replay_actual _ world earlier past,accepted]

/-- Acceptance of the received column establishes the parsed path and replays
that same payload/path in the cache projected from the actual combined log. -/
theorem verify_accepted_replay (height index : ℕ) (root : Digest) (column : Column)
    (world : World) (earlier : List Observation) (past : ObservationReplay.Agrees world earlier)
    (accepted : (run (verify height index root column) world).run.1 = true) :
    ∃ leaf siblings, decodePath height column.path.val = some (leaf,siblings) ∧
      column.path.val = leaf :: siblings.toList ∧
      simulateQ (JointHashCache.project (earlier ++ (run (verify height index root column) world).run.2)).cache.toPartialImpl
        (NativeMerkleVerifier.verifyPayload encoding height index column.values leaf root siblings) = some true := by
  cases decoded : decodePath height column.path.val with
  | none =>
    have rejected := invalid_path height index root column world decoded
    rw [rejected] at accepted
    contradiction
  | some pair =>
    obtain ⟨leaf,siblings⟩ := pair
    refine ⟨leaf,siblings,rfl,decodePath_spec _ _ _ _ decoded,?_⟩
    simp only [verify,decoded] at accepted ⊢
    exact accepted_replay height index root leaf column.values siblings world earlier past accepted

end FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
