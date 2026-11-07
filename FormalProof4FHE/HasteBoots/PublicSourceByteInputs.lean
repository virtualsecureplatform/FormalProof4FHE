module
public import FormalProof4FHE.HasteBoots.StoredDigestView
@[expose] public section

/-! Strict stored-byte adapters for a supplied public source snapshot. Every
hash-output spelling must contain exactly 64 bytes; malformed entries reject the
whole snapshot. Original order and duplicates are preserved. No functional
digest callback is evaluated. Parsing/framing of the enclosing snapshot,
complete-history source selection and physical refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.PublicSourceByteInputs
open InputIndexedOracle (Input Byte)
open PreparedMerklePayloads (StoredDigest)
open SolverOperationCost (Run)
abbrev ByteLog := List (Input × Input)
abbrev StoredLog := List (Input × StoredDigest)

def digest (input : Input) : Run (Option (Vector Byte 64)) :=
  let result := FixedByteReadCost.read 64 input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some (value,rest) => ⟨if rest = [] then some value else none,result.cost+3⟩

theorem digest_cost (input : Input) : (digest input).cost ≤ 455 := by
  have bound := FixedByteReadCost.read_cost 64 input
  simp only [digest]
  split <;> dsimp only <;> omega

theorem digest_sound (input : Input) (value : Vector Byte 64)
    (found : (digest input).value = some value) : input = value.toList := by
  simp only [digest] at found
  split at found
  · contradiction
  · rename_i parsed rest read
    split at found
    · rename_i ended
      have same := Option.some.inj found
      subst value
      have parts := FixedByteReadCost.read_some 64 input parsed rest read
      simpa only [ended,List.append_nil] using parts
    · contradiction

theorem digest_encode (value : Vector Byte 64) : (digest value.toList).value = some value := by
  have native : (FixedByteReadCost.read 64 value.toList).value.map (fun pair => (pair.1.get,pair.2)) =
      some (value.get,[]) := by
    rw [FixedByteReadCost.read_value]
    simpa only [NativeByteCodec.digest,NativeByteCodec.fixed,NativePrefixCodec.Codec.encode,
      FixedByteReadCost.ofFn_get,List.append_nil] using
      NativeByteCodec.digest_prefix value.get []
  cases result : (FixedByteReadCost.read 64 value.toList).value with
  | none => simp only [result,Option.map_none] at native; contradiction
  | some pair =>
    rcases pair with ⟨parsed,rest⟩
    rw [result,Option.map_some] at native
    have same := Option.some.inj native
    have ended : rest = [] := congrArg Prod.snd same
    have vector : parsed = value := by
      apply Vector.ext
      intro i hi
      exact congrFun (congrArg Prod.fst same) ⟨i,hi⟩
    simp only [digest,result,ended,ite_true,vector]

def storedDigest (input : Input) : Run (Option StoredDigest) :=
  let result := digest input
  match result.value with
  | none => ⟨none,result.cost+2⟩
  | some value =>
    let stored := StoredDigestView.fromVector value
    ⟨some stored.value,result.cost+stored.cost+2⟩

theorem storedDigest_cost (input : Input) : (storedDigest input).cost ≤ 586 := by
  have bound := digest_cost input
  simp only [storedDigest]
  split <;> dsimp only [StoredDigestView.fromVector] <;> omega

theorem storedDigest_sound (input : Input) (value : StoredDigest)
    (found : (storedDigest input).value = some value) : input = value.val := by
  simp only [storedDigest] at found
  split at found
  · contradiction
  · rename_i parsed read
    have same := Option.some.inj found
    subst value
    exact digest_sound input parsed read

theorem storedDigest_encode (value : StoredDigest) : (storedDigest value.val).value = some value := by
  let vector : Vector Byte 64 := ⟨value.val.toArray,by simp [value.property]⟩
  have bytes : vector.toList = value.val := by simp [vector]
  have parsed := digest_encode vector
  rw [bytes] at parsed
  simp only [storedDigest,parsed,StoredDigestView.fromVector,bytes]

def log : ByteLog → Run (Option StoredLog)
  | [] => ⟨some [],1⟩
  | (input,output)::tail =>
    let first := storedDigest output
    match first.value with
    | none => ⟨none,first.cost+2⟩
    | some label =>
      let rest := log tail
      ⟨rest.value.map (fun entries => (input,label)::entries),first.cost+rest.cost+3⟩

theorem log_cost (entries : ByteLog) : (log entries).cost ≤ 589*entries.length+1 := by
  induction entries with
  | nil => simp [log]
  | cons head tail ih =>
    rcases head with ⟨input,output⟩
    have bound := storedDigest_cost output
    simp only [log,List.length_cons]
    split <;> dsimp only <;> omega

def encodeLog (entries : StoredLog) : ByteLog := entries.map (fun entry => (entry.1,entry.2.val))

theorem log_sound (entries : ByteLog) (result : StoredLog)
    (found : (log entries).value = some result) : entries = encodeLog result := by
  induction entries generalizing result with
  | nil =>
    have same : [] = result := Option.some.inj found
    subst result
    rfl
  | cons head tail ih =>
    rcases head with ⟨input,output⟩
    simp only [log] at found
    split at found
    · contradiction
    · rename_i label parsed
      cases rest : (log tail).value with
      | none => simp only [rest,Option.map_none] at found; contradiction
      | some rows =>
        simp only [rest,Option.map_some,Option.some.injEq] at found
        subst result
        simp only [encodeLog,List.map_cons]
        rw [storedDigest_sound output label parsed,ih rows rest]
        rfl

theorem log_encode (entries : StoredLog) : (log (encodeLog entries)).value = some entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨input,output⟩
    change (log ((input,output.val)::encodeLog tail)).value = _
    simp only [log,storedDigest_encode,ih,Option.map_some]

structure Inputs where
  dummy : Vector Byte 64
  root : StoredDigest
  hashes : StoredLog

def read (dummy root : Input) (entries : ByteLog) : Run (Option Inputs) :=
  let first := digest dummy
  match first.value with
  | none => ⟨none,first.cost+3⟩
  | some dummyValue =>
    let second := storedDigest root
    match second.value with
    | none => ⟨none,first.cost+second.cost+5⟩
    | some rootValue =>
      let hashes := log entries
      ⟨hashes.value.map (fun values => ⟨dummyValue,rootValue,values⟩),first.cost+second.cost+hashes.cost+7⟩

theorem read_cost (dummy root : Input) (entries : ByteLog) :
    (read dummy root entries).cost ≤ 589*entries.length+1049 := by
  have first := digest_cost dummy
  have second := storedDigest_cost root
  have hashes := log_cost entries
  simp only [read]
  split
  · dsimp only; omega
  · split <;> dsimp only <;> omega

theorem read_encode (dummy : Vector Byte 64) (root : StoredDigest) (entries : StoredLog) :
    (read dummy.toList root.val (encodeLog entries)).value = some ⟨dummy,root,entries⟩ := by
  simp only [read,digest_encode,storedDigest_encode,log_encode,Option.map_some]

theorem read_sound (dummy root : Input) (entries : ByteLog) (result : Inputs)
    (found : (read dummy root entries).value = some result) :
    dummy = result.dummy.toList ∧ root = result.root.val ∧ entries = encodeLog result.hashes := by
  simp only [read] at found
  split at found
  · contradiction
  · rename_i dummyValue first
    split at found
    · contradiction
    · rename_i rootValue second
      cases hashes : (log entries).value with
      | none => simp only [hashes,Option.map_none] at found; contradiction
      | some values =>
        simp only [hashes,Option.map_some,Option.some.injEq] at found
        subst result
        exact ⟨digest_sound _ _ first,storedDigest_sound _ _ second,log_sound _ _ hashes⟩
end FormalProof4FHE.HasteBoots.PublicSourceByteInputs
