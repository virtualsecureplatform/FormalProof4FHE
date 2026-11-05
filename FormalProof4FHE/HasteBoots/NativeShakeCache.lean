module

public import FormalProof4FHE.HasteBoots.NativeCheckpointProgram
public import FormalProof4FHE.HasteBoots.CachedOracleResponse

@[expose] public section

/-! Persistent SHAKE coordinates for the lazy native interpreter. Reader identity
is absent from keys. This module does not yet establish the joint execution law. -/
namespace FormalProof4FHE.HasteBoots.NativeShakeCache

open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open OracleSpec OracleComp

abbrev Key := Input × ℕ
abbrev Cache := Key → Option Byte

def empty : Cache := fun _ => none

noncomputable section

/-- Cache ownership belongs to the interpreter, not the adversary callback. -/
def byte {Cfg : Type} (key : Key) : StateT Cache
    (OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest)) Byte :=
  StateT.mk fun cache => match cache key with
  | some value => pure (value,cache)
  | none => (fun value => (value,Function.update cache key (some value))) <$>
      liftM ((CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inl 255))

/-- Increasing offsets preserve overlap across blocks and cloned readers. -/
def read {Cfg : Type} (input : Input) (offset : ℕ) : ℕ → StateT Cache
    (OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest)) Input
  | 0 => pure []
  | count+1 => do
    let first ← byte (input,offset)
    let rest ← read input (offset+1) count
    pure (first::rest)

theorem byte_cached {Cfg : Type} (cache : Cache) (key : Key) (value : Byte)
    (known : cache key = some value) :
    (byte (Cfg := Cfg) key).run cache = pure (value,cache) := by
  change (match cache key with | some found => pure (found,cache) | none => _) = _
  rw [known]

theorem read_zero {Cfg : Type} (input : Input) (offset : ℕ) (cache : Cache) :
    (read (Cfg := Cfg) input offset 0).run cache = pure ([],cache) := rfl

/-- A fresh coordinate consumes exactly one private uniform byte. -/
theorem byte_fresh {Cfg : Type} (cache : Cache) (key : Key)
    (unknown : cache key = none) :
    (byte (Cfg := Cfg) key).run cache =
      (fun value => (value, Function.update cache key (some value))) <$>
        liftM ((CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inl 255)) := by
  change (match cache key with | some found => pure (found,cache) | none => _) = _
  rw [unknown]

/-- Installing a fresh answer cannot overwrite any previously exposed byte. -/
theorem update_preserves (cache : Cache) (key other : Key) (value saved : Byte)
    (unknown : cache key = none) (known : cache other = some saved) :
    Function.update cache key (some value) other = some saved := by
  have different : other ≠ key := by
    intro same
    subst other
    rw [unknown] at known
    cases known
  simpa only [Function.update_of_ne different] using known

/-- A completely exposed interval is deterministic and leaves the cache intact. -/
theorem read_cached {Cfg : Type} (input : Input) (offset count : ℕ) (cache : Cache)
    (values : ℕ → Byte)
    (known : ∀ index, index < count → cache (input,offset+index) = some (values index)) :
    (read (Cfg := Cfg) input offset count).run cache =
      pure ((List.range count).map values,cache) := by
  induction count generalizing offset values with
  | zero => rfl
  | succ count ih =>
    have first := byte_cached (Cfg := Cfg) cache (input,offset) (values 0)
      (by simpa using known 0 (Nat.zero_lt_succ count))
    have rest := ih (offset+1) (fun index => values (index+1)) (by
      intro index bounded
      simpa only [Nat.add_assoc, Nat.add_comm 1 index] using
        known (index+1) (Nat.succ_lt_succ bounded))
    simp only [read, StateT.run_bind, first, pure_bind, rest]
    simp [List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- Splitting a read retains the same byte order and the same persistent cache. -/
theorem read_split {Cfg : Type} (input : Input) (offset left right : ℕ) :
    read (Cfg := Cfg) input offset (left+right) = (do
      let front ← read input offset left
      let back ← read input (offset+left) right
      pure (front++back)) := by
  induction left generalizing offset with
  | zero => simp [read]
  | succ left ih =>
    simp only [Nat.succ_add, read, ih, bind_assoc]
    simp [Nat.add_assoc]

/-- Every syntactically possible byte reply installs that reply and preserves
all earlier answers. This requires no freshness premise on the caller. -/
theorem byte_supported {Cfg : Type} (cache : Cache) (key : Key) (result : Byte × Cache)
    (possible : result ∈ support ((byte (Cfg := Cfg) key).run cache)) :
    result.2 key = some result.1 ∧
      ∀ other saved, cache other = some saved → result.2 other = some saved := by
  cases known : cache key with
  | some saved =>
    rw [byte_cached cache key saved known] at possible
    have same := eq_of_mem_support_pure _ possible
    subst result
    exact ⟨known,fun _ _ h => h⟩
  | none =>
    rw [byte_fresh cache key known, support_map, Set.mem_image] at possible
    obtain ⟨value,_,rfl⟩ := possible
    exact ⟨Function.update_self _ _ _, fun other saved h =>
      update_preserves cache key other value saved known h⟩

/-- No native read can erase bytes exposed by a previous read. -/
theorem read_preserves {Cfg : Type} (input : Input) (offset count : ℕ)
    (cache : Cache) (result : Input × Cache)
    (possible : result ∈ support ((read (Cfg := Cfg) input offset count).run cache)) :
    ∀ key saved, cache key = some saved → result.2 key = some saved := by
  induction count generalizing offset cache result with
  | zero =>
    rw [read_zero] at possible
    have same := eq_of_mem_support_pure _ possible
    subst result
    exact fun _ _ h => h
  | succ count ih =>
    rw [read,StateT.run_bind,mem_support_bind_iff] at possible
    obtain ⟨first,queried,tail⟩ := possible
    rw [StateT.run_bind,mem_support_bind_iff] at tail
    obtain ⟨rest,readRest,returned⟩ := tail
    have same := eq_of_mem_support_pure _ returned
    subst result
    intro key saved known
    exact ih (offset+1) first.2 rest readRest key saved
      ((byte_supported cache (input,offset) first queried).2 key saved known)

/-- The returned interval is exactly the interval installed in the final cache.
Together with preservation this makes cloned and overlapping readers coherent. -/
theorem read_records {Cfg : Type} (input : Input) (offset count : ℕ)
    (cache : Cache) (result : Input × Cache)
    (possible : result ∈ support ((read (Cfg := Cfg) input offset count).run cache)) :
    result.1.length = count ∧
      ∀ index, index < count → result.2 (input,offset+index) = result.1[index]? := by
  induction count generalizing offset cache result with
  | zero =>
    rw [read_zero] at possible
    have same := eq_of_mem_support_pure _ possible
    subst result
    exact ⟨rfl,fun _ h => by omega⟩
  | succ count ih =>
    rw [read,StateT.run_bind,mem_support_bind_iff] at possible
    obtain ⟨first,queried,tail⟩ := possible
    rw [StateT.run_bind,mem_support_bind_iff] at tail
    obtain ⟨rest,readRest,returned⟩ := tail
    have same := eq_of_mem_support_pure _ returned
    subst result
    obtain ⟨size,records⟩ := ih (offset+1) first.2 rest readRest
    constructor
    · simpa only [List.length_cons] using congrArg Nat.succ size
    · intro index bounded
      cases index with
      | zero =>
        simpa only [Nat.add_zero,List.getElem?_cons_zero] using
          read_preserves input (offset+1) count first.2 rest readRest (input,offset) first.1
            (byte_supported cache (input,offset) first queried).1
      | succ index =>
        simpa only [List.getElem?_cons_succ,Nat.add_assoc,Nat.add_comm 1 index] using
          records index (Nat.lt_of_succ_lt_succ bounded)

/-- Rereading any supported interval uses no new randomness and returns the
identical bytes, regardless of which reader issued the original request. -/
theorem read_again {Cfg : Type} (input : Input) (offset count : ℕ)
    (cache : Cache) (result : Input × Cache)
    (possible : result ∈ support ((read (Cfg := Cfg) input offset count).run cache)) :
    (read (Cfg := Cfg) input offset count).run result.2 = pure result := by
  obtain ⟨size,records⟩ := read_records input offset count cache result possible
  let values : ℕ → Byte := fun index => result.1[index]?.getD 0
  have known : ∀ index, index < count →
      result.2 (input,offset+index) = some (values index) := by
    intro index bounded
    rw [records index bounded]
    have inRange : index < result.1.length := by omega
    simp only [values,List.getElem?_eq_getElem inRange,Option.getD_some]
  rw [read_cached input offset count result.2 values known]
  have same : (List.range count).map values = result.1 := by
    apply List.ext_getElem
    · simpa using size.symm
    · intro index leftBound rightBound
      simp only [List.length_map,List.length_range] at leftBound
      simp [values,List.getElem?_eq_getElem rightBound]
  rw [same]

end
end FormalProof4FHE.HasteBoots.NativeShakeCache
